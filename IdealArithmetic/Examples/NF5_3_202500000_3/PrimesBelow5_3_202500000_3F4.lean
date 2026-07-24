
import IdealArithmetic.Examples.NF5_3_202500000_3.RI5_3_202500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0, 0, 0]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![0, 0, 0, 157, 0], ![0, 0, 0, 0, 157]] where
  M :=![![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![0, 0, 0, 157, 0], ![0, 0, 0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 5 2 7 [146, 113, 83, 118, 143, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 34, 73, 88, 124], [148, 154, 131, 20, 68], [150, 19, 25, 116, 13], [30, 106, 85, 90, 109], [0, 1]]
 g := ![![[0, 67, 96, 133, 14], [148, 111, 76, 127], [148, 8, 78, 15, 145], [37, 76, 33, 2, 86], [144, 142, 78, 14, 1], [], []], ![[42, 46, 91, 19, 118, 43, 89, 76], [20, 96, 96, 124], [122, 148, 30, 32, 73, 43, 116, 13], [101, 131, 16, 34, 138, 91, 57, 30], [72, 5, 7, 72, 71, 81, 16, 154], [6, 127, 138, 64], [143, 119, 18, 147]], ![[28, 9, 100, 34, 96, 132, 137, 148], [35, 88, 37, 51], [89, 123, 119, 17, 112, 61, 143, 30], [88, 112, 40, 111, 48, 23, 87, 17], [95, 117, 122, 9, 4, 11, 81, 37], [50, 95, 100, 13], [108, 133, 103, 71]], ![[154, 100, 142, 119, 37, 95, 19, 3], [51, 24, 134, 122], [62, 122, 136, 43, 134, 155, 29, 47], [98, 132, 56, 113, 137, 49, 27, 13], [141, 79, 140, 127, 155, 28, 47, 40], [145, 5, 91, 144], [31, 118, 44, 12]], ![[9, 68, 149, 103, 120, 106, 38, 3], [122, 6, 51, 17], [111, 133, 156, 105, 29, 121, 72, 10], [73, 107, 59, 75, 123, 132, 148, 40], [132, 49, 61, 40, 129, 53, 102, 122], [62, 104, 7, 4], [106, 131, 66, 106]]]
 h' := ![![[0, 34, 73, 88, 124], [125, 5, 131, 144, 93], [58, 20, 126, 109, 21], [93, 148, 96, 129, 50], [14, 48, 21, 85, 137], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[148, 154, 131, 20, 68], [80, 80, 39, 23, 119], [86, 117, 0, 14, 76], [12, 15, 99, 104, 54], [7, 107, 18, 92, 16], [75, 10, 40, 126, 10], [3, 65, 59, 90, 8], [0, 34, 73, 88, 124]], ![[150, 19, 25, 116, 13], [52, 139, 27, 73, 120], [74, 19, 120, 47, 88], [78, 84, 147, 95, 102], [149, 154, 93, 30, 78], [91, 133, 36, 15, 60], [13, 146, 68, 9, 135], [148, 154, 131, 20, 68]], ![[30, 106, 85, 90, 109], [73, 42, 55, 53, 146], [104, 44, 55, 146, 43], [24, 81, 45, 44, 149], [4, 20, 67, 56, 1], [149, 107, 103, 63, 84], [76, 41, 131, 31, 12], [150, 19, 25, 116, 13]], ![[0, 1], [83, 48, 62, 21, 150], [132, 114, 13, 155, 86], [133, 143, 84, 99, 116], [40, 142, 115, 51, 82], [51, 64, 135, 110, 2], [25, 62, 55, 27, 2], [30, 106, 85, 90, 109]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 102, 86, 114], [], [], []]
 b := ![[], [110, 111, 143, 149, 32], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 5
  hpos := by decide
  P := [146, 113, 83, 118, 143, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![208918459347590, 65509501458618, 188508295441474, -165437518411930, -418226129947728]
  a := ![153, 6, 189, -140, -391]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1330690823870, 417257971074, 1200689779882, -1053742155490, -2663860700304]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 95388992557 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def PBC157 : ContainsPrimesAboveP 157 ![I157N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![157, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 157 (by decide) 𝕀

instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2231, 1629, 1887, -1266, -3440]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![2231, 1629, 1887, -1266, -3440]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![3, 48, 52, 132, 1]] where
  M :=![![![2231, 1629, 1887, -1266, -3440], ![4296, 3210, 3559, -2338, -6392], ![7464, 6139, 6148, -3778, -10552], ![2544, 3703, 1879, -371, -1760], ![3648, 2459, 3085, -2162, -5793]]]
  hmulB := by decide  
  f := ![![![5, 1, 17, -10, -32]], ![![-24, 10, -61, 34, 104]], ![![24, -49, 144, -74, -200]], ![![144, 53, 71, -57, -256]], ![![117, 30, 86, -60, -241]]]
  g := ![![![77, 1023, 1109, 2778, -3440], ![144, 1902, 2061, 5162, -6392], ![240, 3145, 3404, 8522, -10552], ![48, 541, 573, 1423, -1760], ![129, 1721, 1867, 4678, -5793]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 4 2 7 [79, 135, 126, 132, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [161, 12, 46, 99], [7, 42, 16, 131], [26, 108, 101, 96], [0, 1]]
 g := ![![[97, 94, 25, 40], [74, 90, 43, 9], [29, 62, 81], [116, 51, 4], [72, 68, 74], [31, 1], []], ![[99, 11, 111, 102, 1, 130], [3, 153, 120, 125, 67, 105], [41, 71, 87], [40, 42, 135], [3, 133, 43], [40, 100, 138, 56, 102, 149], [54, 142, 21]], ![[24, 103, 13, 148, 34, 126], [77, 35, 59, 90], [112, 57, 39], [124, 119, 93], [120, 51, 62], [153, 8, 45, 16, 84, 64], [159, 76, 46]], ![[142, 150, 74, 14, 144, 55], [62, 131, 43, 16, 65, 126], [107, 47, 51], [128, 106, 83], [38, 105, 69], [9, 94, 80, 159, 85, 158], [105, 115, 88]]]
 h' := ![![[161, 12, 46, 99], [22, 112, 48, 23], [74, 110, 148, 160], [75, 91, 36, 9], [33, 112, 104, 2], [159, 137, 34, 20], [0, 0, 1], [0, 1]], ![[7, 42, 16, 131], [145, 99, 56, 124], [61, 100, 157, 150], [140, 117, 143, 139], [23, 146, 54, 102], [89, 20, 89, 83], [139, 26, 37, 74], [161, 12, 46, 99]], ![[26, 108, 101, 96], [37, 4, 143, 84], [157, 1, 98], [140, 112, 13, 56], [51, 80, 66, 147], [27, 35, 30, 15], [39, 14, 8, 145], [7, 42, 16, 131]], ![[0, 1], [66, 111, 79, 95], [85, 115, 86, 16], [15, 6, 134, 122], [99, 151, 102, 75], [2, 134, 10, 45], [42, 123, 117, 107], [26, 108, 101, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [77, 47, 102], []]
 b := ![[], [], [16, 103, 108, 156], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 4
  hpos := by decide
  P := [79, 135, 126, 132, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6006096161195, 171035626544, -8536441795679, 5356542127561, 16824220951336]
  a := ![-183, -72, -226, 103, 468]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-346495454081, -4953322515568, -5419606940277, -13591660266557, 16824220951336]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 705911761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -1, -17, 10, 32]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-5, -1, -17, 10, 32]] 
 ![![163, 0, 0, 0, 0], ![113, 1, 0, 0, 0], ![108, 0, 1, 0, 0], ![117, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![-5, -1, -17, 10, 32], ![24, -10, 61, -34, -104], ![-24, 49, -144, 74, 200], ![-144, -53, -71, 57, 256], ![48, 41, -35, 10, -13]]]
  hmulB := by decide  
  f := ![![![-2231, -1629, -1887, 1266, 3440]], ![![-1573, -1149, -1330, 892, 2424]], ![![-1524, -1117, -1288, 862, 2344]], ![![-1617, -1192, -1366, 911, 2480]], ![![-214, -155, -181, 122, 331]]]
  g := ![![![2, -1, -17, 10, 32], ![0, -10, 61, -34, -104], ![-9, 49, -144, 74, 200], ![20, -53, -71, 57, 256], ![-11, 41, -35, 10, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![2231, 1629, 1887, -1266, -3440]] ![![-5, -1, -17, 10, 32]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, -499, -752, 479, 1356]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-35, -499, -752, 479, 1356]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![74, 98, 1, 0, 0], ![48, 162, 0, 1, 0], ![103, 139, 0, 0, 1]] where
  M :=![![![-35, -499, -752, 479, 1356], ![-972, -389, -358, 264, 676], ![-1392, -1182, -1453, 972, 2656], ![-1074, -872, -1034, 687, 1878], ![-366, -496, -672, 442, 1225]]]
  hmulB := by decide  
  f := ![![![305, -103, 620, -349, -1090]], ![![-516, 533, -1838, 972, 2772]], ![![-178, 258, -797, 414, 1148]], ![![-354, 488, -1530, 797, 2218]], ![![-269, 376, -1174, 611, 1699]]]
  g := ![![![-641, -1155, -752, 479, 1356], ![-340, -611, -358, 264, 676], ![-1282, -2308, -1453, 972, 2656], ![-904, -1628, -1034, 687, 1878], ![-587, -1057, -672, 442, 1225]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [60, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 166], [0, 1]]
 g := ![![[79, 81], [121, 4], [20, 2], [127], [2], [44, 88], [1]], ![[72, 86], [32, 163], [59, 165], [127], [2], [90, 79], [1]]]
 h' := ![![[103, 166], [88, 158], [136, 2], [147, 13], [69, 36], [32, 13], [107, 103], [0, 1]], ![[0, 1], [163, 9], [8, 165], [150, 154], [103, 131], [35, 154], [28, 64], [103, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [18, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [60, 64, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14358, -5837, -10975, 10531, 26119]
  a := ![38, -1, 47, -37, -97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14359, -25550, -10975, 10531, 26119]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 15, 30, -21, -58]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-5, 15, 30, -21, -58]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![166, 138, 1, 0, 0], ![69, 164, 0, 1, 0], ![84, 101, 0, 0, 1]] where
  M :=![![![-5, 15, 30, -21, -58], ![60, 9, 32, -32, -76], ![240, 80, 233, -200, -512], ![498, 176, 428, -391, -970], ![-30, -8, 2, 8, 9]]]
  hmulB := by decide  
  f := ![![![311, 223, 266, -181, -488]], ![![660, 451, 560, -380, -1036]], ![![862, 600, 733, -498, -1352]], ![![783, 539, 666, -452, -1230]], ![![558, 387, 474, -322, -875]]]
  g := ![![![8, 31, 30, -21, -58], ![20, 51, 32, -32, -76], ![110, 314, 233, -200, -512], ![227, 618, 428, -391, -970], ![-10, -15, 2, 8, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P1 : CertificateIrreducibleZModOfList' 167 2 2 7 [6, 107, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 166], [0, 1]]
 g := ![![[157, 28], [104, 33], [96, 141], [122], [9], [17, 93], [1]], ![[0, 139], [80, 134], [39, 26], [122], [9], [86, 74], [1]]]
 h' := ![![[60, 166], [44, 144], [92, 37], [119, 108], [163, 150], [65, 164], [161, 60], [0, 1]], ![[0, 1], [0, 23], [141, 130], [86, 59], [145, 17], [52, 3], [87, 107], [60, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [150]]
 b := ![[], [88, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N1 : CertifiedPrimeIdeal' SI167N1 167 where
  n := 2
  hpos := by decide
  P := [6, 107, 1]
  hirr := P167P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-736522, -249967, -610247, 566518, 1412554]
  a := ![-259, 5, -320, 250, 662]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-342394, -907861, -610247, 566518, 1412554]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N1 B_one_repr
lemma NI167N1 : Nat.card (O ⧸ I167N1) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, -147, -278, 171, 498]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![197, -147, -278, 171, 498]] 
 ![![167, 0, 0, 0, 0], ![98, 1, 0, 0, 0], ![82, 0, 1, 0, 0], ![108, 0, 0, 1, 0], ![147, 0, 0, 0, 1]] where
  M :=![![![197, -147, -278, 171, 498], ![-180, 75, 126, -64, -204], ![-144, -130, -309, 244, 640], ![-462, -188, -498, 427, 1086], ![138, -62, -106, 56, 175]]]
  hmulB := by decide  
  f := ![![![409, 377, 290, -209, -488]], ![![250, 225, 182, -130, -308]], ![![206, 200, 131, -98, -224]], ![![270, 242, 210, -147, -342]], ![![363, 341, 244, -179, -417]]]
  g := ![![![-325, -147, -278, 171, 498], ![114, 75, 126, -64, -204], ![-494, -130, -309, 244, 640], ![-880, -188, -498, 427, 1086], ![-101, -62, -106, 56, 175]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-35, -499, -752, 479, 1356]] ![![-5, 15, 30, -21, -58]]
  ![![-12383, 8280, 15490, -9338, -27448]] where
 M := ![![![-12383, 8280, 15490, -9338, -27448]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![-12383, 8280, 15490, -9338, -27448]] ![![197, -147, -278, 171, 498]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![-5634079, 3884921, 7259156, -4392267, -12886722]]]
 hmul := by decide  
 g := ![![![![-33737, 23263, 43468, -26301, -77166]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0, 0, 0]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![0, 0, 0, 0, 173]] where
  M :=![![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![0, 0, 0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 5 2 7 [16, 165, 136, 150, 64, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [83, 115, 48, 63, 47], [152, 26, 118, 139, 154], [78, 48, 72, 131, 36], [142, 156, 108, 13, 109], [0, 1]]
 g := ![![[157, 132, 36, 65, 38], [51, 68, 3, 160], [9, 61, 101, 130, 60], [66, 48, 24, 53, 22], [120, 82, 121, 117], [1], []], ![[98, 60, 100, 92, 87, 97, 31, 35], [36, 140, 43, 67], [123, 26, 118, 83, 41, 96, 142, 6], [98, 119, 90, 166, 69, 27, 150, 47], [21, 136, 159, 85], [102, 23, 155, 151, 31, 113, 126, 157], [139, 148, 5, 133]], ![[22, 59, 133, 12, 38, 61, 10, 19], [169, 87, 33, 25], [133, 49, 65, 11, 166, 135, 111, 170], [28, 117, 132, 53, 63, 167, 44, 97], [98, 147, 94, 119], [16, 12, 27, 121, 136, 75, 146, 20], [56, 162, 159, 15]], ![[148, 71, 18, 89, 68, 56, 94, 64], [90, 51, 148, 116], [142, 171, 27, 22, 172, 118, 53, 135], [111, 70, 56, 102, 71, 86, 33, 118], [75, 138, 44, 140], [137, 75, 24, 47, 107, 171, 107, 142], [21, 113, 13, 85]], ![[38, 76, 141, 166, 7, 148, 154, 85], [151, 57, 59, 116], [3, 104, 14, 115, 11, 126, 2, 137], [169, 130, 26, 107, 61, 67, 13, 67], [1, 166, 160, 35], [58, 46, 51, 170, 131, 125, 146, 52], [110, 58, 17, 117]]]
 h' := ![![[83, 115, 48, 63, 47], [25, 107, 43, 171, 111], [29, 112, 155, 154, 81], [155, 137, 36, 98, 135], [66, 84, 137, 75, 117], [157, 8, 37, 23, 109], [0, 0, 1], [0, 1]], ![[152, 26, 118, 139, 154], [115, 147, 172, 140, 97], [93, 55, 84, 25, 97], [78, 40, 101, 123, 113], [102, 57, 36, 9, 1], [145, 28, 97, 64, 137], [167, 15, 106, 57, 112], [83, 115, 48, 63, 47]], ![[78, 48, 72, 131, 36], [160, 143, 154, 40, 93], [142, 11, 170, 27, 168], [93, 18, 24, 141, 65], [73, 118, 33, 7, 2], [55, 138, 85, 23, 130], [64, 51, 4, 135, 69], [152, 26, 118, 139, 154]], ![[142, 156, 108, 13, 109], [150, 84, 46, 24, 59], [44, 120, 128, 9, 17], [133, 144, 55, 144, 77], [127, 152, 148, 132, 121], [17, 123, 158, 23, 113], [39, 139, 131, 135, 15], [78, 48, 72, 131, 36]], ![[0, 1], [145, 38, 104, 144, 159], [73, 48, 155, 131, 156], [102, 7, 130, 13, 129], [7, 108, 165, 123, 105], [14, 49, 142, 40, 30], [66, 141, 104, 19, 150], [142, 156, 108, 13, 109]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79, 64, 4, 84], [], [], []]
 b := ![[], [89, 144, 79, 65, 116], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 5
  hpos := by decide
  P := [16, 165, 136, 150, 64, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6573063552061528, 2302644864818092, 5352895486329344, -4894822941122220, -12517053842121292]
  a := ![385, 23, 476, -339, -984]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![37994587006136, 13310085923804, 30941592406528, -28293774226140, -72352912382204]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 154963892093 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def PBC173 : ContainsPrimesAboveP 173 ![I173N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![173, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 173 (by decide) 𝕀

instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28097, 19818, 23460, -15974, -43190]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![28097, 19818, 23460, -15974, -43190]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![18, 34, 87, 1, 0], ![6, 32, 130, 0, 1]] where
  M :=![![![28097, 19818, 23460, -15974, -43190], ![56784, 40315, 47608, -32348, -87528], ![114192, 81560, 95527, -64640, -175120], ![84408, 61782, 70416, -46939, -127756], ![40428, 28350, 33860, -23154, -62525]]]
  hmulB := by decide  
  f := ![![![-677, 174, -1260, 718, 2286]], ![![1584, -1087, 4440, -2404, -7096]], ![![1392, 3736, -6443, 2912, 5904]], ![![810, 1616, -2519, 1097, 1992]], ![![1314, 2538, -3902, 1690, 3015]]]
  g := ![![![3211, 10866, 39262, -15974, -43190], ![6504, 22017, 79556, -32348, -87528], ![13008, 44040, 159133, -64640, -175120], ![9474, 32100, 115991, -46939, -127756], ![4650, 15734, 56852, -23154, -62525]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [16, 19, 96, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 102, 66], [77, 76, 113], [0, 1]]
 g := ![![[22, 23, 5], [85, 28, 108], [114, 87], [128, 59], [51, 159, 60], [68, 83, 1], []], ![[154, 97, 141, 9], [116, 10, 75, 138], [98, 64], [169, 70], [92, 49, 163, 156], [39, 157, 30, 125], [7, 60]], ![[27, 9, 160, 50], [156, 2, 148, 159], [11, 47], [166, 75], [104, 0, 40, 54], [40, 156, 109, 159], [139, 60]]]
 h' := ![![[6, 102, 66], [72, 102, 149], [14, 77, 114], [76, 51, 83], [79, 84, 43], [165, 65, 113], [0, 0, 1], [0, 1]], ![[77, 76, 113], [100, 30, 156], [46, 55, 142], [160, 144, 8], [0, 60, 41], [22, 132, 169], [103, 131, 76], [6, 102, 66]], ![[0, 1], [59, 47, 53], [145, 47, 102], [58, 163, 88], [108, 35, 95], [142, 161, 76], [125, 48, 102], [77, 76, 113]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 149], []]
 b := ![[], [153, 123, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [16, 19, 96, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20721058, -59128302, 156924232, -79346334, -208892670]
  a := ![-162, -18, -200, 126, 414]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![15096710, 52084986, 191151410, -79346334, -208892670]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -4, 18, -10, -32]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![11, -4, 18, -10, -32]] 
 ![![179, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![166, 0, 1, 0, 0], ![162, 0, 0, 1, 0], ![67, 0, 0, 0, 1]] where
  M :=![![![11, -4, 18, -10, -32], ![-24, 17, -66, 36, 104], ![-48, -58, 61, -20, -16], ![276, 10, 326, -197, -716], ![-132, -30, -106, 72, 283]]]
  hmulB := by decide  
  f := ![![![44593, 31420, 37306, -25434, -68744]], ![![7233, 5097, 6052, -4126, -11152]], ![![42386, 29866, 35461, -24176, -65344]], ![![41154, 28998, 34430, -23473, -63444]], ![![17045, 12010, 14260, -9722, -26277]]]
  g := ![![![5, -4, 18, -10, -32], ![-13, 17, -66, 36, 104], ![-24, -58, 61, -20, -16], ![144, 10, 326, -197, -716], ![-69, -30, -106, 72, 283]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -2, 14, -8, -26]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![7, -2, 14, -8, -26]] 
 ![![179, 0, 0, 0, 0], ![157, 1, 0, 0, 0], ![53, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![157, 0, 0, 0, 1]] where
  M :=![![![7, -2, 14, -8, -26], ![-24, 11, -58, 32, 96], ![0, -50, 107, -52, -128], ![180, 36, 150, -101, -392], ![-72, -36, -14, 18, 101]]]
  hmulB := by decide  
  f := ![![![389, 202, 566, -476, -1222]], ![![355, 181, 508, -428, -1098]], ![![179, 80, 225, -192, -490]], ![![267, 110, 308, -265, -674]], ![![331, 174, 488, -410, -1053]]]
  g := ![![![23, -2, 14, -8, -26], ![-87, 11, -58, 32, 96], ![141, -50, 107, -52, -128], ![301, 36, 150, -101, -392], ![-59, -36, -14, 18, 101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![28097, 19818, 23460, -15974, -43190]] ![![11, -4, 18, -10, -32]]
  ![![-389, -202, -566, 476, 1222]] where
 M := ![![![-389, -202, -566, 476, 1222]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![-389, -202, -566, 476, 1222]] ![![7, -2, 14, -8, -26]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![-179, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5251, -2586, -5206, 3108, 9210]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![5251, -2586, -5206, 3108, 9210]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![141, 150, 122, 1, 0], ![96, 86, 66, 0, 1]] where
  M :=![![![5251, -2586, -5206, 3108, 9210], ![-1368, 3039, 4914, -3056, -8784], ![4608, 874, 15, -124, -64], ![2532, 884, 258, -121, -288], ![3408, -796, -1994, 1126, 3461]]]
  hmulB := by decide  
  f := ![![![-137, -130, 110, -32, 34]], ![![1560, 71, 1854, -1144, -4032]], ![![-7200, 1670, -12961, 7420, 23776]], ![![-3621, 1052, -6986, 3959, 12506]], ![![-1992, 590, -3868, 2190, 6909]]]
  g := ![![![-7277, -6966, -5482, 3108, 9210], ![7032, 6723, 5290, -3056, -8784], ![156, 138, 107, -124, -64], ![261, 242, 188, -121, -288], ![-2694, -2582, -2032, 1126, 3461]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [164, 162, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [162, 149, 9], [150, 31, 172], [0, 1]]
 g := ![![[116, 141, 9], [40, 166], [41, 171, 178], [16, 34], [77, 177, 4], [166, 131, 1], []], ![[158, 108, 52, 132], [54, 14], [174, 159, 135, 129], [1, 100], [12, 103, 66, 101], [98, 102, 132, 142], [80, 81]], ![[45, 56, 103, 108], [55, 100], [7, 153, 178, 52], [15, 129], [120, 15, 29, 36], [152, 17, 64, 15], [98, 81]]]
 h' := ![![[162, 149, 9], [142, 173, 178], [154, 100, 96], [45, 113, 97], [42, 174, 136], [107, 132, 179], [0, 0, 1], [0, 1]], ![[150, 31, 172], [18, 44, 16], [27, 145, 75], [125, 41, 42], [17, 121, 171], [130, 39, 40], [92, 131, 31], [162, 149, 9]], ![[0, 1], [111, 145, 168], [9, 117, 10], [133, 27, 42], [56, 67, 55], [173, 10, 143], [93, 50, 149], [150, 31, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 73], []]
 b := ![[], [104, 11, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [164, 162, 50, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1255730619, -411346113, -1101421699, 985286854, 2470278158]
  a := ![-163, 3, -201, 170, 418]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2084684421, -1992532021, -1570965615, 985286854, 2470278158]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 130, -110, 32, -34]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![137, 130, -110, 32, -34]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![35, 118, 1, 0, 0], ![107, 115, 0, 1, 0], ![42, 74, 0, 0, 1]] where
  M :=![![![137, 130, -110, 32, -34], ![-1560, -71, -1854, 1144, 4032], ![7200, -1670, 12961, -7420, -23776], ![-8316, 5648, -23166, 12549, 37080], ![6360, -2944, 14686, -8126, -24801]]]
  hmulB := by decide  
  f := ![![![-5251, 2586, 5206, -3108, -9210]], ![![1368, -3039, -4914, 3056, 8784]], ![![-149, -1486, -2197, 1392, 3946]], ![![-2249, -407, -46, 105, 138]], ![![-678, -638, -790, 522, 1435]]]
  g := ![![![11, 66, -110, 32, -34], ![-1262, -1167, -1854, 1144, 4032], ![7437, 5976, 12961, -7420, -23776], ![-11589, -7999, -23166, 12549, 37080], ![7754, 5712, 14686, -8126, -24801]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P1 : CertificateIrreducibleZModOfList' 181 2 2 7 [153, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 180], [0, 1]]
 g := ![![[120, 44], [119], [40, 48], [169], [89, 156], [106, 87], [1]], ![[83, 137], [119], [49, 133], [169], [73, 25], [111, 94], [1]]]
 h' := ![![[102, 180], [144, 15], [34, 32], [161, 49], [139, 168], [72, 95], [28, 102], [0, 1]], ![[0, 1], [45, 166], [40, 149], [91, 132], [80, 13], [169, 86], [115, 79], [102, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [66, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N1 : CertifiedPrimeIdeal' SI181N1 181 where
  n := 2
  hpos := by decide
  P := [153, 79, 1]
  hirr := P181P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2969, 2965, -3781, 1436, 856]
  a := ![-47, -7, -58, 36, 120]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-300, 1219, -3781, 1436, 856]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N1 B_one_repr
lemma NI181N1 : Nat.card (O ⧸ I181N1) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![5251, -2586, -5206, 3108, 9210]] ![![137, 130, -110, 32, -34]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2953, -1917, -3629, 2192, 6440]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![2953, -1917, -3629, 2192, 6440]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![0, 0, 0, 191, 0], ![154, 131, 0, 16, 1]] where
  M :=![![![2953, -1917, -3629, 2192, 6440], ![-1632, 1380, 2483, -1514, -4416], ![1512, -537, -1146, 678, 2024], ![756, -173, -573, 339, 1012], ![1596, -917, -1719, 1034, 3049]]]
  hmulB := by decide  
  f := ![![![-1, -1, 1, 0, 0]], ![![0, 0, -1, 2, 0]], ![![-72, -5, -90, 62, 184]], ![![-12, -51, 75, -19, -92]], ![![-2, -5, 6, 0, -7]]]
  g := ![![![-5177, -4427, -19, -528, 6440], ![3552, 3036, 13, 362, -4416], ![-1624, -1391, -6, -166, 2024], ![-812, -695, -3, -83, 1012], ![-2450, -2096, -9, -250, 3049]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 4 2 7 [115, 29, 173, 108, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 184, 53, 45], [66, 39, 95, 86], [151, 158, 43, 60], [0, 1]]
 g := ![![[144, 26, 33, 43], [57, 85, 71, 16], [12, 124, 128, 39], [77, 51, 117, 121], [45, 138, 30, 6], [83, 1], []], ![[102, 56, 12, 164, 132, 130], [170, 25, 4, 189, 101, 9], [86, 106, 24, 174, 137, 68], [34, 149, 26, 127, 184, 100], [101, 134, 179, 27, 161, 25], [41, 155, 38, 2, 88, 32], [172, 181, 115]], ![[20, 116, 0, 23, 178, 18], [121, 166, 143, 20, 51, 79], [164, 158, 182, 51, 131, 85], [181, 88, 101, 115, 151, 30], [131, 179, 134, 188, 68, 16], [112, 115, 150, 46, 4, 54], [76, 99, 138]], ![[57, 30, 89, 105, 67, 158], [93, 177, 25, 135, 137, 45], [86, 93, 57, 154, 86, 51], [10, 12, 37, 123, 79, 120], [154, 18, 147, 142, 73, 2], [44, 41, 164, 124, 111, 79], [104, 79, 162]]]
 h' := ![![[57, 184, 53, 45], [130, 162, 85, 132], [148, 85, 10, 4], [122, 57, 101, 82], [173, 40, 35, 11], [5, 152, 128, 31], [0, 0, 1], [0, 1]], ![[66, 39, 95, 86], [44, 158, 168, 49], [30, 152, 131, 150], [123, 172, 29, 157], [98, 95, 86, 118], [95, 46, 45, 59], [86, 139, 72, 60], [57, 184, 53, 45]], ![[151, 158, 43, 60], [155, 92, 184, 13], [142, 4, 82, 25], [128, 175, 68, 73], [138, 56, 2, 119], [106, 30, 161, 112], [9, 154, 126, 121], [66, 39, 95, 86]], ![[0, 1], [54, 161, 136, 188], [108, 141, 159, 12], [72, 169, 184, 70], [19, 0, 68, 134], [70, 154, 48, 180], [145, 89, 183, 10], [151, 158, 43, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [22, 87, 23], []]
 b := ![[], [], [144, 106, 134, 113], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 4
  hpos := by decide
  P := [115, 29, 173, 108, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-299383956686, -98666560471, -263131417973, 235992546415, 588220086132]
  a := ![-165, -7, -203, 151, 422]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-475839147754, -403955486093, -1377651403, -48039417967, 588220086132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 1330863361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -1, 1, 0, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-1, -1, 1, 0, 0]] 
 ![![191, 0, 0, 0, 0], ![88, 1, 0, 0, 0], ![87, 0, 1, 0, 0], ![139, 0, 0, 1, 0], ![60, 0, 0, 0, 1]] where
  M :=![![![-1, -1, 1, 0, 0], ![0, 0, -1, 2, 0], ![-72, -5, -90, 62, 184], ![-12, -51, 75, -19, -92], ![-36, 15, -77, 42, 135]]]
  hmulB := by decide  
  f := ![![![2953, -1917, -3629, 2192, 6440]], ![![1352, -876, -1659, 1002, 2944]], ![![1353, -876, -1659, 1002, 2944]], ![![2153, -1396, -2644, 1597, 4692]], ![![936, -607, -1149, 694, 2039]]]
  g := ![![![0, -1, 1, 0, 0], ![-1, 0, -1, 2, 0], ![-60, -5, -90, 62, 184], ![32, -51, 75, -19, -92], ![-45, 15, -77, 42, 135]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![2953, -1917, -3629, 2192, 6440]] ![![-1, -1, 1, 0, 0]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![191, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, -164, 662, -358, -1054]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![233, -164, 662, -358, -1054]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![17, 69, 1, 0, 0], ![89, 41, 0, 1, 0], ![154, 168, 0, 0, 1]] where
  M :=![![![233, -164, 662, -358, -1054], ![240, 557, -918, 408, 792], ![-5184, -702, -5131, 3300, 12192], ![13632, -2640, 23394, -13495, -43668], ![-7596, 744, -11430, 6738, 22451]]]
  hmulB := by decide  
  f := ![![![-7375, -2752, -2438, 1834, 4642]], ![![-10320, -8839, -11010, 7392, 20184]], ![![-4463, -3485, -4247, 2870, 7802]], ![![-5687, -3211, -3538, 2467, 6566]], ![![-14914, -9916, -11558, 7918, 21327]]]
  g := ![![![949, 756, 662, -358, -1054], ![-738, -445, -918, 408, 792], ![-10825, -9483, -5131, 3300, 12192], ![39077, 32501, 23394, -13495, -43668], ![-20054, -16884, -11430, 6738, 22451]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [12, 160, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 192], [0, 1]]
 g := ![![[142, 177], [98], [166], [121], [112], [192], [33, 1]], ![[0, 16], [98], [166], [121], [112], [192], [66, 192]]]
 h' := ![![[33, 192], [116, 131], [110, 171], [128, 72], [6, 11], [112, 43], [183, 112], [0, 1]], ![[0, 1], [0, 62], [156, 22], [188, 121], [176, 182], [180, 150], [19, 81], [33, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132]]
 b := ![[], [69, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [12, 160, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-182859, -83178, -127687, 144036, 304728]
  a := ![-241, -13, -298, 214, 616]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-299272, -250635, -127687, 144036, 304728]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-119, -84, -100, 68, 184]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-119, -84, -100, 68, 184]] 
 ![![193, 0, 0, 0, 0], ![65, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![140, 0, 0, 0, 1]] where
  M :=![![![-119, -84, -100, 68, 184], ![-240, -171, -200, 136, 368], ![-480, -344, -403, 272, 736], ![-360, -260, -304, 201, 552], ![-168, -120, -140, 96, 257]]]
  hmulB := by decide  
  f := ![![![2137, -1484, -2796, 1692, 4968]], ![![713, -495, -932, 564, 1656]], ![![237, -164, -311, 188, 552]], ![![633, -440, -828, 501, 1472]], ![![1556, -1080, -2036, 1232, 3617]]]
  g := ![![![-115, -84, -100, 68, 184], ![-229, -171, -200, 136, 368], ![-457, -344, -403, 272, 736], ![-341, -260, -304, 201, 552], ![-160, -120, -140, 96, 257]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 3, 9, -8, -20]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![11, 3, 9, -8, -20]] 
 ![![193, 0, 0, 0, 0], ![115, 1, 0, 0, 0], ![92, 0, 1, 0, 0], ![153, 0, 0, 1, 0], ![132, 0, 0, 0, 1]] where
  M :=![![![11, 3, 9, -8, -20], ![48, 16, 43, -38, -96], ![216, 71, 190, -170, -424], ![492, 153, 447, -391, -988], ![-36, -9, -37, 30, 79]]]
  hmulB := by decide  
  f := ![![![347, 129, 117, -88, -228]], ![![209, 79, 72, -54, -140]], ![![172, 65, 62, -46, -120]], ![![279, 106, 94, -71, -184]], ![![240, 89, 83, -62, -161]]]
  g := ![![![14, 3, 9, -8, -20], ![66, 16, 43, -38, -96], ![293, 71, 190, -170, -424], ![684, 153, 447, -391, -988], ![-55, -9, -37, 30, 79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2

def I193N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![377, 206, 235, -167, -442]] i)))

def SI193N3: IdealEqSpanCertificate' Table ![![377, 206, 235, -167, -442]] 
 ![![193, 0, 0, 0, 0], ![137, 1, 0, 0, 0], ![145, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![377, 206, 235, -167, -442], ![708, 504, 649, -454, -1220], ![1704, 1045, 1414, -1030, -2728], ![1818, 973, 1549, -1199, -3122], ![426, 293, 313, -206, -561]]]
  hmulB := by decide  
  f := ![![![4979, -382, 7255, -4301, -14436]], ![![3439, -238, 4954, -2943, -9904]], ![![3899, -455, 6025, -3535, -11708]], ![![1243, 153, 1264, -808, -2962]], ![![604, -211, 1243, -698, -2177]]]
  g := ![![![-231, 206, 235, -167, -442], ![-595, 504, 649, -454, -1220], ![-1241, 1045, 1414, -1030, -2728], ![-1207, 973, 1549, -1199, -3122], ![-328, 293, 313, -206, -561]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N3 : Nat.card (O ⧸ I193N3) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N3)

lemma isPrimeI193N3 : Ideal.IsPrime I193N3 := prime_ideal_of_norm_prime hp193.out _ NI193N3
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![233, -164, 662, -358, -1054]] ![![-119, -84, -100, 68, 184]]
  ![![-175, 304, -894, 462, 1258]] where
 M := ![![![-175, 304, -894, 462, 1258]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![-175, 304, -894, 462, 1258]] ![![11, 3, 9, -8, -20]]
  ![![1579, 229, 1605, -1074, -3702]] where
 M := ![![![1579, 229, 1605, -1074, -3702]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI193N2 : IdealMulLeCertificate' Table 
  ![![1579, 229, 1605, -1074, -3702]] ![![377, 206, 235, -167, -442]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![-37249, -11773, -33196, 29529, 74112]]]
 hmul := by decide  
 g := ![![![![-193, -61, -172, 153, 384]]]]
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

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0, 0, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0, 0, 0]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![0, 0, 0, 197, 0], ![0, 0, 0, 0, 197]] where
  M :=![![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![0, 0, 0, 197, 0], ![0, 0, 0, 0, 197]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 5 2 7 [14, 7, 110, 47, 118, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 165, 122, 179, 172], [185, 72, 158, 13, 94], [115, 4, 41, 185, 101], [116, 152, 73, 17, 27], [0, 1]]
 g := ![![[10, 40, 77, 120, 155], [42, 150, 3, 1], [75, 52, 21, 85, 96], [99, 108, 80, 190], [67, 78, 123, 83], [79, 1], []], ![[55, 130, 153, 73, 165, 33, 85, 136], [68, 157, 122, 157], [34, 98, 20, 194, 79, 33, 61, 9], [112, 113, 166, 112], [93, 22, 9, 174], [141, 59, 28, 26], [75, 167, 161, 183, 148, 34, 161, 135]], ![[94, 90, 172, 23, 0, 36, 127, 183], [9, 147, 150, 112], [87, 127, 156, 32, 74, 112, 180, 153], [122, 56, 21, 25], [81, 105, 90, 100], [86, 188, 65, 64], [57, 126, 42, 121, 5, 143, 18, 32]], ![[84, 1, 76, 120, 35, 86, 95, 182], [192, 101, 174, 181], [192, 3, 101, 143, 14, 130, 146, 136], [139, 35, 63, 36], [15, 65, 40, 39], [55, 92, 192, 109], [49, 69, 181, 8, 112, 85, 49, 188]], ![[78, 73, 184, 47, 195, 83, 86, 123], [185, 177, 26, 154], [154, 37, 41, 164, 0, 39, 74, 176], [128, 71, 43, 63], [118, 190, 81, 173], [66, 23, 127, 1], [20, 186, 75, 136, 136, 15, 179, 180]]]
 h' := ![![[57, 165, 122, 179, 172], [91, 25, 135, 139, 130], [132, 189, 151, 38, 196], [76, 92, 9, 11, 80], [110, 117, 123, 79, 105], [76, 24, 168, 117, 87], [0, 0, 0, 1], [0, 1]], ![[185, 72, 158, 13, 94], [67, 150, 62, 68, 140], [172, 109, 7, 71, 123], [1, 24, 120, 178, 166], [92, 195, 107, 125, 167], [139, 41, 86, 107, 119], [145, 39, 160, 139, 82], [57, 165, 122, 179, 172]], ![[115, 4, 41, 185, 101], [18, 76, 160, 63, 5], [12, 149, 189, 98, 30], [28, 167, 2, 118, 44], [95, 108, 73, 156, 192], [21, 37, 74, 95, 187], [35, 179, 169, 78, 189], [185, 72, 158, 13, 94]], ![[116, 152, 73, 17, 27], [27, 23, 86, 20, 83], [101, 44, 188, 54, 141], [61, 159, 143, 40, 139], [49, 105, 159, 113, 6], [72, 161, 131, 91, 32], [137, 185, 114, 152, 122], [115, 4, 41, 185, 101]], ![[0, 1], [107, 120, 148, 104, 36], [50, 100, 56, 133, 101], [6, 149, 120, 47, 162], [5, 66, 129, 118, 121], [188, 131, 132, 181, 166], [179, 188, 148, 24, 1], [116, 152, 73, 17, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 29, 139, 94], [], [], []]
 b := ![[], [143, 2, 18, 56, 185], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 5
  hpos := by decide
  P := [14, 7, 110, 47, 118, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-292658582166143, -93999728735513, -260765296301655, 231195899816403, 580675510788631]
  a := ![-127, -3, -157, 121, 325]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1485576559219, -477155983429, -1323681707115, 1173583247799, 2947591425323]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 296709280757 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def PBC197 : ContainsPrimesAboveP 197 ![I197N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![197, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 197 (by decide) 𝕀



lemma PB696I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB696I4 : PrimesBelowBoundCertificateInterval O 151 197 696 where
  m := 9
  g := ![1, 2, 3, 1, 3, 2, 2, 4, 1]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB696I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1, I193N2, I193N3]
    · exact ![I197N0]
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
    · exact ![95388992557]
    · exact ![705911761, 163]
    · exact ![27889, 27889, 167]
    · exact ![154963892093]
    · exact ![5735339, 179, 179]
    · exact ![5929741, 32761]
    · exact ![1330863361, 191]
    · exact ![37249, 193, 193, 193]
    · exact ![296709280757]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
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
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
      exact NI193N3
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
  β := ![I163N1, I167N2, I179N1, I179N2, I191N1, I193N1, I193N2, I193N3]
  Il := ![[], [I163N1], [I167N2], [], [I179N1, I179N2], [], [I191N1], [I193N1, I193N2, I193N3], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
