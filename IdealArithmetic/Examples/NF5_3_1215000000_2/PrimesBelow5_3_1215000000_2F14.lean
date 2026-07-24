
import IdealArithmetic.Examples.NF5_3_1215000000_2.RI5_3_1215000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp709 : Fact (Nat.Prime 709) := {out := by norm_num}

def I709N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5073, 771, -1330, -7819, -3636]] i)))

def SI709N0: IdealEqSpanCertificate' Table ![![5073, 771, -1330, -7819, -3636]] 
 ![![709, 0, 0, 0, 0], ![0, 709, 0, 0, 0], ![84, 162, 1, 0, 0], ![455, 78, 0, 1, 0], ![354, 170, 0, 0, 1]] where
  M :=![![![5073, 771, -1330, -7819, -3636], ![21816, 3314, -5718, -33625, -15638], ![93828, 14245, -24593, -144607, -67250], ![173048, 26279, -45360, -266706, -124034], ![249572, 37901, -65416, -384651, -178883]]]
  hmulB := by decide  
  f := ![![![4229, 2035, 1140, -191, -560]], ![![3360, 1600, 704, -131, -382]], ![![1272, 609, 297, -53, -154]], ![![3087, 1484, 810, -137, -402]], ![![2918, 1399, 738, -127, -371]]]
  g := ![![![6998, 2037, -1330, -7819, -3636], ![30095, 8760, -5718, -33625, -15638], ![129425, 37673, -24593, -144607, -67250], ![238706, 69483, -45360, -266706, -124034], ![344267, 100209, -65416, -384651, -178883]]]
  hle1 := by decide   
  hle2 := by decide  


def P709P0 : CertificateIrreducibleZModOfList' 709 2 2 9 [360, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [634, 708], [0, 1]]
 g := ![![[207, 484], [335], [59, 240], [494], [82], [76], [197, 534], [96, 662], [1]], ![[66, 225], [335], [493, 469], [494], [82], [76], [560, 175], [76, 47], [1]]]
 h' := ![![[634, 708], [121, 687], [30, 572], [650, 586], [582, 505], [691, 662], [689, 160], [181, 356], [349, 634], [0, 1]], ![[0, 1], [353, 22], [379, 137], [658, 123], [284, 204], [671, 47], [33, 549], [423, 353], [302, 75], [634, 708]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [483]]
 b := ![[], [371, 596]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI709N0 : CertifiedPrimeIdeal' SI709N0 709 where
  n := 2
  hpos := by decide
  P := [360, 75, 1]
  hirr := P709P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7718, -6211, 7097, 13430, 11916]
  a := ![0, 7, -7, -5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15420, -5965, 7097, 13430, 11916]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI709N0 : Ideal.IsPrime I709N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI709N0 B_one_repr
lemma NI709N0 : Nat.card (O ⧸ I709N0) = 502681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI709N0

def I709N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, -52, 21, -47, 28]] i)))

def SI709N1: IdealEqSpanCertificate' Table ![![61, -52, 21, -47, 28]] 
 ![![709, 0, 0, 0, 0], ![0, 709, 0, 0, 0], ![41, 421, 1, 0, 0], ![641, 393, 0, 1, 0], ![465, 494, 0, 0, 1]] where
  M :=![![![61, -52, 21, -47, 28], ![-168, 171, -120, 184, -94], ![564, -514, 475, -740, 368], ![-604, 530, -458, 779, -402], ![1142, -988, 815, -1431, 749]]]
  hmulB := by decide  
  f := ![![![-355, -24, 141, 695, 314]], ![![-1884, -249, 530, 3002, 1390]], ![![-1151, -151, 326, 1841, 852]], ![![-1387, -163, 427, 2326, 1070]], ![![-1577, -194, 470, 2596, 1197]]]
  g := ![![![23, -6, 21, -47, 28], ![-98, 35, -120, 184, -94], ![401, -129, 475, -740, 368], ![-415, 121, -458, 779, -402], ![757, -214, 815, -1431, 749]]]
  hle1 := by decide   
  hle2 := by decide  


def P709P1 : CertificateIrreducibleZModOfList' 709 2 2 9 [342, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [664, 708], [0, 1]]
 g := ![![[280, 194], [593], [258, 546], [494], [240], [60], [187, 133], [629, 607], [1]], ![[58, 515], [593], [503, 163], [494], [240], [60], [583, 576], [256, 102], [1]]]
 h' := ![![[664, 708], [272, 504], [389, 579], [470, 485], [26, 505], [216, 123], [565, 293], [418, 177], [367, 664], [0, 1]], ![[0, 1], [280, 205], [567, 130], [624, 224], [698, 204], [353, 586], [142, 416], [252, 532], [265, 45], [664, 708]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [600]]
 b := ![[], [369, 300]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI709N1 : CertifiedPrimeIdeal' SI709N1 709 where
  n := 2
  hpos := by decide
  P := [342, 45, 1]
  hirr := P709P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-698204, -1710778, 1791450, 1464378, 2622854]
  a := ![3, 62, -124, -1, -249]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3148718, -3705362, 1791450, 1464378, 2622854]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI709N1 : Ideal.IsPrime I709N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI709N1 B_one_repr
lemma NI709N1 : Nat.card (O ⧸ I709N1) = 502681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI709N1

def I709N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-849, -435, -223, 42, 110]] i)))

def SI709N2: IdealEqSpanCertificate' Table ![![-849, -435, -223, 42, 110]] 
 ![![709, 0, 0, 0, 0], ![126, 1, 0, 0, 0], ![431, 0, 1, 0, 0], ![45, 0, 0, 1, 0], ![535, 0, 0, 0, 1]] where
  M :=![![![-849, -435, -223, 42, 110], ![-660, -338, -170, 33, 84], ![-504, -271, -135, 27, 66], ![-520, -269, -138, 26, 68], ![-22, -1, -1, 0, 1]]]
  hmulB := by decide  
  f := ![![![-169, 37, -25, 252, -4]], ![![-30, 6, -4, 45, 0]], ![![-107, 24, -16, 159, -2]], ![![-13, 0, 1, 20, 4]], ![![-137, 30, -20, 204, -1]]]
  g := ![![![126, -435, -223, 42, 110], ![97, -338, -170, 33, 84], ![78, -271, -135, 27, 66], ![78, -269, -138, 26, 68], ![0, -1, -1, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI709N2 : Nat.card (O ⧸ I709N2) = 709 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI709N2)

lemma isPrimeI709N2 : Ideal.IsPrime I709N2 := prime_ideal_of_norm_prime hp709.out _ NI709N2
def MulI709N0 : IdealMulLeCertificate' Table 
  ![![5073, 771, -1330, -7819, -3636]] ![![61, -52, 21, -47, 28]]
  ![![169, -37, 25, -252, 4]] where
 M := ![![![169, -37, 25, -252, 4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI709N1 : IdealMulLeCertificate' Table 
  ![![169, -37, 25, -252, 4]] ![![-849, -435, -223, 42, 110]]
  ![![709, 0, 0, 0, 0]] where
 M := ![![![-709, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC709 : ContainsPrimesAboveP 709 ![I709N0, I709N1, I709N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI709N0
    exact isPrimeI709N1
    exact isPrimeI709N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 709 (by decide) (𝕀 ⊙ MulI709N0 ⊙ MulI709N1)
instance hp719 : Fact (Nat.Prime 719) := {out := by norm_num}

def I719N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, -148, -141, -93, 126]] i)))

def SI719N0: IdealEqSpanCertificate' Table ![![257, -148, -141, -93, 126]] 
 ![![719, 0, 0, 0, 0], ![0, 719, 0, 0, 0], ![0, 0, 719, 0, 0], ![0, 0, 0, 719, 0], ![236, 695, 16, 393, 1]] where
  M :=![![![257, -148, -141, -93, 126], ![-756, 869, -100, 240, -186], ![1116, -1454, 1209, -1176, 480], ![-840, 646, -910, 1465, -686], ![1542, -888, 1311, -2715, 1475]]]
  hmulB := by decide  
  f := ![![![187, 96, 49, -9, -24]], ![![144, 75, 38, -6, -18]], ![![108, 58, 31, 0, -12]], ![![108, 58, 32, 5, -10]], ![![262, 137, 71, -6, -31]]]
  g := ![![![-41, -122, -3, -69, 126], ![60, 181, 4, 102, -186], ![-156, -466, -9, -264, 480], ![224, 664, 14, 377, -686], ![-482, -1427, -31, -810, 1475]]]
  hle1 := by decide   
  hle2 := by decide  


def P719P0 : CertificateIrreducibleZModOfList' 719 4 2 9 [685, 397, 440, 167, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [477, 505, 167, 308], [373, 283, 485, 127], [421, 649, 67, 284], [0, 1]]
 g := ![![[585, 703, 161, 305], [3, 646, 638, 232], [524, 365, 25, 130], [161, 391, 538, 364], [499, 64, 512], [265, 351, 208], [559, 476, 490, 311], [552, 1], []], ![[542, 377, 511, 292, 253, 114], [310, 536, 317, 492, 668, 449], [178, 27, 557, 605, 517, 33], [304, 143, 437, 690, 157, 667], [604, 414, 427], [253, 518, 298], [24, 112, 493, 493, 49, 285], [109, 87, 82, 603, 517, 165], [646, 213, 675]], ![[284, 282, 240, 191, 422, 593], [462, 96, 65, 559, 61, 131], [44, 242, 248, 444, 164, 67], [425, 379, 438, 661, 548, 341], [255, 676, 144], [617, 422, 418], [326, 612, 257, 636, 163, 487], [387, 27, 189, 601, 205, 205], [63, 72, 311]], ![[44, 160, 363, 0, 363, 262], [249, 267, 494, 159, 715, 158], [299, 50, 534, 126, 535, 138], [246, 186, 399, 568, 356, 291], [664, 7, 642], [85, 271, 234], [373, 234, 243, 79, 563, 483], [611, 264, 447, 18, 405, 602], [287, 143, 128]]]
 h' := ![![[477, 505, 167, 308], [102, 38, 370, 687], [560, 301, 178, 252], [441, 85, 503, 444], [198, 624, 110, 233], [661, 444, 369, 568], [312, 338, 244, 94], [74, 185, 464, 127], [0, 0, 1], [0, 1]], ![[373, 283, 485, 127], [518, 547, 652, 216], [497, 647, 640, 376], [11, 482, 107, 661], [385, 116, 9, 233], [134, 349, 549, 544], [108, 445, 473, 155], [111, 668, 625, 40], [0, 313, 187, 115], [477, 505, 167, 308]], ![[421, 649, 67, 284], [269, 19, 459, 298], [607, 28, 356, 85], [550, 86, 546, 354], [559, 282, 541, 400], [327, 86, 288, 707], [355, 332, 166, 636], [438, 186, 643, 406], [347, 177, 0, 107], [373, 283, 485, 127]], ![[0, 1], [528, 115, 676, 237], [25, 462, 264, 6], [129, 66, 282, 698], [543, 416, 59, 572], [16, 559, 232, 338], [395, 323, 555, 553], [102, 399, 425, 146], [59, 229, 531, 497], [421, 649, 67, 284]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [442, 277, 143], []]
 b := ![[], [], [341, 309, 299, 582], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI719N0 : CertifiedPrimeIdeal' SI719N0 719 where
  n := 4
  hpos := by decide
  P := [685, 397, 440, 167, 1]
  hirr := P719P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12188190458, -3862184872, 5139295867, 19342353108, 11370112560]
  a := ![1, 6, -8, -3, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3749005222, -10995953288, -245872747, -6187916388, 11370112560]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI719N0 : Ideal.IsPrime I719N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI719N0 B_one_repr
lemma NI719N0 : Nat.card (O ⧸ I719N0) = 267248675521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI719N0

def I719N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-187, -96, -49, 9, 24]] i)))

def SI719N1: IdealEqSpanCertificate' Table ![![-187, -96, -49, 9, 24]] 
 ![![719, 0, 0, 0, 0], ![652, 1, 0, 0, 0], ![544, 0, 1, 0, 0], ![325, 0, 0, 1, 0], ![713, 0, 0, 0, 1]] where
  M :=![![![-187, -96, -49, 9, 24], ![-144, -75, -38, 6, 18], ![-108, -58, -31, 0, 12], ![-108, -58, -32, -5, 10], ![6, 0, -3, -15, -7]]]
  hmulB := by decide  
  f := ![![![-257, 148, 141, 93, -126]], ![![-232, 133, 128, 84, -114]], ![![-196, 114, 105, 72, -96]], ![![-115, 66, 65, 40, -56]], ![![-257, 148, 138, 96, -127]]]
  g := ![![![96, -96, -49, 9, 24], ![76, -75, -38, 6, 18], ![64, -58, -31, 0, 12], ![69, -58, -32, -5, 10], ![16, 0, -3, -15, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI719N1 : Nat.card (O ⧸ I719N1) = 719 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI719N1)

lemma isPrimeI719N1 : Ideal.IsPrime I719N1 := prime_ideal_of_norm_prime hp719.out _ NI719N1
def MulI719N0 : IdealMulLeCertificate' Table 
  ![![257, -148, -141, -93, 126]] ![![-187, -96, -49, 9, 24]]
  ![![719, 0, 0, 0, 0]] where
 M := ![![![-719, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC719 : ContainsPrimesAboveP 719 ![I719N0, I719N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI719N0
    exact isPrimeI719N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 719 (by decide) (𝕀 ⊙ MulI719N0)
instance hp727 : Fact (Nat.Prime 727) := {out := by norm_num}

def I727N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1423, -1494, -648, 198, 208]] i)))

def SI727N0: IdealEqSpanCertificate' Table ![![1423, -1494, -648, 198, 208]] 
 ![![727, 0, 0, 0, 0], ![0, 727, 0, 0, 0], ![394, 687, 1, 0, 0], ![538, 69, 0, 1, 0], ![481, 180, 0, 0, 1]] where
  M :=![![![1423, -1494, -648, 198, 208], ![-1248, 2497, -648, -498, 396], ![-2376, 1086, 2647, -66, -996], ![784, -1454, 124, 445, -244], ![904, 1174, -2276, -762, 1263]]]
  hmulB := by decide  
  f := ![![![-13095, -4582, -304, 9558, 5200]], ![![-31200, -6749, 5280, 39846, 19116]], ![![-36738, -8887, 4863, 43068, 20992]], ![![-12938, -4077, 348, 11287, 5864]], ![![-16793, -4764, 1212, 16812, 8463]]]
  g := ![![![69, 540, -648, 198, 208], ![456, 565, -648, -498, 396], ![-730, -2247, 2647, -66, -996], ![-234, -101, 124, 445, -244], ![963, 1912, -2276, -762, 1263]]]
  hle1 := by decide   
  hle2 := by decide  


def P727P0 : CertificateIrreducibleZModOfList' 727 2 2 9 [722, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [694, 726], [0, 1]]
 g := ![![[575, 436], [108, 173], [332, 350], [648], [697, 594], [208], [608, 68], [83, 362], [1]], ![[0, 291], [215, 554], [414, 377], [648], [724, 133], [208], [545, 659], [496, 365], [1]]]
 h' := ![![[694, 726], [540, 479], [206, 30], [295, 99], [577, 241], [289, 137], [132, 558], [415, 550], [5, 694], [0, 1]], ![[0, 1], [0, 248], [670, 697], [663, 628], [621, 486], [130, 590], [620, 169], [440, 177], [367, 33], [694, 726]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [491]]
 b := ![[], [234, 609]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI727N0 : CertifiedPrimeIdeal' SI727N0 727 where
  n := 2
  hpos := by decide
  P := [722, 33, 1]
  hirr := P727P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-91010, -254323, 265705, 199628, 386714]
  a := ![1, -25, 48, -1, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-547714, -366130, 265705, 199628, 386714]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI727N0 : Ideal.IsPrime I727N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI727N0 B_one_repr
lemma NI727N0 : Nat.card (O ⧸ I727N0) = 528529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI727N0

def I727N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![709, 369, 187, -36, -92]] i)))

def SI727N1: IdealEqSpanCertificate' Table ![![709, 369, 187, -36, -92]] 
 ![![727, 0, 0, 0, 0], ![205, 1, 0, 0, 0], ![141, 0, 1, 0, 0], ![416, 0, 0, 1, 0], ![77, 0, 0, 0, 1]] where
  M :=![![![709, 369, 187, -36, -92], ![552, 282, 146, -27, -72], ![432, 217, 109, -21, -54], ![436, 227, 114, -22, -56], ![10, 7, 7, 0, -3]]]
  hmulB := by decide  
  f := ![![![207, -213, 227, -294, 166]], ![![57, -59, 63, -81, 46]], ![![45, -46, 48, -63, 36]], ![![112, -117, 126, -160, 92]], ![![31, -32, 32, -42, 25]]]
  g := ![![![-109, 369, 187, -36, -92], ![-84, 282, 146, -27, -72], ![-64, 217, 109, -21, -54], ![-67, 227, 114, -22, -56], ![-3, 7, 7, 0, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI727N1 : Nat.card (O ⧸ I727N1) = 727 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI727N1)

lemma isPrimeI727N1 : Ideal.IsPrime I727N1 := prime_ideal_of_norm_prime hp727.out _ NI727N1

def I727N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, 29, 14, -3, -4]] i)))

def SI727N2: IdealEqSpanCertificate' Table ![![-29, 29, 14, -3, -4]] 
 ![![727, 0, 0, 0, 0], ![615, 1, 0, 0, 0], ![542, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![167, 0, 0, 0, 1]] where
  M :=![![![-29, 29, 14, -3, -4], ![24, -52, 12, 15, -6], ![36, -21, -49, 15, 30], ![-40, 29, 2, 26, 18], ![-40, -37, 56, 57, -1]]]
  hmulB := by decide  
  f := ![![![-174547, -90057, -45768, 8727, 22576]], ![![-147843, -76279, -38766, 7392, 19122]], ![![-130274, -67215, -34159, 6513, 16850]], ![![-5430, -2801, -1424, 272, 702]], ![![-40099, -20690, -10514, 2004, 5187]]]
  g := ![![![-34, 29, 14, -3, -4], ![36, -52, 12, 15, -6], ![47, -21, -49, 15, 30], ![-31, 29, 2, 26, 18], ![-12, -37, 56, 57, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI727N2 : Nat.card (O ⧸ I727N2) = 727 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI727N2)

lemma isPrimeI727N2 : Ideal.IsPrime I727N2 := prime_ideal_of_norm_prime hp727.out _ NI727N2

def I727N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2167, 1204, 695, 249, -138]] i)))

def SI727N3: IdealEqSpanCertificate' Table ![![2167, 1204, 695, 249, -138]] 
 ![![727, 0, 0, 0, 0], ![674, 1, 0, 0, 0], ![99, 0, 1, 0, 0], ![68, 0, 0, 1, 0], ![238, 0, 0, 0, 1]] where
  M :=![![![2167, 1204, 695, 249, -138], ![828, 809, 758, 1506, 498], ![-2988, 58, 1557, 6768, 3012], ![-6744, -470, 2528, 12595, 5682], ![-11766, -1800, 3135, 18207, 8497]]]
  hmulB := by decide  
  f := ![![![559189, -783160, -61907, 139533, -16380]], ![![518558, -725471, -58194, 129162, -14802]], ![![73845, -104362, -7234, 18705, -2628]], ![![52376, -73758, -5394, 13189, -1734]], ![![184852, -257512, -21845, 45717, -4733]]]
  g := ![![![-1186, 1204, 695, 249, -138], ![-1156, 809, 758, 1506, 498], ![-1889, 58, 1557, 6768, 3012], ![-2956, -470, 2528, 12595, 5682], ![-3259, -1800, 3135, 18207, 8497]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI727N3 : Nat.card (O ⧸ I727N3) = 727 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI727N3)

lemma isPrimeI727N3 : Ideal.IsPrime I727N3 := prime_ideal_of_norm_prime hp727.out _ NI727N3
def MulI727N0 : IdealMulLeCertificate' Table 
  ![![1423, -1494, -648, 198, 208]] ![![709, 369, 187, -36, -92]]
  ![![-7309, 9565, 1373, -1638, -68]] where
 M := ![![![-7309, 9565, 1373, -1638, -68]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI727N1 : IdealMulLeCertificate' Table 
  ![![-7309, 9565, 1373, -1638, -68]] ![![-29, 29, 14, -3, -4]]
  ![![559189, -783160, -61907, 139533, -16380]] where
 M := ![![![559189, -783160, -61907, 139533, -16380]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI727N2 : IdealMulLeCertificate' Table 
  ![![559189, -783160, -61907, 139533, -16380]] ![![2167, 1204, 695, 249, -138]]
  ![![727, 0, 0, 0, 0]] where
 M := ![![![727, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC727 : ContainsPrimesAboveP 727 ![I727N0, I727N1, I727N2, I727N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI727N0
    exact isPrimeI727N1
    exact isPrimeI727N2
    exact isPrimeI727N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 727 (by decide) (𝕀 ⊙ MulI727N0 ⊙ MulI727N1 ⊙ MulI727N2)
instance hp733 : Fact (Nat.Prime 733) := {out := by norm_num}

def I733N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2783, 174, -634, -4070, -1956]] i)))

def SI733N0: IdealEqSpanCertificate' Table ![![2783, 174, -634, -4070, -1956]] 
 ![![733, 0, 0, 0, 0], ![0, 733, 0, 0, 0], ![0, 0, 733, 0, 0], ![0, 0, 0, 733, 0], ![295, 236, 109, 487, 1]] where
  M :=![![![2783, 174, -634, -4070, -1956], ![11736, 1619, -3262, -17708, -8140], ![48840, 8286, -12827, -76334, -35416], ![91024, 13886, -23770, -140451, -65408], ![132160, 19234, -34730, -202566, -94109]]]
  hmulB := by decide  
  f := ![![![12163, 6274, 3190, -610, -1572]], ![![9432, 4867, 2474, -472, -1220]], ![![7320, 3770, 1921, -370, -944]], ![![7472, 3858, 1958, -371, -968]], ![![13985, 7216, 3667, -699, -1809]]]
  g := ![![![791, 630, 290, 1294, -1956], ![3292, 2623, 1206, 5384, -8140], ![14320, 11414, 5249, 23426, -35416], ![26448, 21078, 9694, 43265, -65408], ![38055, 30326, 13947, 62249, -94109]]]
  hle1 := by decide   
  hle2 := by decide  


def P733P0 : CertificateIrreducibleZModOfList' 733 4 2 9 [661, 210, 299, 445, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [638, 668, 171, 124], [81, 48, 375, 186], [302, 16, 187, 423], [0, 1]]
 g := ![![[355, 184, 484, 256], [272, 417, 599], [591, 153, 725, 622], [690, 541, 408, 115], [157, 135, 193, 669], [363, 190, 442], [22, 709, 637, 138], [288, 1], []], ![[415, 3, 468, 316, 27, 549], [239, 654, 212], [471, 287, 376, 579, 627, 37], [495, 174, 468, 284, 7, 36], [66, 392, 695, 399, 615, 256], [276, 52, 184], [559, 540, 547, 372, 691, 225], [208, 201, 521, 45, 259, 41], [381, 129, 716]], ![[46, 284, 585, 59, 10, 498], [193, 330, 127], [262, 123, 417, 407, 476, 135], [490, 529, 159, 247, 684, 379], [528, 566, 257, 574, 521, 44], [137, 97, 711], [640, 307, 104, 155, 706, 397], [646, 154, 662, 66, 312, 491], [131, 209, 145]], ![[608, 498, 206, 83, 130, 89], [57, 703, 521], [590, 289, 700, 226, 129, 335], [161, 589, 421, 546, 62, 198], [693, 145, 326, 698, 35, 414], [685, 662, 563], [699, 64, 32, 711, 313, 177], [641, 673, 373, 50, 220, 656], [248, 60, 77]]]
 h' := ![![[638, 668, 171, 124], [504, 531, 548, 717], [38, 296, 27, 193], [569, 528, 414, 375], [309, 727, 576, 445], [478, 153, 528, 625], [118, 480, 573, 301], [212, 431, 172, 549], [0, 0, 1], [0, 1]], ![[81, 48, 375, 186], [179, 339, 336, 328], [36, 567, 508, 144], [172, 120, 472, 637], [382, 398, 559, 153], [215, 374, 361, 325], [40, 41, 143, 430], [585, 255, 106, 16], [540, 268, 291, 350], [638, 668, 171, 124]], ![[302, 16, 187, 423], [140, 293, 672, 152], [597, 549, 516, 651], [292, 51, 397, 297], [650, 156, 557, 633], [547, 117, 192, 729], [144, 496, 75, 38], [127, 699, 398, 584], [600, 445, 697, 657], [81, 48, 375, 186]], ![[0, 1], [699, 303, 643, 269], [154, 54, 415, 478], [293, 34, 183, 157], [125, 185, 507, 235], [143, 89, 385, 520], [428, 449, 675, 697], [356, 81, 57, 317], [576, 20, 477, 459], [302, 16, 187, 423]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [208, 95, 44], []]
 b := ![[], [], [203, 88, 25, 717], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI733N0 : CertifiedPrimeIdeal' SI733N0 733 where
  n := 4
  hpos := by decide
  P := [661, 210, 299, 445, 1]
  hirr := P733P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3805509162, -30493913594, 29936214819, 14142426321, 41917956027]
  a := ![-1, 7, -17, 8, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16875310419, -13537696502, -6192525228, -27830698716, 41917956027]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI733N0 : Ideal.IsPrime I733N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI733N0 B_one_repr
lemma NI733N0 : Nat.card (O ⧸ I733N0) = 288679469521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI733N0

def I733N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12163, -6274, -3190, 610, 1572]] i)))

def SI733N1: IdealEqSpanCertificate' Table ![![-12163, -6274, -3190, 610, 1572]] 
 ![![733, 0, 0, 0, 0], ![492, 1, 0, 0, 0], ![559, 0, 1, 0, 0], ![55, 0, 0, 1, 0], ![336, 0, 0, 0, 1]] where
  M :=![![![-12163, -6274, -3190, 610, 1572], ![-9432, -4867, -2474, 472, 1220], ![-7320, -3770, -1921, 370, 944], ![-7472, -3858, -1958, 371, 968], ![-224, -110, -62, 18, 25]]]
  hmulB := by decide  
  f := ![![![-2783, -174, 634, 4070, 1956]], ![![-1884, -119, 430, 2756, 1324]], ![![-2189, -144, 501, 3208, 1540]], ![![-333, -32, 80, 497, 236]], ![![-1456, -106, 338, 2142, 1025]]]
  g := ![![![5861, -6274, -3190, 610, 1572], ![4546, -4867, -2474, 472, 1220], ![3525, -3770, -1921, 370, 944], ![3601, -3858, -1958, 371, 968], ![108, -110, -62, 18, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI733N1 : Nat.card (O ⧸ I733N1) = 733 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI733N1)

lemma isPrimeI733N1 : Ideal.IsPrime I733N1 := prime_ideal_of_norm_prime hp733.out _ NI733N1
def MulI733N0 : IdealMulLeCertificate' Table 
  ![![2783, 174, -634, -4070, -1956]] ![![-12163, -6274, -3190, 610, 1572]]
  ![![733, 0, 0, 0, 0]] where
 M := ![![![-733, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC733 : ContainsPrimesAboveP 733 ![I733N0, I733N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI733N0
    exact isPrimeI733N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 733 (by decide) (𝕀 ⊙ MulI733N0)
instance hp739 : Fact (Nat.Prime 739) := {out := by norm_num}

def I739N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![527, 80, -140, -816, -380]] i)))

def SI739N0: IdealEqSpanCertificate' Table ![![527, 80, -140, -816, -380]] 
 ![![739, 0, 0, 0, 0], ![0, 739, 0, 0, 0], ![533, 439, 1, 0, 0], ![516, 130, 0, 1, 0], ![672, 259, 0, 0, 1]] where
  M :=![![![527, 80, -140, -816, -380], ![2280, 343, -596, -3516, -1632], ![9792, 1496, -2577, -15096, -7032], ![18088, 2736, -4732, -27877, -12952], ![26056, 3976, -6848, -40164, -18701]]]
  hmulB := by decide  
  f := ![![![-371, -240, 484, 96, -220]], ![![1320, -1611, -628, 228, 192]], ![![515, -1127, -25, 204, -44]], ![![-28, -450, 228, 107, -120]], ![![128, -787, 220, 168, -133]]]
  g := ![![![1017, 360, -140, -816, -380], ![4372, 1545, -596, -3516, -1632], ![18807, 6653, -2577, -15096, -7032], ![34680, 12258, -4732, -27877, -12952], ![50024, 17693, -6848, -40164, -18701]]]
  hle1 := by decide   
  hle2 := by decide  


def P739P0 : CertificateIrreducibleZModOfList' 739 2 2 9 [574, 661, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [78, 738], [0, 1]]
 g := ![![[417, 421], [282, 574], [151], [5], [263], [170, 625], [81, 26], [728, 172], [1]], ![[0, 318], [714, 165], [151], [5], [263], [146, 114], [631, 713], [103, 567], [1]]]
 h' := ![![[78, 738], [712, 313], [566, 654], [415, 633], [79, 502], [707, 636], [63, 25], [402, 61], [165, 78], [0, 1]], ![[0, 1], [0, 426], [587, 85], [276, 106], [68, 237], [63, 103], [535, 714], [726, 678], [337, 661], [78, 738]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [437]]
 b := ![[], [716, 588]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI739N0 : CertifiedPrimeIdeal' SI739N0 739 where
  n := 2
  hpos := by decide
  P := [574, 661, 1]
  hirr := P739P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20662, -15868, 25800, -41774, 22058]
  a := ![0, 4, 16, -26, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9470, -15730, 25800, -41774, 22058]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI739N0 : Ideal.IsPrime I739N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI739N0 B_one_repr
lemma NI739N0 : Nat.card (O ⧸ I739N0) = 546121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI739N0

def I739N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-123, 252, 144, -262, 108]] i)))

def SI739N1: IdealEqSpanCertificate' Table ![![-123, 252, 144, -262, 108]] 
 ![![739, 0, 0, 0, 0], ![0, 739, 0, 0, 0], ![315, 612, 1, 0, 0], ![138, 598, 0, 1, 0], ![550, 117, 0, 0, 1]] where
  M :=![![![-123, 252, 144, -262, 108], ![-648, 319, -154, 818, -524], ![3144, -2884, 1291, -2788, 1636], ![-2440, 2328, -1942, 2977, -1488], ![3788, -3532, 3872, -5574, 2641]]]
  hmulB := by decide  
  f := ![![![74183, 38484, 19772, -2822, -9236]], ![![55416, 29525, 15890, 1078, -5644]], ![![77559, 40884, 21607, -290, -8608]], ![![58730, 31106, 16574, 385, -6280]], ![![63946, 33311, 17242, -1868, -7739]]]
  g := ![![![-93, 76, 144, -262, 108], ![302, -451, -154, 818, -524], ![-1243, 924, 1291, -2788, 1636], ![1376, -562, -1942, 2977, -1488], ![-2570, 881, 3872, -5574, 2641]]]
  hle1 := by decide   
  hle2 := by decide  


def P739P1 : CertificateIrreducibleZModOfList' 739 2 2 9 [123, 732, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 738], [0, 1]]
 g := ![![[42, 4], [21, 442], [107], [11], [455], [271, 31], [135, 611], [99, 49], [1]], ![[70, 735], [159, 297], [107], [11], [455], [488, 708], [717, 128], [442, 690], [1]]]
 h' := ![![[7, 738], [373, 2], [676, 476], [312, 600], [371, 667], [661, 253], [392, 149], [386, 188], [616, 7], [0, 1]], ![[0, 1], [387, 737], [313, 263], [78, 139], [606, 72], [215, 486], [696, 590], [224, 551], [665, 732], [7, 738]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [729]]
 b := ![[], [387, 734]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI739N1 : CertifiedPrimeIdeal' SI739N1 739 where
  n := 2
  hpos := by decide
  P := [123, 732, 1]
  hirr := P739P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10490, -17894, 11640, 8551, 9725]
  a := ![13, 7, -15, 5, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13782, -18123, 11640, 8551, 9725]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI739N1 : Ideal.IsPrime I739N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI739N1 B_one_repr
lemma NI739N1 : Nat.card (O ⧸ I739N1) = 546121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI739N1

def I739N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![121, -118, -65, 15, 22]] i)))

def SI739N2: IdealEqSpanCertificate' Table ![![121, -118, -65, 15, 22]] 
 ![![739, 0, 0, 0, 0], ![427, 1, 0, 0, 0], ![204, 0, 1, 0, 0], ![488, 0, 0, 1, 0], ![248, 0, 0, 0, 1]] where
  M :=![![![121, -118, -65, 15, 22], ![-132, 237, -38, -48, 30], ![-180, 44, 227, 18, -96], ![88, -144, 8, 31, -10], ![10, 178, -197, -51, 99]]]
  hmulB := by decide  
  f := ![![![-254337, -131226, -66695, 12723, 32896]], ![![-147225, -75961, -38607, 7365, 19042]], ![![-70416, -36332, -18465, 3522, 9108]], ![![-168164, -86764, -44098, 8413, 21750]], ![![-85358, -44042, -22383, 4269, 11041]]]
  g := ![![![69, -118, -65, 15, 22], ![-105, 237, -38, -48, 30], ![-68, 44, 227, 18, -96], ![64, -144, 8, 31, -10], ![-48, 178, -197, -51, 99]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI739N2 : Nat.card (O ⧸ I739N2) = 739 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI739N2)

lemma isPrimeI739N2 : Ideal.IsPrime I739N2 := prime_ideal_of_norm_prime hp739.out _ NI739N2
def MulI739N0 : IdealMulLeCertificate' Table 
  ![![527, 80, -140, -816, -380]] ![![-123, 252, 144, -262, 108]]
  ![![-5221, 4596, -3860, 6574, -3416]] where
 M := ![![![-5221, 4596, -3860, 6574, -3416]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI739N1 : IdealMulLeCertificate' Table 
  ![![-5221, 4596, -3860, 6574, -3416]] ![![121, -118, -65, 15, 22]]
  ![![739, 0, 0, 0, 0]] where
 M := ![![![739, -19214, 14041, 9607, -10346]]]
 hmul := by decide  
 g := ![![![![1, -26, 19, 13, -14]]]]
 hle2 := by decide  


def PBC739 : ContainsPrimesAboveP 739 ![I739N0, I739N1, I739N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI739N0
    exact isPrimeI739N1
    exact isPrimeI739N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 739 (by decide) (𝕀 ⊙ MulI739N0 ⊙ MulI739N1)
instance hp743 : Fact (Nat.Prime 743) := {out := by norm_num}

def I743N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![175, -314, 51, 63, -42]] i)))

def SI743N0: IdealEqSpanCertificate' Table ![![175, -314, 51, 63, -42]] 
 ![![743, 0, 0, 0, 0], ![0, 743, 0, 0, 0], ![0, 0, 743, 0, 0], ![413, 683, 135, 1, 0], ![120, 59, 732, 0, 1]] where
  M :=![![![175, -314, 51, 63, -42], ![252, -65, -302, -36, 126], ![-756, 968, 201, -186, -72], ![-24, -28, 160, -79, -106], ![834, -714, -465, -3, 73]]]
  hmulB := by decide  
  f := ![![![4733, 2442, 1241, -237, -612]], ![![3672, 1893, 964, -186, -474]], ![![2844, 1472, 743, -138, -372]], ![![6527, 3367, 1712, -328, -844]], ![![3858, 1995, 1009, -189, -503]]]
  g := ![![![-28, -55, 30, 63, -42], ![0, 23, -118, -36, 126], ![114, 178, 105, -186, -72], ![61, 81, 119, -79, -106], ![-9, -4, -72, -3, 73]]]
  hle1 := by decide   
  hle2 := by decide  


def P743P0 : CertificateIrreducibleZModOfList' 743 3 2 9 [412, 86, 622, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [508, 187, 375], [356, 555, 368], [0, 1]]
 g := ![![[547, 40, 184], [61, 552, 241], [721, 657, 200], [117, 2], [398, 639], [291, 250, 253], [433, 80, 264], [438, 121, 1], []], ![[350, 148, 22, 487], [279, 498, 305, 605], [78, 711, 250, 137], [316, 53], [42, 436], [636, 111, 415, 463], [73, 457, 241, 459], [658, 404, 368, 366], [5, 198]], ![[595, 724, 549, 587], [635, 263, 438, 254], [683, 79, 531, 16], [122, 723], [0, 171], [19, 632, 307, 111], [610, 711, 519, 62], [361, 370, 521, 575], [12, 198]]]
 h' := ![![[508, 187, 375], [130, 246, 426], [148, 515, 299], [643, 186, 466], [517, 587, 641], [474, 345, 456], [667, 120, 310], [93, 154, 572], [0, 0, 1], [0, 1]], ![[356, 555, 368], [438, 613, 274], [82, 464, 201], [325, 176, 717], [354, 208, 55], [279, 651, 553], [625, 688, 94], [443, 737, 738], [412, 251, 555], [508, 187, 375]], ![[0, 1], [477, 627, 43], [602, 507, 243], [263, 381, 303], [139, 691, 47], [87, 490, 477], [268, 678, 339], [536, 595, 176], [683, 492, 187], [356, 555, 368]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [648, 495], []]
 b := ![[], [646, 516, 177], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI743N0 : CertifiedPrimeIdeal' SI743N0 743 where
  n := 3
  hpos := by decide
  P := [412, 86, 622, 1]
  hirr := P743P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-117523, -233430, 259081, 225877, 385091]
  a := ![-1, 1, -2, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-187908, -238530, -420082, 225877, 385091]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI743N0 : Ideal.IsPrime I743N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI743N0 B_one_repr
lemma NI743N0 : Nat.card (O ⧸ I743N0) = 410172407 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI743N0

def I743N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, -208, 178, -272, 160]] i)))

def SI743N1: IdealEqSpanCertificate' Table ![![223, -208, 178, -272, 160]] 
 ![![743, 0, 0, 0, 0], ![66, 1, 0, 0, 0], ![102, 0, 1, 0, 0], ![41, 0, 0, 1, 0], ![466, 0, 0, 0, 1]] where
  M :=![![![223, -208, 178, -272, 160], ![-960, 797, -658, 1222, -544], ![3264, -3156, 2677, -4016, 2444], ![-4120, 3192, -2610, 5295, -2044], ![6080, -6088, 5186, -7428, 4823]]]
  hmulB := by decide  
  f := ![![![-58247, 37288, 51046, -1376, -20312]], ![![-5010, 3085, 4514, -82, -1808]], ![![-7974, 5252, 6841, -232, -2708]], ![![-3313, 2184, 2840, -97, -1124]], ![![-36402, 23088, 32118, -796, -12801]]]
  g := ![![![-91, -208, 178, -272, 160], ![292, 797, -658, 1222, -544], ![-1394, -3156, 2677, -4016, 2444], ![1059, 3192, -2610, 5295, -2044], ![-2778, -6088, 5186, -7428, 4823]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI743N1 : Nat.card (O ⧸ I743N1) = 743 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI743N1)

lemma isPrimeI743N1 : Ideal.IsPrime I743N1 := prime_ideal_of_norm_prime hp743.out _ NI743N1

def I743N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1099, -446, -309, 31, 156]] i)))

def SI743N2: IdealEqSpanCertificate' Table ![![-1099, -446, -309, 31, 156]] 
 ![![743, 0, 0, 0, 0], ![271, 1, 0, 0, 0], ![116, 0, 1, 0, 0], ![300, 0, 0, 1, 0], ![514, 0, 0, 0, 1]] where
  M :=![![![-1099, -446, -309, 31, 156], ![-936, -353, -106, 40, 62], ![-372, -684, -207, 94, 80], ![-596, -352, -232, 29, 110], ![-314, 310, 121, -45, -35]]]
  hmulB := by decide  
  f := ![![![7991, -9178, 7953, -9437, 7878]], ![![2851, -3303, 2865, -3359, 2848]], ![![1400, -1620, 1405, -1650, 1396]], ![![2924, -3532, 3078, -3405, 3110]], ![![5784, -6714, 5825, -6811, 5795]]]
  g := ![![![89, -446, -309, 31, 156], ![85, -353, -106, 40, 62], ![188, -684, -207, 94, 80], ![76, -352, -232, 29, 110], ![-90, 310, 121, -45, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI743N2 : Nat.card (O ⧸ I743N2) = 743 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI743N2)

lemma isPrimeI743N2 : Ideal.IsPrime I743N2 := prime_ideal_of_norm_prime hp743.out _ NI743N2
def MulI743N0 : IdealMulLeCertificate' Table 
  ![![175, -314, 51, 63, -42]] ![![223, -208, 178, -272, 160]]
  ![![-7991, 9178, -7953, 9437, -7878]] where
 M := ![![![-7991, 9178, -7953, 9437, -7878]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI743N1 : IdealMulLeCertificate' Table 
  ![![-7991, 9178, -7953, 9437, -7878]] ![![-1099, -446, -309, 31, 156]]
  ![![743, 0, 0, 0, 0]] where
 M := ![![![-743, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC743 : ContainsPrimesAboveP 743 ![I743N0, I743N1, I743N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI743N0
    exact isPrimeI743N1
    exact isPrimeI743N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 743 (by decide) (𝕀 ⊙ MulI743N0 ⊙ MulI743N1)
instance hp751 : Fact (Nat.Prime 751) := {out := by norm_num}

def I751N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![751, 0, 0, 0, 0]] i)))

def SI751N0: IdealEqSpanCertificate' Table ![![751, 0, 0, 0, 0]] 
 ![![751, 0, 0, 0, 0], ![0, 751, 0, 0, 0], ![0, 0, 751, 0, 0], ![0, 0, 0, 751, 0], ![0, 0, 0, 0, 751]] where
  M :=![![![751, 0, 0, 0, 0], ![0, 751, 0, 0, 0], ![0, 0, 751, 0, 0], ![0, 0, 0, 751, 0], ![0, 0, 0, 0, 751]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P751P0 : CertificateIrreducibleZModOfList' 751 5 2 9 [603, 242, 527, 237, 16, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [704, 400, 92, 349, 412], [610, 51, 88, 83, 285], [43, 712, 444, 476, 93], [129, 338, 127, 594, 712], [0, 1]]
 g := ![![[431, 492, 698, 435, 229], [165, 415, 125, 731, 430], [284, 62, 641, 692, 655], [681, 475, 637, 384, 106], [361, 93, 468, 430], [329, 723, 208, 158, 663], [110, 138, 111, 484, 256], [1], []], ![[750, 432, 257, 427, 172, 241, 164, 292], [682, 437, 547, 266, 710, 736, 112, 73], [266, 96, 165, 435, 349, 283, 195, 275], [128, 514, 207, 76, 35, 341, 585, 223], [394, 724, 703, 185], [724, 317, 594, 170, 487, 265, 643, 548], [238, 99, 250, 482, 635, 112, 382, 301], [380, 607, 31, 729, 73, 407, 220, 554], [654, 599, 406, 18]], ![[448, 435, 145, 8, 457, 583, 185, 312], [726, 354, 56, 431, 383, 717, 738, 504], [645, 185, 492, 232, 700, 28, 589, 705], [749, 625, 201, 415, 35, 12, 348, 177], [642, 553, 682, 320], [6, 358, 662, 380, 463, 351, 34, 679], [281, 26, 85, 420, 410, 653, 85, 566], [748, 592, 258, 130, 378, 717, 35, 586], [721, 742, 378, 117]], ![[261, 228, 183, 42, 533, 169, 54, 131], [43, 23, 542, 87, 498, 166, 471, 52], [613, 734, 587, 270, 504, 542, 445, 163], [635, 678, 728, 17, 545, 507, 515, 610], [347, 399, 241, 382], [45, 149, 61, 714, 632, 287, 473, 211], [513, 201, 703, 505, 28, 471, 560, 169], [633, 395, 113, 558, 250, 406, 625, 433], [190, 171, 469, 388]], ![[46, 675, 478, 262, 597, 362, 588, 355], [265, 547, 503, 68, 693, 486, 309, 400], [410, 666, 554, 237, 195, 265, 409, 574], [654, 68, 443, 539, 694, 134, 602, 360], [190, 97, 489, 479], [306, 201, 42, 428, 108, 47, 538, 9], [188, 645, 144, 427, 581, 565, 32, 737], [318, 466, 558, 114, 574, 526, 479, 604], [321, 159, 677, 19]]]
 h' := ![![[704, 400, 92, 349, 412], [388, 287, 428, 262, 637], [727, 212, 344, 428, 566], [154, 218, 99, 594, 548], [216, 705, 622, 162, 470], [628, 336, 560, 585, 566], [509, 688, 626, 248, 697], [148, 509, 224, 514, 735], [0, 0, 1], [0, 1]], ![[610, 51, 88, 83, 285], [620, 230, 119, 40, 226], [13, 606, 528, 424, 638], [454, 272, 481, 161, 92], [340, 34, 203, 694, 593], [317, 306, 720, 60, 575], [110, 287, 60, 48, 353], [673, 565, 131, 238, 63], [620, 177, 445, 235, 604], [704, 400, 92, 349, 412]], ![[43, 712, 444, 476, 93], [149, 295, 101, 217, 748], [455, 674, 559, 434, 354], [138, 105, 549, 101, 207], [496, 6, 423, 126, 205], [470, 393, 728, 662, 364], [59, 42, 422, 130, 114], [353, 315, 212, 168, 316], [421, 558, 649, 616, 68], [610, 51, 88, 83, 285]], ![[129, 338, 127, 594, 712], [398, 407, 607, 276, 358], [318, 564, 391, 623, 692], [414, 473, 82, 257, 77], [685, 581, 423, 502, 468], [97, 716, 482, 447, 265], [163, 557, 667, 565, 376], [284, 226, 529, 140, 577], [680, 6, 649, 580, 419], [43, 712, 444, 476, 93]], ![[0, 1], [59, 283, 247, 707, 284], [358, 197, 431, 344, 3], [70, 434, 291, 389, 578], [353, 176, 582, 18, 517], [660, 502, 514, 499, 483], [504, 679, 478, 511, 713], [450, 638, 406, 442, 562], [314, 10, 509, 71, 411], [129, 338, 127, 594, 712]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [740, 57, 378, 346], [], [], []]
 b := ![[], [498, 668, 33, 15, 258], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI751N0 : CertifiedPrimeIdeal' SI751N0 751 where
  n := 5
  hpos := by decide
  P := [603, 242, 527, 237, 16, 1]
  hirr := P751P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-262071095844, -58136554690, 86426832834, 408992714239, 211855645313]
  a := ![3, -3, 4, 2, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-348962844, -77412190, 115082334, 544597489, 282098063]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI751N0 : Ideal.IsPrime I751N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI751N0 B_one_repr
lemma NI751N0 : Nat.card (O ⧸ I751N0) = 238890943128751 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI751N0

def PBC751 : ContainsPrimesAboveP 751 ![I751N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI751N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![751, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 751 (by decide) 𝕀

instance hp757 : Fact (Nat.Prime 757) := {out := by norm_num}

def I757N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-141, 153, 12, -13, -6]] i)))

def SI757N0: IdealEqSpanCertificate' Table ![![-141, 153, 12, -13, -6]] 
 ![![757, 0, 0, 0, 0], ![0, 757, 0, 0, 0], ![0, 0, 757, 0, 0], ![638, 674, 619, 1, 0], ![29, 659, 297, 0, 1]] where
  M :=![![![-141, 153, 12, -13, -6], ![36, -158, 128, -13, -26], ![156, -157, -299, 215, -26], ![116, -51, 62, -212, 126], ![-496, 347, 20, 357, -275]]]
  hmulB := by decide  
  f := ![![![-49, -15, 2, 43, 22]], ![![-132, -28, 26, 181, 86]], ![![-516, -81, 127, 775, 362]], ![![-582, -104, 129, 833, 392]], ![![-321, -57, 73, 466, 219]]]
  g := ![![![11, 17, 13, -13, -6], ![12, 34, 21, -13, -26], ![-180, -169, -166, 215, -26], ![174, 79, 124, -212, 126], ![-291, -78, -184, 357, -275]]]
  hle1 := by decide   
  hle2 := by decide  


def P757P0 : CertificateIrreducibleZModOfList' 757 3 2 9 [622, 156, 625, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [575, 270, 3], [314, 486, 754], [0, 1]]
 g := ![![[565, 344, 232], [176, 610], [128, 240, 236], [314, 615], [215, 596, 501], [598, 572, 426], [63, 110, 204], [614, 132, 1], []], ![[268, 236, 291, 25], [330, 81], [236, 16, 480, 601], [564, 522], [157, 34, 436, 343], [614, 571, 566, 601], [171, 154, 337, 100], [528, 223, 631, 36], [537, 9]], ![[677, 10, 478, 282], [451, 574], [79, 426, 630, 531], [672, 529], [499, 572, 461, 640], [705, 410, 93, 219], [400, 678, 155, 62], [440, 298, 113, 73], [543, 9]]]
 h' := ![![[575, 270, 3], [43, 0, 630], [626, 458, 385], [463, 437, 124], [259, 432, 546], [488, 476, 122], [178, 293, 507], [377, 7, 31], [0, 0, 1], [0, 1]], ![[314, 486, 754], [470, 433, 352], [86, 71, 748], [313, 721, 258], [77, 84, 188], [18, 481, 160], [9, 78, 499], [24, 14, 704], [396, 86, 486], [575, 270, 3]], ![[0, 1], [496, 324, 532], [254, 228, 381], [25, 356, 375], [191, 241, 23], [60, 557, 475], [223, 386, 508], [712, 736, 22], [62, 671, 270], [314, 486, 754]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [154, 524], []]
 b := ![[], [414, 480, 330], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI757N0 : CertifiedPrimeIdeal' SI757N0 757 where
  n := 3
  hpos := by decide
  P := [622, 156, 625, 1]
  hirr := P757P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![753468, -22550250, 21971818, 4872960, 29186424]
  a := ![1, -5, 12, -5, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5224044, -29776458, -15406550, 4872960, 29186424]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI757N0 : Ideal.IsPrime I757N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI757N0 B_one_repr
lemma NI757N0 : Nat.card (O ⧸ I757N0) = 433798093 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI757N0

def I757N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, -15, 2, 43, 22]] i)))

def SI757N1: IdealEqSpanCertificate' Table ![![-49, -15, 2, 43, 22]] 
 ![![757, 0, 0, 0, 0], ![0, 757, 0, 0, 0], ![477, 413, 1, 0, 0], ![351, 215, 0, 1, 0], ![163, 505, 0, 0, 1]] where
  M :=![![![-49, -15, 2, 43, 22], ![-132, -28, 26, 181, 86], ![-516, -81, 127, 775, 362], ![-940, -147, 240, 1428, 666], ![-1336, -205, 350, 2061, 957]]]
  hmulB := by decide  
  f := ![![![-141, 153, 12, -13, -6]], ![![36, -158, 128, -13, -26]], ![![-69, 10, 77, -15, -18]], ![![-55, 26, 42, -10, -10]], ![![-7, -72, 88, -11, -19]]]
  g := ![![![-26, -28, 2, 43, 22], ![-119, -123, 26, 181, 86], ![-518, -531, 127, 775, 362], ![-958, -981, 240, 1428, 666], ![-1384, -1415, 350, 2061, 957]]]
  hle1 := by decide   
  hle2 := by decide  


def P757P1 : CertificateIrreducibleZModOfList' 757 2 2 9 [693, 579, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [178, 756], [0, 1]]
 g := ![![[263, 343], [476], [436, 184], [425], [682, 721], [608, 83], [168, 580], [176, 647], [1]], ![[0, 414], [476], [637, 573], [425], [330, 36], [242, 674], [456, 177], [278, 110], [1]]]
 h' := ![![[178, 756], [611, 273], [652, 276], [653, 694], [499, 157], [305, 235], [154, 362], [666, 375], [64, 178], [0, 1]], ![[0, 1], [0, 484], [575, 481], [37, 63], [436, 600], [500, 522], [245, 395], [43, 382], [711, 579], [178, 756]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [197]]
 b := ![[], [696, 477]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI757N1 : CertifiedPrimeIdeal' SI757N1 757 where
  n := 2
  hpos := by decide
  P := [693, 579, 1]
  hirr := P757P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3079, -62, -534, 524, -536]
  a := ![4, 0, -1, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![213, 500, -534, 524, -536]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI757N1 : Ideal.IsPrime I757N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI757N1 B_one_repr
lemma NI757N1 : Nat.card (O ⧸ I757N1) = 573049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI757N1
def MulI757N0 : IdealMulLeCertificate' Table 
  ![![-141, 153, 12, -13, -6]] ![![-49, -15, 2, 43, 22]]
  ![![757, 0, 0, 0, 0]] where
 M := ![![![757, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC757 : ContainsPrimesAboveP 757 ![I757N0, I757N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI757N0
    exact isPrimeI757N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 757 (by decide) (𝕀 ⊙ MulI757N0)
instance hp761 : Fact (Nat.Prime 761) := {out := by norm_num}

def I761N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11699, 13875, 3851, -2170, -918]] i)))

def SI761N0: IdealEqSpanCertificate' Table ![![-11699, 13875, 3851, -2170, -918]] 
 ![![761, 0, 0, 0, 0], ![0, 761, 0, 0, 0], ![0, 0, 761, 0, 0], ![0, 0, 0, 761, 0], ![186, 629, 688, 135, 1]] where
  M :=![![![-11699, 13875, 3851, -2170, -918], ![5508, -16134, 7854, 3875, -4340], ![26040, -19241, -20113, 1397, 7750], ![-4984, 10877, -3330, -2390, 2068], ![-13978, -415, 21557, 2448, -9469]]]
  hmulB := by decide  
  f := ![![![1, 23, -7, 20, -12]], ![![72, -48, 50, -73, 40]], ![![-240, 215, -171, 317, -146]], ![![236, -219, 194, -276, 176]], ![![-116, 122, -81, 183, -71]]]
  g := ![![![209, 777, 835, 160, -918], ![1068, 3566, 3934, 775, -4340], ![-1860, -6431, -7033, -1373, 7750], ![-512, -1695, -1874, -370, 2068], ![2296, 7826, 8589, 1683, -9469]]]
  hle1 := by decide   
  hle2 := by decide  


def P761P0 : CertificateIrreducibleZModOfList' 761 4 2 9 [138, 60, 169, 69, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [714, 505, 440, 88], [37, 489, 144, 668], [702, 527, 177, 5], [0, 1]]
 g := ![![[61, 637, 80, 389], [444, 391, 722], [280, 133, 74], [81, 454, 391, 471], [592, 351, 113, 36], [190, 733, 379, 278], [269, 43, 317, 676], [692, 1], []], ![[539, 198, 346, 109, 128, 552], [116, 246, 233], [610, 636, 627], [507, 284, 433, 612, 669, 354], [722, 166, 42, 101, 35, 348], [292, 397, 265, 380, 286, 477], [424, 109, 451, 8, 24, 241], [438, 37, 79, 426, 129, 692], [210, 465, 134]], ![[16, 281, 749, 491, 752, 46], [94, 485, 20], [369, 196, 263], [337, 424, 37, 62, 674, 661], [466, 26, 420, 524, 332, 64], [114, 179, 67, 245, 169, 618], [321, 564, 668, 417, 746, 207], [496, 510, 149, 247, 149, 687], [561, 455, 278]], ![[688, 661, 570, 28, 684, 443], [345, 506, 576], [162, 277, 465], [407, 638, 637, 140, 468, 178], [175, 247, 357, 358, 449, 81], [643, 353, 728, 639, 264, 39], [715, 518, 347, 546, 569, 711], [672, 632, 40, 704, 555, 185], [351, 45, 25]]]
 h' := ![![[714, 505, 440, 88], [284, 40, 40, 327], [26, 58, 234, 626], [237, 283, 514, 450], [492, 752, 590, 202], [415, 567, 153, 6], [167, 656, 232, 93], [390, 197, 186, 26], [0, 0, 1], [0, 1]], ![[37, 489, 144, 668], [151, 288, 630, 328], [517, 84, 694, 554], [118, 63, 574, 373], [584, 676, 741, 202], [223, 745, 30, 254], [330, 605, 17, 666], [186, 243, 749, 255], [625, 564, 130, 173], [714, 505, 440, 88]], ![[702, 527, 177, 5], [90, 334, 14, 304], [154, 296, 513, 366], [226, 426, 679, 32], [454, 278, 629, 612], [155, 525, 668, 526], [104, 80, 444, 168], [393, 499, 354, 196], [51, 616, 267, 144], [37, 489, 144, 668]], ![[0, 1], [645, 99, 77, 563], [681, 323, 81, 737], [677, 750, 516, 667], [108, 577, 323, 506], [224, 446, 671, 736], [686, 181, 68, 595], [251, 583, 233, 284], [703, 342, 363, 444], [702, 527, 177, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [131, 292, 364], []]
 b := ![[], [], [293, 449, 175, 724], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI761N0 : CertifiedPrimeIdeal' SI761N0 761 where
  n := 4
  hpos := by decide
  P := [138, 60, 169, 69, 1]
  hirr := P761P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-175333258701, -27983535308, 47274702239, 270601284315, 127451867451]
  a := ![7, 21, 7, -50, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-31381577667, -105381351067, -115163745209, -22254140370, 127451867451]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI761N0 : Ideal.IsPrime I761N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI761N0 B_one_repr
lemma NI761N0 : Nat.card (O ⧸ I761N0) = 335381132641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI761N0

def I761N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 23, -7, 20, -12]] i)))

def SI761N1: IdealEqSpanCertificate' Table ![![1, 23, -7, 20, -12]] 
 ![![761, 0, 0, 0, 0], ![491, 1, 0, 0, 0], ![156, 0, 1, 0, 0], ![304, 0, 0, 1, 0], ![342, 0, 0, 0, 1]] where
  M :=![![![1, 23, -7, 20, -12], ![72, -48, 50, -73, 40], ![-240, 215, -171, 317, -146], ![236, -219, 194, -276, 176], ![-490, 401, -331, 624, -271]]]
  hmulB := by decide  
  f := ![![![-11699, 13875, 3851, -2170, -918]], ![![-7541, 8931, 2495, -1395, -598]], ![![-2364, 2819, 763, -443, -178]], ![![-4680, 5557, 1534, -870, -364]], ![![-5276, 6235, 1759, -972, -425]]]
  g := ![![![-16, 23, -7, 20, -12], ![32, -48, 50, -73, 40], ![-165, 215, -171, 317, -146], ![133, -219, 194, -276, 176], ![-319, 401, -331, 624, -271]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI761N1 : Nat.card (O ⧸ I761N1) = 761 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI761N1)

lemma isPrimeI761N1 : Ideal.IsPrime I761N1 := prime_ideal_of_norm_prime hp761.out _ NI761N1
def MulI761N0 : IdealMulLeCertificate' Table 
  ![![-11699, 13875, 3851, -2170, -918]] ![![1, 23, -7, 20, -12]]
  ![![761, 0, 0, 0, 0]] where
 M := ![![![761, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC761 : ContainsPrimesAboveP 761 ![I761N0, I761N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI761N0
    exact isPrimeI761N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 761 (by decide) (𝕀 ⊙ MulI761N0)


lemma PB1705I14_primes (p : ℕ) :
  p ∈ Set.range ![709, 719, 727, 733, 739, 743, 751, 757, 761] ↔ Nat.Prime p ∧ 701 < p ∧ p ≤ 761 := by
  rw [← List.mem_ofFn']
  convert primes_range 701 761 (by omega)

def PB1705I14 : PrimesBelowBoundCertificateInterval O 701 761 1705 where
  m := 9
  g := ![3, 2, 4, 2, 3, 3, 1, 2, 2]
  P := ![709, 719, 727, 733, 739, 743, 751, 757, 761]
  hP := PB1705I14_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I709N0, I709N1, I709N2]
    · exact ![I719N0, I719N1]
    · exact ![I727N0, I727N1, I727N2, I727N3]
    · exact ![I733N0, I733N1]
    · exact ![I739N0, I739N1, I739N2]
    · exact ![I743N0, I743N1, I743N2]
    · exact ![I751N0]
    · exact ![I757N0, I757N1]
    · exact ![I761N0, I761N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC709
    · exact PBC719
    · exact PBC727
    · exact PBC733
    · exact PBC739
    · exact PBC743
    · exact PBC751
    · exact PBC757
    · exact PBC761
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![502681, 502681, 709]
    · exact ![267248675521, 719]
    · exact ![528529, 727, 727, 727]
    · exact ![288679469521, 733]
    · exact ![546121, 546121, 739]
    · exact ![410172407, 743, 743]
    · exact ![238890943128751]
    · exact ![433798093, 573049]
    · exact ![335381132641, 761]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI709N0
      exact NI709N1
      exact NI709N2
    · dsimp ; intro j
      fin_cases j
      exact NI719N0
      exact NI719N1
    · dsimp ; intro j
      fin_cases j
      exact NI727N0
      exact NI727N1
      exact NI727N2
      exact NI727N3
    · dsimp ; intro j
      fin_cases j
      exact NI733N0
      exact NI733N1
    · dsimp ; intro j
      fin_cases j
      exact NI739N0
      exact NI739N1
      exact NI739N2
    · dsimp ; intro j
      fin_cases j
      exact NI743N0
      exact NI743N1
      exact NI743N2
    · dsimp ; intro j
      fin_cases j
      exact NI751N0
    · dsimp ; intro j
      fin_cases j
      exact NI757N0
      exact NI757N1
    · dsimp ; intro j
      fin_cases j
      exact NI761N0
      exact NI761N1
  β := ![I709N2, I719N1, I727N1, I727N2, I727N3, I733N1, I739N2, I743N1, I743N2, I761N1]
  Il := ![[I709N2], [I719N1], [I727N1, I727N2, I727N3], [I733N1], [I739N2], [I743N1, I743N2], [], [], [I761N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
