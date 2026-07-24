
import IdealArithmetic.Examples.NF5_3_379687500_2.RI5_3_379687500_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp709 : Fact (Nat.Prime 709) := {out := by norm_num}

def I709N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-337, -210, -21, 79, 468]] i)))

def SI709N0: IdealEqSpanCertificate' Table ![![-337, -210, -21, 79, 468]] 
 ![![709, 0, 0, 0, 0], ![0, 709, 0, 0, 0], ![23, 662, 1, 0, 0], ![529, 703, 0, 1, 0], ![264, 3, 0, 0, 1]] where
  M :=![![![-337, -210, -21, 79, 468], ![-326, -31, -12, 24, 86], ![-1672, -1806, -145, 614, 3790], ![1706, 3393, 177, -1035, -6674], ![-650, -777, -51, 252, 1573]]]
  hmulB := by decide  
  f := ![![![-9609, -6405, -348, 3115, 17264]], ![![-46158, -30847, -1686, 14990, 83082]], ![![-43723, -29219, -1597, 14199, 78698]], ![![-53531, -35761, -1953, 17380, 96328]], ![![-3726, -2484, -135, 1208, 6695]]]
  g := ![![![-233, -61, -21, 79, 468], ![-50, -13, -12, 24, 86], ![-1867, -492, -145, 614, 3790], ![3254, 894, 177, -1035, -6674], ![-773, -210, -51, 252, 1573]]]
  hle1 := by decide   
  hle2 := by decide  


def P709P0 : CertificateIrreducibleZModOfList' 709 2 2 9 [546, 695, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 708], [0, 1]]
 g := ![![[509, 622], [300], [388, 627], [214], [432], [533], [431, 234], [218, 196], [1]], ![[0, 87], [300], [658, 82], [214], [432], [533], [162, 475], [126, 513], [1]]]
 h' := ![![[14, 708], [576, 364], [143, 56], [679, 258], [357, 445], [680, 500], [62, 184], [84, 595], [163, 14], [0, 1]], ![[0, 1], [0, 345], [218, 653], [37, 451], [206, 264], [590, 209], [511, 525], [615, 114], [359, 695], [14, 708]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [204]]
 b := ![[], [704, 102]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI709N0 : CertifiedPrimeIdeal' SI709N0 709 where
  n := 2
  hpos := by decide
  P := [546, 695, 1]
  hirr := P709P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-614718, -571898, -21172, 220966, 1322952]
  a := ![935, 890, 79, -369, -2189]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-657656, -205732, -21172, 220966, 1322952]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI709N0 : Ideal.IsPrime I709N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI709N0 B_one_repr
lemma NI709N0 : Nat.card (O ⧸ I709N0) = 502681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI709N0

def I709N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2043, -1224, -135, 453, 2668]] i)))

def SI709N1: IdealEqSpanCertificate' Table ![![-2043, -1224, -135, 453, 2668]] 
 ![![709, 0, 0, 0, 0], ![0, 709, 0, 0, 0], ![294, 403, 1, 0, 0], ![168, 276, 0, 1, 0], ![39, 415, 0, 0, 1]] where
  M :=![![![-2043, -1224, -135, 453, 2668], ![-2306, -725, -150, 280, 1538], ![-4536, -4602, -461, 1262, 8394], ![12514, 15327, 825, -5613, -34258], ![-4070, -3627, -279, 1306, 7917]]]
  hmulB := by decide  
  f := ![![![-2603, -10233, -1392, 3445, 19248]], ![![-46706, -21749, -5556, 12858, 81494]], ![![-27492, -16391, -3701, 8654, 53820]], ![![-18568, -10965, -2487, 5813, 36178]], ![![-27547, -13295, -3333, 7725, 48827]]]
  g := ![![![-201, -1663, -135, 453, 2668], ![-92, -925, -150, 280, 1538], ![-576, -5149, -461, 1262, 8394], ![2890, 21790, 825, -5613, -34258], ![-635, -4989, -279, 1306, 7917]]]
  hle1 := by decide   
  hle2 := by decide  


def P709P1 : CertificateIrreducibleZModOfList' 709 2 2 9 [344, 706, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 708], [0, 1]]
 g := ![![[608, 423], [565], [265, 26], [500], [246], [558], [568, 413], [90, 9], [1]], ![[459, 286], [565], [343, 683], [500], [246], [558], [389, 296], [117, 700], [1]]]
 h' := ![![[3, 708], [464, 379], [301, 443], [436, 671], [551, 135], [371, 304], [292, 408], [236, 652], [365, 3], [0, 1]], ![[0, 1], [183, 330], [212, 266], [322, 38], [247, 574], [574, 405], [98, 301], [65, 57], [374, 706], [3, 708]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [556]]
 b := ![[], [292, 278]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI709N1 : CertifiedPrimeIdeal' SI709N1 709 where
  n := 2
  hpos := by decide
  P := [344, 706, 1]
  hirr := P709P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3155477, -3387148, -235946, 1286134, 7748968]
  a := ![-1313, -1315, -111, 518, 3074]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-637613, -4907046, -235946, 1286134, 7748968]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI709N1 : Ideal.IsPrime I709N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI709N1 B_one_repr
lemma NI709N1 : Nat.card (O ⧸ I709N1) = 502681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI709N1

def I709N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-189, -177, -14, 61, 376]] i)))

def SI709N2: IdealEqSpanCertificate' Table ![![-189, -177, -14, 61, 376]] 
 ![![709, 0, 0, 0, 0], ![353, 1, 0, 0, 0], ![175, 0, 1, 0, 0], ![221, 0, 0, 1, 0], ![587, 0, 0, 0, 1]] where
  M :=![![![-189, -177, -14, 61, 376], ![158, 457, 22, -138, -914], ![-2132, -3078, -193, 990, 6314], ![5312, 8679, 507, -2745, -17666], ![-1048, -1557, -95, 498, 3185]]]
  hmulB := by decide  
  f := ![![![-125769, -83922, -4571, 40805, 226156]], ![![-63471, -42353, -2307, 20593, 114134]], ![![-35139, -23448, -1278, 11401, 63190]], ![![-46979, -31347, -1708, 15242, 84478]], ![![-103509, -69069, -3762, 33583, 186129]]]
  g := ![![![-239, -177, -14, 61, 376], ![567, 457, 22, -138, -914], ![-3959, -3078, -193, 990, 6314], ![11043, 8679, 507, -2745, -17666], ![-1995, -1557, -95, 498, 3185]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI709N2 : Nat.card (O ⧸ I709N2) = 709 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI709N2)

lemma isPrimeI709N2 : Ideal.IsPrime I709N2 := prime_ideal_of_norm_prime hp709.out _ NI709N2
def MulI709N0 : IdealMulLeCertificate' Table 
  ![![-337, -210, -21, 79, 468]] ![![-2043, -1224, -135, 453, 2668]]
  ![![351853, 174777, 21279, -70182, -399596]] where
 M := ![![![351853, 174777, 21279, -70182, -399596]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI709N1 : IdealMulLeCertificate' Table 
  ![![351853, 174777, 21279, -70182, -399596]] ![![-189, -177, -14, 61, 376]]
  ![![709, 0, 0, 0, 0]] where
 M := ![![![-38282455, -34840260, -2808349, 12060799, 74028108]]]
 hmul := by decide  
 g := ![![![![-53995, -49140, -3961, 17011, 104412]]]]
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

def I719N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-59, -43, -2, 19, 118]] i)))

def SI719N0: IdealEqSpanCertificate' Table ![![-59, -43, -2, 19, 118]] 
 ![![719, 0, 0, 0, 0], ![0, 719, 0, 0, 0], ![0, 0, 719, 0, 0], ![56, 159, 108, 1, 0], ![155, 364, 336, 0, 1]] where
  M :=![![![-59, -43, -2, 19, 118], ![74, 167, 24, -48, -344], ![-1472, -1782, -121, 664, 3944], ![-488, 1587, 45, -233, -1960], ![-8, -325, -5, 68, 481]]]
  hmulB := by decide  
  f := ![![![191, 110, 13, -43, -250]], ![![310, 157, 18, -62, -364]], ![![348, 162, 13, -52, -288]], ![![136, 68, 7, -25, -144]], ![![361, 179, 18, -65, -373]]]
  g := ![![![-27, -64, -58, 19, 118], ![78, 185, 168, -48, -344], ![-904, -2146, -1943, 664, 3944], ![440, 1046, 951, -233, -1960], ![-109, -259, -235, 68, 481]]]
  hle1 := by decide   
  hle2 := by decide  


def P719P0 : CertificateIrreducibleZModOfList' 719 3 2 9 [569, 58, 111, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [139, 412, 125], [469, 306, 594], [0, 1]]
 g := ![![[92, 293, 535], [234, 199, 620], [662, 638, 514], [101, 498, 216], [351, 40], [283, 9], [201, 291, 81], [40, 608, 1], []], ![[418, 3, 66, 617], [365, 407, 92, 26], [446, 111, 346, 338], [118, 351, 678, 321], [115, 20], [194, 427], [680, 634, 250, 501], [419, 571, 75, 618], [36, 526]], ![[65, 531, 489, 424], [315, 192, 671, 153], [286, 448, 59, 635], [29, 393, 164, 430], [533, 42], [275, 105], [342, 221, 7, 398], [408, 446, 229, 409], [286, 526]]]
 h' := ![![[139, 412, 125], [588, 73, 458], [78, 228, 257], [51, 210, 603], [222, 145, 491], [176, 415, 665], [671, 26, 716], [248, 443, 710], [0, 0, 1], [0, 1]], ![[469, 306, 594], [75, 509, 440], [347, 178, 11], [217, 121, 101], [98, 201, 125], [590, 534, 120], [584, 364, 175], [392, 482, 134], [275, 94, 306], [139, 412, 125]], ![[0, 1], [572, 137, 540], [73, 313, 451], [233, 388, 15], [578, 373, 103], [685, 489, 653], [83, 329, 547], [704, 513, 594], [426, 625, 412], [469, 306, 594]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [530, 349], []]
 b := ![[], [184, 408, 118], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI719N0 : CertifiedPrimeIdeal' SI719N0 719 where
  n := 3
  hpos := by decide
  P := [569, 58, 111, 1]
  hirr := P719P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2441985, 2308410, 109681, -922781, -5398442]
  a := ![129, 120, 11, -51, -302]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1239049, 2940283, 2661539, -922781, -5398442]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI719N0 : Ideal.IsPrime I719N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI719N0 B_one_repr
lemma NI719N0 : Nat.card (O ⧸ I719N0) = 371694959 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI719N0

def I719N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 110, 13, -43, -250]] i)))

def SI719N1: IdealEqSpanCertificate' Table ![![191, 110, 13, -43, -250]] 
 ![![719, 0, 0, 0, 0], ![0, 719, 0, 0, 0], ![595, 504, 1, 0, 0], ![393, 660, 0, 1, 0], ![92, 637, 0, 0, 1]] where
  M :=![![![191, 110, 13, -43, -250], ![310, 157, 18, -62, -364], ![348, 162, 13, -52, -288], ![214, 273, 39, -93, -556], ![186, 71, 7, -30, -173]]]
  hmulB := by decide  
  f := ![![![-59, -43, -2, 19, 118]], ![![74, 167, 24, -48, -344]], ![![1, 79, 15, -17, -138]], ![![35, 132, 21, -34, -254]], ![![58, 142, 21, -40, -289]]]
  g := ![![![45, 252, 13, -43, -250], ![66, 367, 18, -62, -364], ![55, 294, 13, -52, -288], ![90, 551, 39, -93, -556], ![33, 176, 7, -30, -173]]]
  hle1 := by decide   
  hle2 := by decide  


def P719P1 : CertificateIrreducibleZModOfList' 719 2 2 9 [324, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [691, 718], [0, 1]]
 g := ![![[222, 162], [252, 9], [666, 486], [429, 454], [441], [397], [618, 25], [506, 65], [1]], ![[0, 557], [0, 710], [0, 233], [659, 265], [441], [397], [637, 694], [124, 654], [1]]]
 h' := ![![[691, 718], [318, 679], [635, 716], [490, 377], [649, 620], [343, 21], [369, 624], [707, 5], [395, 691], [0, 1]], ![[0, 1], [0, 40], [0, 3], [0, 342], [545, 99], [474, 698], [153, 95], [567, 714], [460, 28], [691, 718]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [455]]
 b := ![[], [309, 587]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI719N1 : CertifiedPrimeIdeal' SI719N1 719 where
  n := 2
  hpos := by decide
  P := [324, 28, 1]
  hirr := P719P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2900443, -2666700, -169115, 1079494, 6426108]
  a := ![-1401, -1316, -119, 552, 3280]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1276384, -6569304, -169115, 1079494, 6426108]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI719N1 : Ideal.IsPrime I719N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI719N1 B_one_repr
lemma NI719N1 : Nat.card (O ⧸ I719N1) = 516961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI719N1
def MulI719N0 : IdealMulLeCertificate' Table 
  ![![-59, -43, -2, 19, 118]] ![![191, 110, 13, -43, -250]]
  ![![719, 0, 0, 0, 0]] where
 M := ![![![719, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I727N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1335, 1689, 285, -688, -4052]] i)))

def SI727N0: IdealEqSpanCertificate' Table ![![1335, 1689, 285, -688, -4052]] 
 ![![727, 0, 0, 0, 0], ![0, 727, 0, 0, 0], ![370, 523, 1, 0, 0], ![478, 562, 0, 1, 0], ![263, 725, 0, 0, 1]] where
  M :=![![![1335, 1689, 285, -688, -4052], ![3504, -665, 138, -266, -2340], ![-20300, -18924, -3557, 8460, 50912], ![3818, 26820, 3456, -8623, -47468], ![942, -4530, -486, 1246, 6475]]]
  hmulB := by decide  
  f := ![![![13177, 20685, 1227, -6610, -42384]], ![![-63052, -102755, -6090, 32418, 208948]], ![![-38186, -62657, -3713, 19722, 127236]], ![![-41444, -68042, -4032, 21413, 138156]], ![![-57877, -94612, -5607, 29818, 192271]]]
  g := ![![![1775, 4370, 285, -688, -4052], ![956, 2439, 138, -266, -2340], ![-22198, -54779, -3557, 8460, 50912], ![21088, 51554, 3456, -8623, -47468], ![-2913, -7077, -486, 1246, 6475]]]
  hle1 := by decide   
  hle2 := by decide  


def P727P0 : CertificateIrreducibleZModOfList' 727 2 2 9 [349, 343, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [384, 726], [0, 1]]
 g := ![![[578, 25], [18, 602], [510, 578], [498], [678, 390], [512], [427, 717], [213, 602], [1]], ![[0, 702], [0, 125], [0, 149], [498], [676, 337], [512], [222, 10], [195, 125], [1]]]
 h' := ![![[384, 726], [261, 5], [125, 384], [405, 459], [380, 35], [298, 128], [12, 295], [544, 38], [378, 384], [0, 1]], ![[0, 1], [0, 722], [0, 343], [0, 268], [7, 692], [14, 599], [607, 432], [596, 689], [253, 343], [384, 726]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [586]]
 b := ![[], [450, 293]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI727N0 : CertifiedPrimeIdeal' SI727N0 727 where
  n := 2
  hpos := by decide
  P := [349, 343, 1]
  hirr := P727P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3244379, -3130509, -186678, 1230043, 7377666]
  a := ![1656, 1578, 142, -652, -3877]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3387153, -8178253, -186678, 1230043, 7377666]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI727N0 : Ideal.IsPrime I727N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI727N0 B_one_repr
lemma NI727N0 : Nat.card (O ⧸ I727N0) = 528529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI727N0

def I727N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12385, 11525, 2164, -5151, -30996]] i)))

def SI727N1: IdealEqSpanCertificate' Table ![![12385, 11525, 2164, -5151, -30996]] 
 ![![727, 0, 0, 0, 0], ![0, 727, 0, 0, 0], ![58, 6, 1, 0, 0], ![524, 8, 0, 1, 0], ![195, 460, 0, 0, 1]] where
  M :=![![![12385, 11525, 2164, -5151, -30996], ![7782, -21041, -2034, 5318, 26634], ![-158308, -107982, -22943, 53946, 332086], ![142948, 254415, 39543, -96171, -555670], ![-19228, -49489, -7151, 17554, 99635]]]
  hmulB := by decide  
  f := ![![![19731, 29014, 1775, -9353, -59696]], ![![-81478, -136571, -8004, 42908, 277138]], ![![1542, 2188, 135, -712, -4526]], ![![11490, 16435, 1015, -5329, -33922]], ![![-45943, -78121, -4558, 24479, 158303]]]
  g := ![![![11871, 19667, 2164, -5151, -30996], ![-10804, -16923, -2034, 5318, 26634], ![-126344, -210676, -22943, 53946, 332086], ![215404, 352675, 39543, -96171, -555670], ![-38833, -63245, -7151, 17554, 99635]]]
  hle1 := by decide   
  hle2 := by decide  


def P727P1 : CertificateIrreducibleZModOfList' 727 2 2 9 [488, 133, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [594, 726], [0, 1]]
 g := ![![[258, 73], [463, 162], [555, 436], [131], [475, 524], [346], [107, 544], [337, 241], [1]], ![[0, 654], [0, 565], [0, 291], [131], [575, 203], [346], [455, 183], [272, 486], [1]]]
 h' := ![![[594, 726], [153, 187], [331, 243], [458, 479], [113, 536], [206, 345], [128, 644], [573, 107], [239, 594], [0, 1]], ![[0, 1], [0, 540], [0, 484], [0, 248], [71, 191], [122, 382], [262, 83], [155, 620], [480, 133], [594, 726]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [529]]
 b := ![[], [323, 628]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI727N1 : CertifiedPrimeIdeal' SI727N1 727 where
  n := 2
  hpos := by decide
  P := [488, 133, 1]
  hirr := P727P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-70782, -101682, -5700, 32754, 212930]
  a := ![-170, -162, -16, 62, 398]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-80364, -135182, -5700, 32754, 212930]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI727N1 : Ideal.IsPrime I727N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI727N1 B_one_repr
lemma NI727N1 : Nat.card (O ⧸ I727N1) = 528529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI727N1

def I727N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-445, -296, -16, 144, 798]] i)))

def SI727N2: IdealEqSpanCertificate' Table ![![-445, -296, -16, 144, 798]] 
 ![![727, 0, 0, 0, 0], ![198, 1, 0, 0, 0], ![54, 0, 1, 0, 0], ![443, 0, 0, 1, 0], ![66, 0, 0, 0, 1]] where
  M :=![![![-445, -296, -16, 144, 798], ![-2136, -1429, -78, 694, 3846], ![-10292, -6876, -379, 3342, 18530], ![-19504, -12990, -708, 6321, 35038], ![1552, 1030, 56, -502, -2783]]]
  hmulB := by decide  
  f := ![![![-2883, -2548, -200, 884, 5450]], ![![-782, -685, -54, 238, 1466]], ![![-258, -252, -19, 86, 534]], ![![-1655, -1382, -112, 485, 2976]], ![![-282, -262, -20, 90, 557]]]
  g := ![![![-79, -296, -16, 144, 798], ![-380, -1429, -78, 694, 3846], ![-1832, -6876, -379, 3342, 18530], ![-3469, -12990, -708, 6321, 35038], ![276, 1030, 56, -502, -2783]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI727N2 : Nat.card (O ⧸ I727N2) = 727 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI727N2)

lemma isPrimeI727N2 : Ideal.IsPrime I727N2 := prime_ideal_of_norm_prime hp727.out _ NI727N2
def MulI727N0 : IdealMulLeCertificate' Table 
  ![![1335, 1689, 285, -688, -4052]] ![![12385, 11525, 2164, -5151, -30996]]
  ![![-35876375, -25435336, -5314973, 12516967, 76829616]] where
 M := ![![![-35876375, -25435336, -5314973, 12516967, 76829616]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI727N1 : IdealMulLeCertificate' Table 
  ![![-35876375, -25435336, -5314973, 12516967, 76829616]] ![![-445, -296, -16, 144, 798]]
  ![![727, 0, 0, 0, 0]] where
 M := ![![![105206351, 51359642, 12798835, -29679775, -187430778]]]
 hmul := by decide  
 g := ![![![![144713, 70646, 17605, -40825, -257814]]]]
 hle2 := by decide  


def PBC727 : ContainsPrimesAboveP 727 ![I727N0, I727N1, I727N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI727N0
    exact isPrimeI727N1
    exact isPrimeI727N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 727 (by decide) (𝕀 ⊙ MulI727N0 ⊙ MulI727N1)
instance hp733 : Fact (Nat.Prime 733) := {out := by norm_num}

def I733N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35303, -19818, -2206, 7680, 44500]] i)))

def SI733N0: IdealEqSpanCertificate' Table ![![-35303, -19818, -2206, 7680, 44500]] 
 ![![733, 0, 0, 0, 0], ![0, 733, 0, 0, 0], ![147, 240, 1, 0, 0], ![245, 107, 0, 1, 0], ![6, 113, 0, 0, 1]] where
  M :=![![![-35303, -19818, -2206, 7680, 44500], ![-59600, -33463, -3724, 12968, 75140], ![-100640, -56496, -6287, 21900, 126884], ![-34804, -19596, -2172, 7601, 44044], ![-37508, -21048, -2344, 8156, 47257]]]
  hmulB := by decide  
  f := ![![![533, 642, 110, -264, -1572]], ![![864, -715, -4, 88, 252]], ![![379, -114, 19, -20, -208]], ![![305, 121, 38, -79, -508]], ![![138, -107, 0, 12, 29]]]
  g := ![![![-2537, -7286, -2206, 7680, 44500], ![-4284, -12303, -3724, 12968, 75140], ![-7235, -20776, -6287, 21900, 126884], ![-2513, -7215, -2172, 7601, 44044], ![-2694, -7737, -2344, 8156, 47257]]]
  hle1 := by decide   
  hle2 := by decide  


def P733P0 : CertificateIrreducibleZModOfList' 733 2 2 9 [633, 627, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 732], [0, 1]]
 g := ![![[133, 711], [4], [342, 708], [417, 127], [458, 389], [572], [551, 682], [567, 241], [1]], ![[0, 22], [4], [624, 25], [685, 606], [644, 344], [572], [276, 51], [458, 492], [1]]]
 h' := ![![[106, 732], [363, 695], [482, 731], [652, 434], [354, 82], [258, 296], [125, 175], [259, 378], [100, 106], [0, 1]], ![[0, 1], [0, 38], [270, 2], [477, 299], [250, 651], [115, 437], [350, 558], [12, 355], [341, 627], [106, 732]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [255]]
 b := ![[], [206, 494]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI733N0 : CertifiedPrimeIdeal' SI733N0 733 where
  n := 2
  hpos := by decide
  P := [633, 627, 1]
  hirr := P733P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12916995, -11917550, -805774, 4864026, 28800250]
  a := ![-2743, -2614, -230, 1086, 6422]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1717539, -4902334, -805774, 4864026, 28800250]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI733N0 : Ideal.IsPrime I733N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI733N0 B_one_repr
lemma NI733N0 : Nat.card (O ⧸ I733N0) = 537289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI733N0

def I733N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6759, -7178, -550, 2358, 14800]] i)))

def SI733N1: IdealEqSpanCertificate' Table ![![-6759, -7178, -550, 2358, 14800]] 
 ![![733, 0, 0, 0, 0], ![0, 733, 0, 0, 0], ![726, 564, 1, 0, 0], ![145, 94, 0, 1, 0], ![325, 110, 0, 0, 1]] where
  M :=![![![-6759, -7178, -550, 2358, 14800], ![13540, 25645, 1302, -8272, -53116], ![-81008, -133644, -8321, 40928, 266516], ![292848, 442374, 25992, -143999, -916872], ![-51988, -76178, -4636, 24654, 157139]]]
  hmulB := by decide  
  f := ![![![-200563, -41194, -17594, 39426, 264848]], ![![713324, 828169, 144366, -346400, -2053268]], ![![352118, 595524, 93667, -227468, -1317956]], ![![43729, 92406, 13846, -33829, -193752]], ![![19825, 107406, 14138, -35152, -194645]]]
  g := ![![![-6493, -2110, -550, 2358, 14800], ![23916, 8065, 1302, -8272, -53116], ![-118134, -39024, -8321, 40928, 266516], ![409667, 136664, 25992, -143999, -916872], ![-70029, -23280, -4636, 24654, 157139]]]
  hle1 := by decide   
  hle2 := by decide  


def P733P1 : CertificateIrreducibleZModOfList' 733 2 2 9 [54, 453, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [280, 732], [0, 1]]
 g := ![![[212, 270], [9], [638, 560], [286, 636], [546, 513], [595], [34, 347], [662, 702], [1]], ![[313, 463], [9], [576, 173], [247, 97], [518, 220], [595], [438, 386], [45, 31], [1]]]
 h' := ![![[280, 732], [248, 315], [732, 3], [682, 65], [569, 37], [684, 413], [363, 285], [169, 103], [679, 280], [0, 1]], ![[0, 1], [488, 418], [106, 730], [557, 668], [667, 696], [510, 320], [266, 448], [422, 630], [648, 453], [280, 732]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [368]]
 b := ![[], [628, 184]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI733N1 : CertifiedPrimeIdeal' SI733N1 733 where
  n := 2
  hpos := by decide
  P := [54, 453, 1]
  hirr := P733P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-80562, -83790, -6598, 32132, 195670]
  a := ![-129, -126, -11, 50, 302]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-86688, -28522, -6598, 32132, 195670]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI733N1 : Ideal.IsPrime I733N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI733N1 B_one_repr
lemma NI733N1 : Nat.card (O ⧸ I733N1) = 537289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI733N1

def I733N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![143, 92, 3, -45, -246]] i)))

def SI733N2: IdealEqSpanCertificate' Table ![![143, 92, 3, -45, -246]] 
 ![![733, 0, 0, 0, 0], ![662, 1, 0, 0, 0], ![90, 0, 1, 0, 0], ![218, 0, 0, 1, 0], ![533, 0, 0, 0, 1]] where
  M :=![![![143, 92, 3, -45, -246], ![762, 545, 32, -258, -1428], ![3876, 2574, 163, -1256, -7008], ![6710, 4275, 195, -2113, -11672], ![-514, -295, -9, 152, 837]]]
  hmulB := by decide  
  f := ![![![47323, 74665, 4456, -23745, -152522]], ![![42420, 66919, 3994, -21282, -136700]], ![![7454, 11796, 703, -3750, -24092]], ![![9078, 14201, 851, -4521, -29024]], ![![35263, 55656, 3321, -17699, -113689]]]
  g := ![![![109, 92, 3, -45, -246], ![620, 545, 32, -258, -1428], ![3130, 2574, 163, -1256, -7008], ![5240, 4275, 195, -2113, -11672], ![-387, -295, -9, 152, 837]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI733N2 : Nat.card (O ⧸ I733N2) = 733 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI733N2)

lemma isPrimeI733N2 : Ideal.IsPrime I733N2 := prime_ideal_of_norm_prime hp733.out _ NI733N2
def MulI733N0 : IdealMulLeCertificate' Table 
  ![![-35303, -19818, -2206, 7680, 44500]] ![![-6759, -7178, -550, 2358, 14800]]
  ![![84587545, 47502308, 5286300, -18406466, -106657268]] where
 M := ![![![84587545, 47502308, 5286300, -18406466, -106657268]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI733N1 : IdealMulLeCertificate' Table 
  ![![84587545, 47502308, 5286300, -18406466, -106657268]] ![![143, 92, 3, -45, -246]]
  ![![733, 0, 0, 0, 0]] where
 M := ![![![96925323, 54000110, 6157933, -20669867, -120084458]]]
 hmul := by decide  
 g := ![![![![132231, 73670, 8401, -28199, -163826]]]]
 hle2 := by decide  


def PBC733 : ContainsPrimesAboveP 733 ![I733N0, I733N1, I733N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI733N0
    exact isPrimeI733N1
    exact isPrimeI733N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 733 (by decide) (𝕀 ⊙ MulI733N0 ⊙ MulI733N1)
instance hp739 : Fact (Nat.Prime 739) := {out := by norm_num}

def I739N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12689, -20321, -1204, 6451, 41476]] i)))

def SI739N0: IdealEqSpanCertificate' Table ![![-12689, -20321, -1204, 6451, 41476]] 
 ![![739, 0, 0, 0, 0], ![0, 739, 0, 0, 0], ![586, 29, 1, 0, 0], ![78, 597, 0, 1, 0], ![656, 356, 0, 0, 1]] where
  M :=![![![-12689, -20321, -1204, 6451, 41476], ![64658, 103577, 6138, -32878, -211394], ![-329772, -528138, -31297, 167662, 1077954], ![1004972, 1609917, 95397, -511029, -3285698], ![-171060, -274019, -16237, 86982, 559253]]]
  hmulB := by decide  
  f := ![![![-18167, -10090, -1115, 3913, 22672]], ![![-30394, -17257, -1884, 6636, 38350]], ![![-15672, -8721, -963, 3380, 19580]], ![![-26498, -15018, -1641, 5779, 33404]], ![![-30794, -17285, -1899, 6676, 38633]]]
  g := ![![![-36561, -25172, -1204, 6451, 41476], ![186342, 128295, 6138, -32878, -211394], ![-950210, -654217, -31297, 167662, 1077954], ![2896320, 1994095, 95397, -511029, -3285698], ![-492978, -339412, -16237, 86982, 559253]]]
  hle1 := by decide   
  hle2 := by decide  


def P739P0 : CertificateIrreducibleZModOfList' 739 2 2 9 [348, 594, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [145, 738], [0, 1]]
 g := ![![[677, 189], [170, 562], [506], [36], [664], [715, 357], [229, 215], [573, 333], [1]], ![[0, 550], [370, 177], [506], [36], [664], [11, 382], [366, 524], [84, 406], [1]]]
 h' := ![![[145, 738], [699, 408], [714, 444], [211, 286], [451, 6], [223, 490], [120, 126], [126, 364], [391, 145], [0, 1]], ![[0, 1], [0, 331], [62, 295], [297, 453], [582, 733], [329, 249], [654, 613], [437, 375], [724, 594], [145, 738]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [194]]
 b := ![[], [727, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI739N0 : CertifiedPrimeIdeal' SI739N0 739 where
  n := 2
  hpos := by decide
  P := [348, 594, 1]
  hirr := P739P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5437652, -5262843, -353537, 2092859, 12518681]
  a := ![-1738, -1656, -145, 684, 4069]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11060572, -7714611, -353537, 2092859, 12518681]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI739N0 : Ideal.IsPrime I739N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI739N0 B_one_repr
lemma NI739N0 : Nat.card (O ⧸ I739N0) = 546121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI739N0

def I739N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![48475, 77644, 4601, -24647, -158468]] i)))

def SI739N1: IdealEqSpanCertificate' Table ![![48475, 77644, 4601, -24647, -158468]] 
 ![![739, 0, 0, 0, 0], ![0, 739, 0, 0, 0], ![358, 682, 1, 0, 0], ![417, 61, 0, 1, 0], ![123, 582, 0, 0, 1]] where
  M :=![![![48475, 77644, 4601, -24647, -158468], ![-247114, -395815, -23454, 125648, 807850], ![1259640, 2017710, 119561, -640490, -4118046], ![-3840814, -6151989, -364539, 1952889, 12556054], ![653706, 1047073, 62045, -332382, -2137045]]]
  hmulB := by decide  
  f := ![![![-119, 1007, 82, -245, -1208]], ![![7826, 5747, 1140, -2718, -16574]], ![![7162, 5770, 1089, -2620, -15842]], ![![525, 1025, 135, -350, -1968]], ![![6157, 4700, 913, -2185, -13277]]]
  g := ![![![38120, 122695, 4601, -24647, -158468], ![-194332, -625485, -23454, 125648, 807850], ![990610, 3188430, 119561, -640490, -4118046], ![-3020413, -9721632, -364539, 1952889, 12556054], ![514075, 1654625, 62045, -332382, -2137045]]]
  hle1 := by decide   
  hle2 := by decide  


def P739P1 : CertificateIrreducibleZModOfList' 739 2 2 9 [732, 538, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [201, 738], [0, 1]]
 g := ![![[451, 211], [251, 367], [569], [497], [157], [545, 286], [450, 373], [327, 495], [1]], ![[0, 528], [118, 372], [569], [497], [157], [389, 453], [45, 366], [57, 244], [1]]]
 h' := ![![[201, 738], [279, 142], [150, 356], [184, 138], [719, 628], [120, 644], [194, 697], [72, 514], [7, 201], [0, 1]], ![[0, 1], [0, 597], [23, 383], [579, 601], [578, 111], [239, 95], [620, 42], [665, 225], [502, 538], [201, 738]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [479]]
 b := ![[], [502, 609]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI739N1 : CertifiedPrimeIdeal' SI739N1 739 where
  n := 2
  hpos := by decide
  P := [732, 538, 1]
  hirr := P739P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2142137, -2043528, -145377, 821662, 4905532]
  a := ![-1061, -1010, -91, 418, 2484]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1212599, -3799780, -145377, 821662, 4905532]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI739N1 : Ideal.IsPrime I739N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI739N1 B_one_repr
lemma NI739N1 : Nat.card (O ⧸ I739N1) = 546121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI739N1

def I739N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, -17, -1, 2, 4]] i)))

def SI739N2: IdealEqSpanCertificate' Table ![![31, -17, -1, 2, 4]] 
 ![![739, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![694, 0, 1, 0, 0], ![283, 0, 0, 1, 0], ![713, 0, 0, 0, 1]] where
  M :=![![![31, -17, -1, 2, 4], ![-228, -181, -36, 86, 528], ![164, 624, 77, -204, -1148], ![1186, 222, 120, -239, -1564], ![-278, -104, -34, 72, 457]]]
  hmulB := by decide  
  f := ![![![-256907, -171505, -9371, 83400, 462280]], ![![-11404, -7613, -416, 3702, 20520]], ![![-249282, -166414, -9093, 80924, 448556]], ![![-113625, -75853, -4145, 36885, 204452]], ![![-246655, -164661, -8997, 80072, 443833]]]
  g := ![![![-3, -17, -1, 2, 4], ![-502, -181, -36, 86, 528], ![1090, 624, 77, -204, -1148], ![1481, 222, 120, -239, -1564], ![-433, -104, -34, 72, 457]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI739N2 : Nat.card (O ⧸ I739N2) = 739 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI739N2)

lemma isPrimeI739N2 : Ideal.IsPrime I739N2 := prime_ideal_of_norm_prime hp739.out _ NI739N2
def MulI739N0 : IdealMulLeCertificate' Table 
  ![![-12689, -20321, -1204, 6451, 41476]] ![![48475, 77644, 4601, -24647, -158468]]
  ![![5225916701, 8370727768, 496012532, -2657186158, -17084366080]] where
 M := ![![![5225916701, 8370727768, 496012532, -2657186158, -17084366080]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI739N1 : IdealMulLeCertificate' Table 
  ![![5225916701, 8370727768, 496012532, -2657186158, -17084366080]] ![![31, -17, -1, 2, 4]]
  ![![739, 0, 0, 0, 0]] where
 M := ![![![-67145471273, -107551744713, -6373043625, 34140998924, 219509394124]]]
 hmul := by decide  
 g := ![![![![-90859907, -145536867, -8623875, 46198916, 297035716]]]]
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

def I743N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7541, 4232, 467, -1635, -9466]] i)))

def SI743N0: IdealEqSpanCertificate' Table ![![7541, 4232, 467, -1635, -9466]] 
 ![![743, 0, 0, 0, 0], ![0, 743, 0, 0, 0], ![0, 0, 743, 0, 0], ![618, 223, 366, 1, 0], ![239, 17, 720, 0, 1]] where
  M :=![![![7541, 4232, 467, -1635, -9466], ![12902, 7363, 826, -2850, -16508], ![22276, 12378, 1415, -4860, -28264], ![6266, 2913, 243, -1083, -6164], ![8302, 4811, 551, -1870, -10851]]]
  hmulB := by decide  
  f := ![![![131, 101, 6, -45, -258]], ![![426, 197, 8, -120, -624]], ![![2928, 2394, 133, -1040, -5952]], ![![1684, 1324, 73, -587, -3340]], ![![2889, 2357, 131, -1025, -5865]]]
  g := ![![![4415, 713, 9979, -1635, -9466], ![7698, 1243, 17402, -2850, -16508], ![13164, 2122, 29785, -4860, -28264], ![2892, 470, 6507, -1083, -6164], ![5057, 816, 11437, -1870, -10851]]]
  hle1 := by decide   
  hle2 := by decide  


def P743P0 : CertificateIrreducibleZModOfList' 743 3 2 9 [619, 520, 97, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [287, 659, 507], [359, 83, 236], [0, 1]]
 g := ![![[236, 158, 328], [353, 477, 172], [610, 617, 564], [268, 698], [362, 600], [683], [473, 593, 636], [716, 646, 1], []], ![[135, 526, 113, 458], [337, 480, 681, 730], [435, 698, 200, 132], [337, 199], [654, 680], [613, 37, 483, 239], [306, 117, 543, 648], [486, 107, 692, 623], [110, 714]], ![[398, 333, 379, 689], [337, 566, 92, 347], [432, 666, 453, 193], [309, 363], [508, 486], [693, 656, 241, 504], [5, 735, 326, 311], [460, 33, 679, 153], [381, 714]]]
 h' := ![![[287, 659, 507], [678, 181, 232], [597, 304, 49], [572, 564, 163], [408, 324, 442], [733, 533, 133], [698, 154], [367, 526, 430], [0, 0, 1], [0, 1]], ![[359, 83, 236], [306, 592, 316], [679, 308, 679], [124, 65, 48], [54, 521, 344], [645, 114, 416], [316, 438, 63], [318, 363, 714], [162, 209, 83], [287, 659, 507]], ![[0, 1], [731, 713, 195], [692, 131, 15], [550, 114, 532], [241, 641, 700], [450, 96, 194], [259, 151, 680], [239, 597, 342], [34, 534, 659], [359, 83, 236]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [211, 21], []]
 b := ![[], [130, 240, 444], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI743N0 : CertifiedPrimeIdeal' SI743N0 743 where
  n := 3
  hpos := by decide
  P := [619, 520, 97, 1]
  hirr := P743P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3292188597, -3161187495, -183292071, 1255161688, 7449532618]
  a := ![-1099, -1047, -93, 435, 2573]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3444711181, -551418975, -7837464273, 1255161688, 7449532618]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI743N0 : Ideal.IsPrime I743N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI743N0 B_one_repr
lemma NI743N0 : Nat.card (O ⧸ I743N0) = 410172407 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI743N0

def I743N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-131, -101, -6, 45, 258]] i)))

def SI743N1: IdealEqSpanCertificate' Table ![![-131, -101, -6, 45, 258]] 
 ![![743, 0, 0, 0, 0], ![0, 743, 0, 0, 0], ![426, 12, 1, 0, 0], ![203, 135, 0, 1, 0], ![573, 368, 0, 0, 1]] where
  M :=![![![-131, -101, -6, 45, 258], ![-426, -197, -8, 120, 624], ![-2928, -2394, -133, 1040, 5952], ![-3608, -1179, -69, 931, 4592], ![184, -83, -3, -20, -15]]]
  hmulB := by decide  
  f := ![![![-7541, -4232, -467, 1635, 9466]], ![![-12902, -7363, -826, 2850, 16508]], ![![-4562, -2562, -283, 990, 5732]], ![![-4413, -2498, -278, 966, 5594]], ![![-12217, -6917, -770, 2675, 15491]]]
  g := ![![![-208, -136, -6, 45, 258], ![-510, -331, -8, 120, 624], ![-4802, -3138, -133, 1040, 5952], ![-3761, -2444, -69, 931, 4592], ![19, 11, -3, -20, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P743P1 : CertificateIrreducibleZModOfList' 743 2 2 9 [675, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [725, 742], [0, 1]]
 g := ![![[109, 295], [56, 630], [716, 229], [127], [2], [11, 582], [282, 738], [636, 324], [1]], ![[0, 448], [604, 113], [309, 514], [127], [2], [680, 161], [372, 5], [5, 419], [1]]]
 h' := ![![[725, 742], [93, 129], [393, 697], [379, 273], [161, 241], [5, 102], [601, 468], [154, 348], [68, 725], [0, 1]], ![[0, 1], [0, 614], [478, 46], [666, 470], [281, 502], [398, 641], [350, 275], [577, 395], [392, 18], [725, 742]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [369]]
 b := ![[], [546, 556]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI743N1 : CertifiedPrimeIdeal' SI743N1 743 where
  n := 2
  hpos := by decide
  P := [675, 18, 1]
  hirr := P743P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5281173, -5282015, -316708, 2050847, 12315079]
  a := ![1838, 1754, 146, -722, -4303]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9883211, -6474152, -316708, 2050847, 12315079]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI743N1 : Ideal.IsPrime I743N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI743N1 B_one_repr
lemma NI743N1 : Nat.card (O ⧸ I743N1) = 552049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI743N1
def MulI743N0 : IdealMulLeCertificate' Table 
  ![![7541, 4232, 467, -1635, -9466]] ![![-131, -101, -6, 45, 258]]
  ![![743, 0, 0, 0, 0]] where
 M := ![![![-743, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC743 : ContainsPrimesAboveP 743 ![I743N0, I743N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI743N0
    exact isPrimeI743N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 743 (by decide) (𝕀 ⊙ MulI743N0)
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


def P751P0 : CertificateIrreducibleZModOfList' 751 5 2 9 [95, 440, 744, 276, 349, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [91, 319, 402, 372, 274], [371, 686, 445, 250, 308], [604, 502, 629, 719, 349], [87, 745, 26, 161, 571], [0, 1]]
 g := ![![[86, 733, 478, 134, 520], [408, 738, 435, 309, 298], [707, 460, 749, 145, 360], [411, 556, 516, 227, 483], [393, 399, 567, 336], [352, 656, 309, 417, 494], [739, 727, 302, 696, 139], [1], []], ![[393, 125, 617, 34, 386, 568, 373, 88], [249, 405, 283, 707, 511, 393, 558, 243], [556, 406, 442, 37, 297, 565, 235, 447], [597, 84, 138, 345, 546, 154, 724, 363], [492, 111, 40, 712], [644, 619, 245, 326, 549, 14, 532, 322], [457, 20, 396, 433, 131, 675, 77, 571], [363, 181, 142, 292, 148, 455, 703, 560], [700, 227, 450, 727]], ![[410, 430, 546, 211, 357, 462, 10, 334], [416, 705, 569, 688, 568, 529, 404, 218], [588, 53, 72, 340, 78, 168, 258, 106], [542, 504, 137, 683, 351, 35, 0, 25], [740, 697, 511, 168], [393, 593, 520, 228, 682, 389, 647, 288], [35, 630, 108, 568, 683, 165, 136, 423], [37, 289, 324, 24, 353, 710, 74, 688], [454, 676, 344, 238]], ![[91, 288, 114, 150, 251, 346, 285, 157], [27, 393, 552, 633, 521, 433, 161, 603], [300, 117, 52, 350, 460, 371, 287, 359], [557, 414, 12, 541, 515, 569, 385, 27], [407, 726, 20, 416], [236, 187, 300, 632, 413, 398, 301, 268], [153, 493, 685, 348, 108, 131, 363, 228], [404, 707, 706, 339, 249, 281, 528, 228], [743, 347, 498, 139]], ![[341, 138, 228, 712, 230, 568, 210, 561], [225, 380, 313, 300, 531, 160, 97, 743], [416, 665, 497, 379, 230, 308, 659, 248], [291, 518, 639, 466, 180, 741, 20, 240], [457, 528, 38, 254], [389, 77, 244, 276, 565, 353, 323, 96], [90, 624, 290, 133, 424, 109, 489, 259], [367, 588, 506, 406, 16, 240, 479, 371], [243, 255, 74, 107]]]
 h' := ![![[91, 319, 402, 372, 274], [292, 87, 188, 72, 166], [425, 492, 97, 111, 365], [7, 579, 186, 204, 693], [72, 649, 398, 139, 283], [355, 209, 88, 7, 531], [389, 63, 49, 169, 358], [656, 311, 7, 475, 402], [0, 0, 1], [0, 1]], ![[371, 686, 445, 250, 308], [628, 160, 739, 264, 701], [27, 316, 406, 711, 544], [229, 653, 541, 143, 690], [66, 3, 409, 538, 498], [383, 716, 722, 165, 257], [410, 372, 418, 172, 655], [616, 220, 497, 71, 670], [359, 355, 396, 684, 109], [91, 319, 402, 372, 274]], ![[604, 502, 629, 719, 349], [698, 347, 581, 561, 209], [276, 382, 386, 46, 519], [207, 536, 666, 39, 315], [378, 240, 484, 686, 484], [110, 263, 50, 256, 337], [240, 670, 47, 123, 14], [432, 19, 716, 458, 378], [636, 206, 714, 581, 48], [371, 686, 445, 250, 308]], ![[87, 745, 26, 161, 571], [146, 634, 146, 369, 34], [651, 20, 552, 420, 307], [705, 647, 284, 305, 256], [602, 165, 73, 107, 641], [314, 351, 683, 239, 618], [410, 37, 499, 233, 455], [108, 174, 472, 671, 144], [590, 203, 710, 186, 607], [604, 502, 629, 719, 349]], ![[0, 1], [715, 274, 599, 236, 392], [743, 292, 61, 214, 518], [662, 589, 576, 60, 299], [463, 445, 138, 32, 347], [364, 714, 710, 84, 510], [463, 360, 489, 54, 20], [324, 27, 561, 578, 659], [255, 738, 432, 51, 738], [87, 745, 26, 161, 571]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [394, 673, 153, 703], [], [], []]
 b := ![[], [513, 312, 737, 303, 203], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI751N0 : CertifiedPrimeIdeal' SI751N0 751 where
  n := 5
  hpos := by decide
  P := [95, 440, 744, 276, 349, 1]
  hirr := P751P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13568624153889445, 15966934547896596, 926760770962337, -5764083518306557, -35281384612611706]
  a := ![1149, 1098, 95, -453, -2690]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![18067408993195, 21260898199596, 1234035647087, -7675211076307, -46979207207206]
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

def I757N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![757, 0, 0, 0, 0]] i)))

def SI757N0: IdealEqSpanCertificate' Table ![![757, 0, 0, 0, 0]] 
 ![![757, 0, 0, 0, 0], ![0, 757, 0, 0, 0], ![0, 0, 757, 0, 0], ![0, 0, 0, 757, 0], ![0, 0, 0, 0, 757]] where
  M :=![![![757, 0, 0, 0, 0], ![0, 757, 0, 0, 0], ![0, 0, 757, 0, 0], ![0, 0, 0, 757, 0], ![0, 0, 0, 0, 757]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P757P0 : CertificateIrreducibleZModOfList' 757 5 2 9 [117, 661, 694, 338, 692, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [441, 59, 449, 501, 109], [307, 634, 465, 423, 174], [489, 414, 480, 42, 154], [342, 406, 120, 548, 320], [0, 1]]
 g := ![![[695, 183, 375, 481, 270], [153, 295, 246, 176], [572, 531, 312, 282, 9], [633, 710, 483, 120], [39, 93, 257, 508, 465], [562, 676, 661, 224, 275], [403, 638, 78, 557, 440], [1], []], ![[125, 275, 401, 608, 504, 422, 642, 276], [36, 486, 591, 699], [543, 615, 19, 341, 193, 484, 43, 383], [477, 136, 49, 51], [285, 483, 286, 535, 15, 721, 691, 264], [78, 195, 232, 415, 746, 134, 714, 488], [679, 487, 436, 596, 78, 431, 63, 502], [438, 561, 733, 14, 328, 529, 561, 88], [256, 592, 335, 526]], ![[152, 45, 595, 675, 380, 241, 520, 51], [92, 317, 209, 539], [3, 634, 299, 148, 160, 169, 268, 394], [637, 732, 636, 750], [3, 660, 414, 162, 412, 657, 742, 402], [482, 78, 314, 492, 251, 488, 527, 482], [81, 439, 705, 318, 466, 413, 665, 190], [147, 662, 168, 92, 223, 555, 156, 360], [735, 228, 86, 753]], ![[688, 575, 325, 129, 727, 112, 591, 207], [291, 118, 686, 194], [731, 299, 734, 218, 621, 573, 550, 655], [642, 700, 51, 91], [180, 416, 110, 466, 135, 491, 346, 537], [392, 621, 568, 89, 35, 103, 379, 80], [576, 744, 141, 542, 411, 415, 336, 350], [112, 661, 444, 113, 380, 352, 350, 503], [346, 705, 355, 249]], ![[337, 220, 277, 472, 396, 196, 249, 735], [583, 435, 728, 324], [724, 463, 67, 582, 573, 714, 94, 34], [623, 402, 264, 576], [131, 709, 703, 340, 92, 657, 175, 592], [616, 112, 488, 27, 713, 545, 356, 466], [346, 663, 425, 552, 62, 403, 673, 690], [291, 518, 720, 526, 402, 653, 240, 444], [663, 334, 685, 205]]]
 h' := ![![[441, 59, 449, 501, 109], [506, 711, 210, 63, 219], [449, 500, 633, 25, 412], [566, 624, 240, 429, 754], [736, 103, 158, 299, 146], [105, 753, 382, 99, 259], [540, 441, 543, 500, 242], [640, 96, 63, 419, 65], [0, 0, 1], [0, 1]], ![[307, 634, 465, 423, 174], [349, 306, 273, 225, 664], [420, 410, 520, 180, 153], [89, 476, 188, 745, 575], [167, 261, 172, 90, 394], [359, 132, 560, 99, 293], [152, 310, 206, 427, 356], [413, 267, 165, 143, 748], [260, 537, 260, 657, 491], [441, 59, 449, 501, 109]], ![[489, 414, 480, 42, 154], [5, 618, 152, 506, 469], [254, 714, 349, 715, 721], [56, 743, 300, 411, 277], [34, 26, 122, 489, 392], [80, 378, 485, 7, 408], [705, 504, 301, 368, 707], [338, 518, 663, 503, 453], [684, 156, 709, 232, 199], [307, 634, 465, 423, 174]], ![[342, 406, 120, 548, 320], [376, 682, 463, 167, 280], [70, 250, 286, 570, 210], [316, 8, 66, 404, 337], [629, 595, 461, 240, 606], [54, 236, 193, 731, 319], [61, 258, 633, 178, 321], [103, 718, 280, 746, 22], [305, 590, 666, 0, 232], [489, 414, 480, 42, 154]], ![[0, 1], [61, 711, 416, 553, 639], [189, 397, 483, 24, 18], [464, 420, 720, 282, 328], [555, 529, 601, 396, 733], [290, 15, 651, 578, 235], [179, 1, 588, 41, 645], [737, 672, 343, 460, 226], [29, 231, 635, 625, 592], [342, 406, 120, 548, 320]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [370, 605, 202, 585], [], [], []]
 b := ![[], [240, 182, 0, 140, 453], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI757N0 : CertifiedPrimeIdeal' SI757N0 757 where
  n := 5
  hpos := by decide
  P := [117, 661, 694, 338, 692, 1]
  hirr := P757P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-178414164208296041, -179580415013359776, -10270291980307932, 69793639882182716, 416098654882043672]
  a := ![-1823, -1737, -153, 722, 4268]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-235685817976613, -237226439911968, -13567096407276, 92197674877388, 549667972103096]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI757N0 : Ideal.IsPrime I757N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI757N0 B_one_repr
lemma NI757N0 : Nat.card (O ⧸ I757N0) = 248587563395557 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI757N0

def PBC757 : ContainsPrimesAboveP 757 ![I757N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI757N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![757, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 757 (by decide) 𝕀

instance hp761 : Fact (Nat.Prime 761) := {out := by norm_num}

def I761N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9093, 4702, 641, -1641, -9716]] i)))

def SI761N0: IdealEqSpanCertificate' Table ![![9093, 4702, 641, -1641, -9716]] 
 ![![761, 0, 0, 0, 0], ![0, 761, 0, 0, 0], ![0, 0, 761, 0, 0], ![0, 0, 0, 761, 0], ![606, 521, 167, 210, 1]] where
  M :=![![![9093, 4702, 641, -1641, -9716], ![6922, 2887, 810, -148, -2146], ![-34928, -29190, -521, 15458, 84878], ![-108174, -66675, -3213, 35035, 190290], ![21746, 11995, 1055, -5454, -30379]]]
  hmulB := by decide  
  f := ![![![-35, 85, 8, -21, -104]], ![![658, 455, 96, -226, -1390]], ![![-500, -1650, -229, 566, 3182]], ![![-3312, -723, -297, 665, 4446]], ![![-600, -182, -60, 136, 889]]]
  g := ![![![7749, 6658, 2133, 2679, -9716], ![1718, 1473, 472, 592, -2146], ![-67636, -58148, -18627, -23402, 84878], ![-151674, -130365, -41763, -52465, 190290], ![24220, 20814, 6668, 8376, -30379]]]
  hle1 := by decide   
  hle2 := by decide  


def P761P0 : CertificateIrreducibleZModOfList' 761 4 2 9 [271, 135, 459, 734, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [341, 136, 454, 36], [371, 372, 649, 497], [76, 252, 419, 228], [0, 1]]
 g := ![![[434, 509, 504, 202], [513, 79, 17], [121, 277, 478], [147, 521, 622, 178], [570, 460, 191, 694], [633, 21, 393, 433], [66, 560, 524, 605], [27, 1], []], ![[213, 345, 265, 70, 490, 740], [527, 726, 342], [14, 710, 105], [12, 704, 322, 241, 713, 139], [629, 116, 474, 646, 455, 288], [499, 308, 553, 564, 383, 473], [693, 540, 248, 657, 597, 72], [608, 529, 237, 746, 566, 84], [221, 712, 535]], ![[400, 10, 391, 339, 724, 583], [727, 391, 671], [658, 361, 168], [303, 680, 484, 122, 348, 178], [173, 43, 611, 396, 529, 548], [182, 32, 637, 457, 0, 137], [465, 758, 532, 99, 702, 535], [269, 317, 448, 657, 369, 116], [296, 378, 445]], ![[672, 100, 710, 118, 563, 734], [320, 729, 512], [246, 216, 450], [15, 608, 9, 739, 406, 451], [322, 198, 37, 693, 719, 212], [121, 340, 111, 664, 348, 748], [318, 385, 568, 526, 367, 628], [191, 126, 250, 698, 334, 86], [237, 337, 236]]]
 h' := ![![[341, 136, 454, 36], [718, 43, 579, 461], [145, 32, 354, 481], [496, 465, 190, 145], [13, 727, 715, 244], [443, 751, 94, 464], [378, 518, 588, 235], [293, 650, 409, 270], [0, 0, 1], [0, 1]], ![[371, 372, 649, 497], [292, 603, 180, 449], [412, 638, 215, 543], [182, 523, 501, 348], [587, 568, 653, 756], [368, 36, 672, 146], [743, 492, 229, 394], [517, 455, 472, 688], [76, 96, 39, 16], [341, 136, 454, 36]], ![[76, 252, 419, 228], [246, 685, 298, 356], [698, 555, 396, 91], [474, 114, 542, 602], [324, 27, 601, 575], [145, 604, 101, 50], [166, 690, 608, 736], [737, 48, 20, 252], [350, 451, 443, 503], [371, 372, 649, 497]], ![[0, 1], [570, 191, 465, 256], [585, 297, 557, 407], [433, 420, 289, 427], [351, 200, 314, 708], [534, 131, 655, 101], [560, 583, 97, 157], [595, 369, 621, 312], [146, 214, 278, 242], [76, 252, 419, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [169, 575, 206], []]
 b := ![[], [], [375, 5, 444, 560], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI761N0 : CertifiedPrimeIdeal' SI761N0 761 where
  n := 4
  hpos := by decide
  P := [271, 135, 459, 734, 1]
  hirr := P761P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-100932315909497, -122282465071683, -7069127787084, 43561775611200, 267856713580689]
  a := ![2342, 2234, 199, -920, -5483]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-213432458273071, -183542221078332, -58789934685627, -73858538865090, 267856713580689]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI761N0 : Ideal.IsPrime I761N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI761N0 B_one_repr
lemma NI761N0 : Nat.card (O ⧸ I761N0) = 335381132641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI761N0

def I761N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, 85, 8, -21, -104]] i)))

def SI761N1: IdealEqSpanCertificate' Table ![![-35, 85, 8, -21, -104]] 
 ![![761, 0, 0, 0, 0], ![197, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![563, 0, 0, 1, 0], ![421, 0, 0, 0, 1]] where
  M :=![![![-35, 85, 8, -21, -104], ![658, 455, 96, -226, -1390], ![-500, -1650, -229, 566, 3182], ![-3312, -723, -297, 665, 4446], ![812, 313, 89, -204, -1311]]]
  hmulB := by decide  
  f := ![![![9093, 4702, 641, -1641, -9716]], ![![2363, 1221, 167, -425, -2518]], ![![-22, -26, 1, 16, 86]], ![![6585, 3391, 470, -1168, -6938]], ![![5059, 2617, 356, -915, -5415]]]
  g := ![![![51, 85, 8, -21, -104], ![819, 455, 96, -226, -1390], ![-1752, -1650, -229, 566, 3182], ![-2768, -723, -297, 665, 4446], ![796, 313, 89, -204, -1311]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI761N1 : Nat.card (O ⧸ I761N1) = 761 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI761N1)

lemma isPrimeI761N1 : Ideal.IsPrime I761N1 := prime_ideal_of_norm_prime hp761.out _ NI761N1
def MulI761N0 : IdealMulLeCertificate' Table 
  ![![9093, 4702, 641, -1641, -9716]] ![![-35, 85, 8, -21, -104]]
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


lemma PB953I14_primes (p : ℕ) :
  p ∈ Set.range ![709, 719, 727, 733, 739, 743, 751, 757, 761] ↔ Nat.Prime p ∧ 701 < p ∧ p ≤ 761 := by
  rw [← List.mem_ofFn']
  convert primes_range 701 761 (by omega)

def PB953I14 : PrimesBelowBoundCertificateInterval O 701 761 953 where
  m := 9
  g := ![3, 2, 3, 3, 3, 2, 1, 1, 2]
  P := ![709, 719, 727, 733, 739, 743, 751, 757, 761]
  hP := PB953I14_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I709N0, I709N1, I709N2]
    · exact ![I719N0, I719N1]
    · exact ![I727N0, I727N1, I727N2]
    · exact ![I733N0, I733N1, I733N2]
    · exact ![I739N0, I739N1, I739N2]
    · exact ![I743N0, I743N1]
    · exact ![I751N0]
    · exact ![I757N0]
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
    · exact ![371694959, 516961]
    · exact ![528529, 528529, 727]
    · exact ![537289, 537289, 733]
    · exact ![546121, 546121, 739]
    · exact ![410172407, 552049]
    · exact ![238890943128751]
    · exact ![248587563395557]
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
    · dsimp ; intro j
      fin_cases j
      exact NI733N0
      exact NI733N1
      exact NI733N2
    · dsimp ; intro j
      fin_cases j
      exact NI739N0
      exact NI739N1
      exact NI739N2
    · dsimp ; intro j
      fin_cases j
      exact NI743N0
      exact NI743N1
    · dsimp ; intro j
      fin_cases j
      exact NI751N0
    · dsimp ; intro j
      fin_cases j
      exact NI757N0
    · dsimp ; intro j
      fin_cases j
      exact NI761N0
      exact NI761N1
  β := ![I709N2, I727N2, I733N2, I739N2, I761N1]
  Il := ![[I709N2], [], [I727N2], [I733N2], [I739N2], [], [], [], [I761N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
