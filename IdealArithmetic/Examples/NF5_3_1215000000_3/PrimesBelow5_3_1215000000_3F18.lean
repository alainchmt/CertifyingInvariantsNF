
import IdealArithmetic.Examples.NF5_3_1215000000_3.RI5_3_1215000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp967 : Fact (Nat.Prime 967) := {out := by norm_num}

def I967N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5611160, -3414024, -491067, -412113, 877955]] i)))

def SI967N0: IdealEqSpanCertificate' Table ![![5611160, -3414024, -491067, -412113, 877955]] 
 ![![967, 0, 0, 0, 0], ![0, 967, 0, 0, 0], ![0, 0, 967, 0, 0], ![243, 150, 401, 1, 0], ![112, 788, 381, 0, 1]] where
  M :=![![![5611160, -3414024, -491067, -412113, 877955], ![-10535460, 6410161, 922022, 773776, -1648452], ![19781424, -12035666, -1731199, -1452860, 3095104], ![-13302894, 8094014, 1164224, 977017, -2081494], ![13501329, -8214588, -1181593, -991621, 2112456]]]
  hmulB := by decide  
  f := ![![![19094, 11392, 1715, -1137, -2679]], ![![32148, 19267, 2950, -1928, -4548]], ![![54576, 32478, 4931, -3196, -7712]], ![![32448, 19338, 2936, -1912, -4581]], ![![49961, 29846, 4550, -2965, -7062]]]
  g := ![![![7677, -655042, -175527, -412113, 877955], ![-14412, 1229911, 329574, 773776, -1648452], ![27068, -2309254, -618789, -1452860, 3095104], ![-18191, 1553008, 416163, 977017, -2081494], ![18480, -1576098, -422324, -991621, 2112456]]]
  hle1 := by decide   
  hle2 := by decide  


def P967P0 : CertificateIrreducibleZModOfList' 967 3 2 9 [739, 797, 421, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [746, 220, 234], [767, 746, 733], [0, 1]]
 g := ![![[860, 921, 246], [771, 933, 122], [527, 349, 236], [23, 813], [516, 781], [755, 4], [324, 546, 444], [104, 70, 280], [1]], ![[471, 363, 824, 798], [856, 800, 868, 319], [339, 736, 69, 493], [711, 406], [578, 257], [507, 696], [442, 762, 268, 684], [934, 325, 103, 575], [858, 95, 191, 154]], ![[748, 613, 632, 349], [242, 309, 919, 851], [558, 578, 912, 402], [345, 317], [737, 36], [458, 95], [492, 106, 108, 944], [466, 838, 310, 743], [935, 730, 898, 813]]]
 h' := ![![[746, 220, 234], [761, 125, 182], [248, 160, 934], [738, 679, 255], [931, 81, 167], [331, 868, 598], [380, 368, 2], [504, 528, 205], [228, 170, 546], [0, 1]], ![[767, 746, 733], [116, 643, 632], [440, 513, 251], [472, 551, 29], [61, 514, 420], [68, 628, 363], [704, 457, 574], [768, 457, 887], [83, 344, 342], [746, 220, 234]], ![[0, 1], [700, 199, 153], [233, 294, 749], [889, 704, 683], [649, 372, 380], [124, 438, 6], [121, 142, 391], [785, 949, 842], [431, 453, 79], [767, 746, 733]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [839, 174], []]
 b := ![[], [714, 714, 272], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI967N0 : CertifiedPrimeIdeal' SI967N0 967 where
  n := 3
  hpos := by decide
  P := [739, 797, 421, 1]
  hirr := P967P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3878162, 1766310, 1944592, -1185571, -920914]
  a := ![0, 4, 9, -4, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![400577, 936176, 856491, -1185571, -920914]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI967N0 : Ideal.IsPrime I967N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI967N0 B_one_repr
lemma NI967N0 : Nat.card (O ⧸ I967N0) = 904231063 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI967N0

def I967N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19094, 11392, 1715, -1137, -2679]] i)))

def SI967N1: IdealEqSpanCertificate' Table ![![19094, 11392, 1715, -1137, -2679]] 
 ![![967, 0, 0, 0, 0], ![0, 967, 0, 0, 0], ![812, 165, 1, 0, 0], ![700, 332, 0, 1, 0], ![700, 342, 0, 0, 1]] where
  M :=![![![19094, 11392, 1715, -1137, -2679], ![32148, 19267, 2950, -1928, -4548], ![54576, 32478, 4931, -3196, -7712], ![30198, 17862, 2536, -1817, -4118], ![47679, 28664, 4459, -2871, -6810]]]
  hmulB := by decide  
  f := ![![![5611160, -3414024, -491067, -412113, 877955]], ![![-10535460, 6410161, 922022, 773776, -1648452]], ![![2934532, -1785467, -256819, -215528, 459152]], ![![430958, -262202, -37716, -31653, 67426]], ![![349727, -212778, -30607, -25687, 54716]]]
  g := ![![![1342, 1057, 1715, -1137, -2679], ![2244, 1787, 2950, -1928, -4548], ![3812, 3017, 4931, -3196, -7712], ![2198, 1666, 2536, -1817, -4118], ![3313, 2663, 4459, -2871, -6810]]]
  hle1 := by decide   
  hle2 := by decide  


def P967P1 : CertificateIrreducibleZModOfList' 967 2 2 9 [264, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [937, 966], [0, 1]]
 g := ![![[110, 202], [450, 226], [375, 412], [429], [941], [412], [45, 437], [37, 290], [937, 1]], ![[819, 765], [439, 741], [586, 555], [429], [941], [412], [473, 530], [40, 677], [907, 966]]]
 h' := ![![[937, 966], [141, 838], [601, 648], [434, 223], [663, 823], [286, 891], [691, 223], [869, 668], [184, 636], [0, 1]], ![[0, 1], [143, 129], [501, 319], [513, 744], [148, 144], [632, 76], [770, 744], [169, 299], [444, 331], [937, 966]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124]]
 b := ![[], [930, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI967N1 : CertifiedPrimeIdeal' SI967N1 967 where
  n := 2
  hpos := by decide
  P := [264, 30, 1]
  hirr := P967P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2236329, -314512, 370897, 368679, 504550]
  a := ![3, -4, 59, -65, -178]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-945879, -368635, 370897, 368679, 504550]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI967N1 : Ideal.IsPrime I967N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI967N1 B_one_repr
lemma NI967N1 : Nat.card (O ⧸ I967N1) = 935089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI967N1
def MulI967N0 : IdealMulLeCertificate' Table 
  ![![5611160, -3414024, -491067, -412113, 877955]] ![![19094, 11392, 1715, -1137, -2679]]
  ![![967, 0, 0, 0, 0]] where
 M := ![![![967, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC967 : ContainsPrimesAboveP 967 ![I967N0, I967N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI967N0
    exact isPrimeI967N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 967 (by decide) (𝕀 ⊙ MulI967N0)
instance hp971 : Fact (Nat.Prime 971) := {out := by norm_num}

def I971N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![65609, -39903, -5739, -4818, 10262]] i)))

def SI971N0: IdealEqSpanCertificate' Table ![![65609, -39903, -5739, -4818, 10262]] 
 ![![971, 0, 0, 0, 0], ![0, 971, 0, 0, 0], ![0, 0, 971, 0, 0], ![558, 52, 406, 1, 0], ![333, 123, 615, 0, 1]] where
  M :=![![![65609, -39903, -5739, -4818, 10262], ![-123144, 74950, 10781, 9046, -19272], ![231264, -140681, -20230, -16982, 36184], ![-155532, 94625, 13619, 11431, -24328], ![157830, -96021, -13807, -11584, 24705]]]
  hmulB := by decide  
  f := ![![![79, -1, -23, 6, 6]], ![![-72, 56, 11, -34, 24]], ![![-288, -3, 220, 70, -136]], ![![-78, 1, 79, 31, -52]], ![![-165, 5, 133, 42, -81]]]
  g := ![![![-683, -1083, -4491, -4818, 10262], ![1284, 2034, 8435, 9046, -19272], ![-2412, -3819, -15838, -16982, 36184], ![1614, 2567, 10643, 11431, -24328], ![-1653, -2608, -10818, -11584, 24705]]]
  hle1 := by decide   
  hle2 := by decide  


def P971P0 : CertificateIrreducibleZModOfList' 971 3 2 9 [586, 101, 489, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [264, 738, 849], [218, 232, 122], [0, 1]]
 g := ![![[722, 665, 845], [707, 385, 88], [744, 826], [310, 295, 466], [39, 189], [356, 655], [786, 162, 564], [121, 300, 255], [1]], ![[38, 281, 276, 455], [154, 348, 49, 399], [766, 529], [41, 444, 689, 332], [431, 793], [113, 49], [932, 338, 179, 654], [645, 557, 548, 506], [299, 833, 622, 893]], ![[232, 920, 485, 465], [578, 251, 18, 251], [81, 380], [899, 515, 540, 622], [233, 304], [819, 927], [57, 871, 100, 874], [830, 518, 658, 396], [546, 844, 363, 78]]]
 h' := ![![[264, 738, 849], [315, 881, 344], [87, 377, 404], [888, 753, 760], [597, 304, 741], [593, 571, 200], [629, 20, 224], [948, 15, 848], [385, 870, 482], [0, 1]], ![[218, 232, 122], [943, 364, 485], [717, 753, 155], [694, 798, 948], [303, 923, 826], [288, 830, 42], [134, 55, 7], [38, 830, 706], [802, 656, 829], [264, 738, 849]], ![[0, 1], [756, 697, 142], [615, 812, 412], [372, 391, 234], [260, 715, 375], [275, 541, 729], [303, 896, 740], [627, 126, 388], [136, 416, 631], [218, 232, 122]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [422, 568], []]
 b := ![[], [803, 849, 132], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI971N0 : CertifiedPrimeIdeal' SI971N0 971 where
  n := 3
  hpos := by decide
  P := [586, 101, 489, 1]
  hirr := P971P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3553277, 286583, 870756, -22745, 417429]
  a := ![1, 1, 6, -5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-133744, -51364, -253979, -22745, 417429]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI971N0 : Ideal.IsPrime I971N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI971N0 B_one_repr
lemma NI971N0 : Nat.card (O ⧸ I971N0) = 915498611 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI971N0

def I971N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, -1, -23, 6, 6]] i)))

def SI971N1: IdealEqSpanCertificate' Table ![![79, -1, -23, 6, 6]] 
 ![![971, 0, 0, 0, 0], ![0, 971, 0, 0, 0], ![898, 159, 1, 0, 0], ![463, 432, 0, 1, 0], ![565, 501, 0, 0, 1]] where
  M :=![![![79, -1, -23, 6, 6], ![-72, 56, 11, -34, 24], ![-288, -3, 220, 70, -136], ![852, -165, -349, 101, 128], ![-546, 145, 149, -84, 39]]]
  hmulB := by decide  
  f := ![![![65609, -39903, -5739, -4818, 10262]], ![![-123144, 74950, 10781, 9046, -19272]], ![![40750, -24775, -3563, -2992, 6372]], ![![-23663, 14416, 2074, 1739, -3706]], ![![-25199, 15354, 2209, 1852, -3947]]]
  g := ![![![15, -2, -23, 6, 6], ![-8, 1, 11, -34, 24], ![-158, 3, 220, 70, -136], ![201, -54, -349, 101, 128], ![-121, -7, 149, -84, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P971P1 : CertificateIrreducibleZModOfList' 971 2 2 9 [449, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [906, 970], [0, 1]]
 g := ![![[783, 916], [866, 567], [721], [156, 331], [119], [183], [83, 793], [934, 12], [906, 1]], ![[474, 55], [909, 404], [721], [3, 640], [119], [183], [1, 178], [154, 959], [841, 970]]]
 h' := ![![[906, 970], [537, 218], [531, 852], [839, 816], [248, 723], [589, 327], [602, 315], [106, 42], [55, 863], [0, 1]], ![[0, 1], [932, 753], [498, 119], [233, 155], [832, 248], [696, 644], [518, 656], [289, 929], [278, 108], [906, 970]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [321]]
 b := ![[], [604, 646]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI971N1 : CertifiedPrimeIdeal' SI971N1 971 where
  n := 2
  hpos := by decide
  P := [449, 65, 1]
  hirr := P971P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-448504, -55844, 90703, 69087, 82725]
  a := ![1, -8, -30, 18, 87]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-165424, -88330, 90703, 69087, 82725]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI971N1 : Ideal.IsPrime I971N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI971N1 B_one_repr
lemma NI971N1 : Nat.card (O ⧸ I971N1) = 942841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI971N1
def MulI971N0 : IdealMulLeCertificate' Table 
  ![![65609, -39903, -5739, -4818, 10262]] ![![79, -1, -23, 6, 6]]
  ![![971, 0, 0, 0, 0]] where
 M := ![![![971, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC971 : ContainsPrimesAboveP 971 ![I971N0, I971N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI971N0
    exact isPrimeI971N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 971 (by decide) (𝕀 ⊙ MulI971N0)
instance hp977 : Fact (Nat.Prime 977) := {out := by norm_num}

def I977N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-245174, 149175, 21456, 18011, -38365]] i)))

def SI977N0: IdealEqSpanCertificate' Table ![![-245174, 149175, 21456, 18011, -38365]] 
 ![![977, 0, 0, 0, 0], ![0, 977, 0, 0, 0], ![0, 0, 977, 0, 0], ![193, 920, 656, 1, 0], ![201, 345, 490, 0, 1]] where
  M :=![![![-245174, 149175, 21456, 18011, -38365], ![460380, -280094, -40307, -33818, 72044], ![-864528, 525935, 75718, 63474, -135272], ![581442, -353731, -50897, -42645, 90926], ![-589947, 358973, 51598, 43297, -92270]]]
  hmulB := by decide  
  f := ![![![-4480, -2697, -418, 257, 623]], ![![-7476, -4532, -719, 410, 1028]], ![![-12336, -7577, -1240, 618, 1640]], ![![-16214, -9892, -1593, 852, 2193]], ![![-9759, -5962, -963, 508, 1315]]]
  g := ![![![4084, -3260, 7170, 18011, -38365], ![-7670, 6118, -13467, -33818, 72044], ![14406, -11465, 25302, 63474, -135272], ![-9687, 7687, -17021, -42645, 90926], ![9826, -7821, 17258, 43297, -92270]]]
  hle1 := by decide   
  hle2 := by decide  


def P977P0 : CertificateIrreducibleZModOfList' 977 3 2 9 [361, 7, 688, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [741, 287, 106], [525, 689, 871], [0, 1]]
 g := ![![[615, 966, 722], [52, 815], [900, 8], [763, 127], [356, 664, 801], [457, 688], [134, 517, 889], [155, 646, 476], [1]], ![[37, 823, 45, 911], [624, 63], [808, 109], [507, 928], [976, 436, 539, 79], [276, 915], [917, 177, 513, 951], [442, 728, 348, 951], [373, 874, 604, 53]], ![[506, 973, 755, 216], [350, 573], [209, 203], [206, 861], [355, 569, 513, 796], [235, 244], [39, 36, 866, 371], [817, 203, 594, 280], [17, 929, 860, 924]]]
 h' := ![![[741, 287, 106], [312, 421, 120], [199, 481, 132], [490, 292, 553], [448, 450, 416], [48, 721, 281], [476, 421, 601], [711, 569, 501], [616, 970, 289], [0, 1]], ![[525, 689, 871], [616, 745, 296], [217, 681, 269], [533, 184, 652], [371, 234, 190], [246, 850, 383], [169, 312, 502], [643, 540, 48], [475, 542, 48], [741, 287, 106]], ![[0, 1], [280, 788, 561], [866, 792, 576], [325, 501, 749], [357, 293, 371], [976, 383, 313], [521, 244, 851], [20, 845, 428], [357, 442, 640], [525, 689, 871]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [684, 458], []]
 b := ![[], [653, 55, 604], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI977N0 : CertifiedPrimeIdeal' SI977N0 977 where
  n := 3
  hpos := by decide
  P := [361, 7, 688, 1]
  hirr := P977P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31266711, 756029, 14464655, 1245398, -5140216]
  a := ![-1, 11, 13, 5, -34]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![779483, 643157, 1756591, 1245398, -5140216]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI977N0 : Ideal.IsPrime I977N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI977N0 B_one_repr
lemma NI977N0 : Nat.card (O ⧸ I977N0) = 932574833 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI977N0

def I977N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![386, -89, -194, 25, 79]] i)))

def SI977N1: IdealEqSpanCertificate' Table ![![386, -89, -194, 25, 79]] 
 ![![977, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![930, 0, 1, 0, 0], ![736, 0, 0, 1, 0], ![447, 0, 0, 0, 1]] where
  M :=![![![386, -89, -194, 25, 79], ![-948, 246, 177, -230, 100], ![-1200, -441, 1106, 554, -920], ![5994, -907, -2703, 301, 1058], ![-4011, 853, 1278, -603, -134]]]
  hmulB := by decide  
  f := ![![![47581240, -28949857, -4164140, -3494657, 7444731]], ![![1467004, -892568, -128387, -107746, 229532]], ![![45463968, -27661643, -3978844, -3339152, 7113454]], ![![35728754, -21738443, -3126853, -2624139, 5590246]], ![![21886701, -13316522, -1915446, -1607494, 3424469]]]
  g := ![![![133, -89, -194, 25, 79], ![-50, 246, 177, -230, 100], ![-1036, -441, 1106, 554, -920], ![1898, -907, -2703, 301, 1058], ![-733, 853, 1278, -603, -134]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI977N1 : Nat.card (O ⧸ I977N1) = 977 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI977N1)

lemma isPrimeI977N1 : Ideal.IsPrime I977N1 := prime_ideal_of_norm_prime hp977.out _ NI977N1

def I977N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-191, 42, 32, 42, 26]] i)))

def SI977N2: IdealEqSpanCertificate' Table ![![-191, 42, 32, 42, 26]] 
 ![![977, 0, 0, 0, 0], ![610, 1, 0, 0, 0], ![137, 0, 1, 0, 0], ![898, 0, 0, 1, 0], ![56, 0, 0, 0, 1]] where
  M :=![![![-191, 42, 32, 42, 26], ![-312, -175, 62, 116, 168], ![-2016, -198, 265, 460, 464], ![-2628, -786, 338, 671, 836], ![-3594, -674, 452, 846, 945]]]
  hmulB := by decide  
  f := ![![![37685, -5882, -16136, 2430, 5782]], ![![23458, -3647, -10062, 1496, 3620]], ![![5165, -852, -2155, 386, 726]], ![![35182, -5490, -15066, 2267, 5400]], ![![1826, -254, -820, 82, 325]]]
  g := ![![![-71, 42, 32, 42, 26], ![-16, -175, 62, 116, 168], ![-365, -198, 265, 460, 464], ![-224, -786, 338, 671, 836], ![-478, -674, 452, 846, 945]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI977N2 : Nat.card (O ⧸ I977N2) = 977 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI977N2)

lemma isPrimeI977N2 : Ideal.IsPrime I977N2 := prime_ideal_of_norm_prime hp977.out _ NI977N2
def MulI977N0 : IdealMulLeCertificate' Table 
  ![![-245174, 149175, 21456, 18011, -38365]] ![![386, -89, -194, 25, 79]]
  ![![37685, -5882, -16136, 2430, 5782]] where
 M := ![![![37685, -5882, -16136, 2430, 5782]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI977N1 : IdealMulLeCertificate' Table 
  ![![37685, -5882, -16136, 2430, 5782]] ![![-191, 42, 32, 42, 26]]
  ![![977, 0, 0, 0, 0]] where
 M := ![![![977, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC977 : ContainsPrimesAboveP 977 ![I977N0, I977N1, I977N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI977N0
    exact isPrimeI977N1
    exact isPrimeI977N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 977 (by decide) (𝕀 ⊙ MulI977N0 ⊙ MulI977N1)
instance hp983 : Fact (Nat.Prime 983) := {out := by norm_num}

def I983N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1238, -655, -96, 79, 159]] i)))

def SI983N0: IdealEqSpanCertificate' Table ![![-1238, -655, -96, 79, 159]] 
 ![![983, 0, 0, 0, 0], ![0, 983, 0, 0, 0], ![0, 0, 983, 0, 0], ![501, 18, 247, 1, 0], ![547, 667, 464, 0, 1]] where
  M :=![![![-1238, -655, -96, 79, 159], ![-1908, -1254, -177, 126, 316], ![-3792, -1895, -242, 278, 504], ![-2070, -1277, -129, 199, 398], ![-3567, -1761, -186, 305, 530]]]
  hmulB := by decide  
  f := ![![![8, -9, 6, 11, -11]], ![![132, -8, -75, -10, 44]], ![![-528, 111, 188, -62, -40]], ![![-126, 23, 49, -10, -15]], ![![-155, 42, 41, -30, 5]]]
  g := ![![![-130, -110, -95, 79, 159], ![-242, -218, -181, 126, 316], ![-426, -349, -308, 278, 504], ![-325, -275, -238, 199, 398], ![-454, -367, -327, 305, 530]]]
  hle1 := by decide   
  hle2 := by decide  


def P983P0 : CertificateIrreducibleZModOfList' 983 3 2 9 [36, 200, 618, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [877, 941, 371], [471, 41, 612], [0, 1]]
 g := ![![[276, 279, 922], [491, 151, 547], [940, 645, 324], [135, 18], [129, 734, 798], [517, 377], [844, 249, 861], [627, 548, 520], [1]], ![[343, 190, 857, 433], [949, 687, 949, 305], [929, 818, 495, 578], [772, 392], [215, 286, 785, 603], [676, 288], [848, 339, 99, 255], [872, 857, 773, 472], [490, 232, 199, 910]], ![[951, 349, 546, 792], [867, 451, 199, 650], [491, 396, 732, 559], [252, 242], [159, 38, 501, 375], [977, 895], [117, 829, 678, 820], [815, 570, 629, 261], [364, 728, 721, 73]]]
 h' := ![![[877, 941, 371], [18, 312, 389], [565, 467, 300], [754, 583, 18], [271, 14, 367], [122, 681, 468], [89, 545, 547], [37, 669, 907], [947, 783, 365], [0, 1]], ![[471, 41, 612], [857, 518, 962], [532, 216, 753], [334, 689, 771], [714, 177, 581], [114, 760, 531], [665, 586, 498], [41, 497, 316], [434, 579, 728], [877, 941, 371]], ![[0, 1], [493, 153, 615], [623, 300, 913], [852, 694, 194], [811, 792, 35], [125, 525, 967], [634, 835, 921], [161, 800, 743], [767, 604, 873], [471, 41, 612]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 306], []]
 b := ![[], [875, 199, 492], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI983N0 : CertifiedPrimeIdeal' SI983N0 983 where
  n := 3
  hpos := by decide
  P := [36, 200, 618, 1]
  hirr := P983P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9261540, -4907840, -1130816, 2270592, -474496]
  a := ![0, -16, -10, -18, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-883780, 275392, -347712, 2270592, -474496]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI983N0 : Ideal.IsPrime I983N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI983N0 B_one_repr
lemma NI983N0 : Nat.card (O ⧸ I983N0) = 949862087 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI983N0

def I983N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, -7, -1, -2, 2]] i)))

def SI983N1: IdealEqSpanCertificate' Table ![![29, -7, -1, -2, 2]] 
 ![![983, 0, 0, 0, 0], ![89, 1, 0, 0, 0], ![926, 0, 1, 0, 0], ![526, 0, 0, 1, 0], ![332, 0, 0, 0, 1]] where
  M :=![![![29, -7, -1, -2, 2], ![-24, 32, 5, 2, -8], ![96, -29, -4, -6, 8], ![-36, 37, 5, 3, -8], ![66, -17, -1, -4, 5]]]
  hmulB := by decide  
  f := ![![![-257, 35, 111, -2, -22]], ![![-23, 3, 10, 0, -2]], ![![-242, 33, 104, -2, -20]], ![![-142, 19, 61, -1, -12]], ![![-86, 11, 37, 0, -7]]]
  g := ![![![2, -7, -1, -2, 2], ![-6, 32, 5, 2, -8], ![7, -29, -4, -6, 8], ![-7, 37, 5, 3, -8], ![3, -17, -1, -4, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI983N1 : Nat.card (O ⧸ I983N1) = 983 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI983N1)

lemma isPrimeI983N1 : Ideal.IsPrime I983N1 := prime_ideal_of_norm_prime hp983.out _ NI983N1

def I983N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![62, -14, -21, 9, 3]] i)))

def SI983N2: IdealEqSpanCertificate' Table ![![62, -14, -21, 9, 3]] 
 ![![983, 0, 0, 0, 0], ![400, 1, 0, 0, 0], ![229, 0, 1, 0, 0], ![201, 0, 0, 1, 0], ![266, 0, 0, 0, 1]] where
  M :=![![![62, -14, -21, 9, 3], ![-36, 35, -20, -36, 36], ![-432, 16, 251, 32, -144], ![882, -196, -302, 125, 46], ![-363, 142, 55, -121, 62]]]
  hmulB := by decide  
  f := ![![![21748, 9290, 1417, -1343, -2159]], ![![8876, 3803, 580, -548, -884]], ![![5132, 2190, 334, -317, -509]], ![![4470, 1922, 293, -276, -447]], ![![5941, 2538, 387, -367, -590]]]
  g := ![![![8, -14, -21, 9, 3], ![-12, 35, -20, -36, 36], ![-33, 16, 251, 32, -144], ![113, -196, -302, 125, 46], ![-63, 142, 55, -121, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI983N2 : Nat.card (O ⧸ I983N2) = 983 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI983N2)

lemma isPrimeI983N2 : Ideal.IsPrime I983N2 := prime_ideal_of_norm_prime hp983.out _ NI983N2
def MulI983N0 : IdealMulLeCertificate' Table 
  ![![-1238, -655, -96, 79, 159]] ![![29, -7, -1, -2, 2]]
  ![![-21748, -9290, -1417, 1343, 2159]] where
 M := ![![![-21748, -9290, -1417, 1343, 2159]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI983N1 : IdealMulLeCertificate' Table 
  ![![-21748, -9290, -1417, 1343, 2159]] ![![62, -14, -21, 9, 3]]
  ![![983, 0, 0, 0, 0]] where
 M := ![![![-983, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC983 : ContainsPrimesAboveP 983 ![I983N0, I983N1, I983N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI983N0
    exact isPrimeI983N1
    exact isPrimeI983N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 983 (by decide) (𝕀 ⊙ MulI983N0 ⊙ MulI983N1)
instance hp991 : Fact (Nat.Prime 991) := {out := by norm_num}

def I991N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2254, 381, 234, 355, 153]] i)))

def SI991N0: IdealEqSpanCertificate' Table ![![-2254, 381, 234, 355, 153]] 
 ![![991, 0, 0, 0, 0], ![0, 991, 0, 0, 0], ![0, 0, 991, 0, 0], ![242, 11, 712, 1, 0], ![65, 534, 474, 0, 1]] where
  M :=![![![-2254, 381, 234, 355, 153], ![-1836, -2222, 283, 774, 1420], ![-17040, -907, 1910, 3406, 3096], ![-17658, -6609, 2191, 4619, 6102], ![-27285, -4505, 3166, 6043, 6522]]]
  hmulB := by decide  
  f := ![![![-340, -237, -52, 27, 59]], ![![-708, -360, -55, 14, 108]], ![![-1296, -669, 44, 106, 56]], ![![-1022, -543, 18, 83, 56]], ![![-1025, -530, -12, 60, 89]]]
  g := ![![![-99, -86, -328, 355, 153], ![-284, -776, -1235, 774, 1420], ![-1052, -1707, -3926, 3406, 3096], ![-1546, -3346, -6235, 4619, 6102], ![-1931, -3586, -7458, 6043, 6522]]]
  hle1 := by decide   
  hle2 := by decide  


def P991P0 : CertificateIrreducibleZModOfList' 991 3 2 9 [520, 179, 76, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [443, 558, 202], [472, 432, 789], [0, 1]]
 g := ![![[710, 800, 967], [253, 957, 848], [359, 916, 61], [748, 520, 529], [208, 49, 733], [642, 773], [746, 846, 594], [368, 488, 821], [1]], ![[61, 666, 176, 720], [37, 858, 427, 585], [355, 458, 525, 754], [552, 789, 478, 336], [641, 668, 429, 338], [204, 13], [942, 446, 515, 165], [869, 660, 713, 697], [69, 630, 214, 261]], ![[227, 72, 14, 633], [468, 713, 178, 886], [165, 226, 661, 686], [938, 889, 972, 804], [893, 248, 913, 836], [885, 458], [19, 569, 702, 96], [823, 482, 563, 426], [142, 312, 258, 730]]]
 h' := ![![[443, 558, 202], [243, 776, 408], [619, 809, 471], [503, 97, 141], [850, 752, 968], [594, 495, 730], [552, 825, 42], [894, 318, 680], [471, 812, 915], [0, 1]], ![[472, 432, 789], [668, 106, 32], [691, 365, 220], [244, 516, 235], [703, 523, 255], [745, 468, 121], [607, 645, 468], [945, 330, 245], [646, 324, 380], [443, 558, 202]], ![[0, 1], [916, 109, 551], [558, 808, 300], [204, 378, 615], [584, 707, 759], [540, 28, 140], [847, 512, 481], [161, 343, 66], [514, 846, 687], [472, 432, 789]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [764, 231], []]
 b := ![[], [130, 496, 200], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI991N0 : CertifiedPrimeIdeal' SI991N0 991 where
  n := 3
  hpos := by decide
  P := [520, 179, 76, 1]
  hirr := P991P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1808887, 2884038, 2570649, -2109473, -2822531]
  a := ![13, 8, 11, 2, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![698434, 1547245, 2868209, -2109473, -2822531]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI991N0 : Ideal.IsPrime I991N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI991N0 B_one_repr
lemma NI991N0 : Nat.card (O ⧸ I991N0) = 973242271 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI991N0

def I991N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2581, -1570, -226, -190, 404]] i)))

def SI991N1: IdealEqSpanCertificate' Table ![![2581, -1570, -226, -190, 404]] 
 ![![991, 0, 0, 0, 0], ![741, 1, 0, 0, 0], ![924, 0, 1, 0, 0], ![669, 0, 0, 1, 0], ![590, 0, 0, 0, 1]] where
  M :=![![![2581, -1570, -226, -190, 404], ![-4848, 2949, 426, 356, -760], ![9120, -5538, -803, -668, 1424], ![-6120, 3730, 534, 443, -956], ![6216, -3778, -540, -456, 965]]]
  hmulB := by decide  
  f := ![![![-966893, -577498, -87554, 57502, 136140]], ![![-724623, -432797, -65616, 43094, 102028]], ![![-904308, -540118, -81887, 53780, 127328]], ![![-654255, -390768, -59244, 38909, 92120]], ![![-578098, -345282, -52348, 34380, 81397]]]
  g := ![![![1275, -1570, -226, -190, 404], ![-2395, 2949, 426, 356, -760], ![4502, -5538, -803, -668, 1424], ![-3023, 3730, 534, 443, -956], ![3068, -3778, -540, -456, 965]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI991N1 : Nat.card (O ⧸ I991N1) = 991 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI991N1)

lemma isPrimeI991N1 : Ideal.IsPrime I991N1 := prime_ideal_of_norm_prime hp991.out _ NI991N1

def I991N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-92111, -54688, -8144, 5646, 13102]] i)))

def SI991N2: IdealEqSpanCertificate' Table ![![-92111, -54688, -8144, 5646, 13102]] 
 ![![991, 0, 0, 0, 0], ![808, 1, 0, 0, 0], ![205, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![724, 0, 0, 0, 1]] where
  M :=![![![-92111, -54688, -8144, 5646, 13102], ![-157224, -92799, -13572, 9916, 22584], ![-271008, -158128, -22295, 18024, 39664], ![-159372, -89432, -10974, 12411, 24756], ![-249078, -141764, -18348, 18382, 37889]]]
  hmulB := by decide  
  f := ![![![-270389, 162792, 25676, 21510, -44466]], ![![-219920, 132417, 20876, 17500, -36168]], ![![-56975, 34280, 5421, 4506, -9350]], ![![-4816, 2872, 490, 411, -828]], ![![-198134, 119332, 18776, 15754, -32563]]]
  g := ![![![36495, -54688, -8144, 5646, 13102], ![61612, -92799, -13572, 9916, 22584], ![103925, -158128, -22295, 18024, 39664], ![56690, -89432, -10974, 12411, 24756], ![91078, -141764, -18348, 18382, 37889]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI991N2 : Nat.card (O ⧸ I991N2) = 991 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI991N2)

lemma isPrimeI991N2 : Ideal.IsPrime I991N2 := prime_ideal_of_norm_prime hp991.out _ NI991N2
def MulI991N0 : IdealMulLeCertificate' Table 
  ![![-2254, 381, 234, 355, 153]] ![![2581, -1570, -226, -190, 404]]
  ![![-6752134, 4112573, 590758, 495081, -1058695]] where
 M := ![![![-6752134, 4112573, 590758, 495081, -1058695]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI991N1 : IdealMulLeCertificate' Table 
  ![![-6752134, 4112573, 590758, 495081, -1058695]] ![![-92111, -54688, -8144, 5646, 13102]]
  ![![991, 0, 0, 0, 0]] where
 M := ![![![46077536, 11415329, -5494104, -10933703, -12955343]]]
 hmul := by decide  
 g := ![![![![46496, 11519, -5544, -11033, -13073]]]]
 hle2 := by decide  


def PBC991 : ContainsPrimesAboveP 991 ![I991N0, I991N1, I991N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI991N0
    exact isPrimeI991N1
    exact isPrimeI991N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 991 (by decide) (𝕀 ⊙ MulI991N0 ⊙ MulI991N1)
instance hp997 : Fact (Nat.Prime 997) := {out := by norm_num}

def I997N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![34561, 20771, 3149, -2054, -4898]] i)))

def SI997N0: IdealEqSpanCertificate' Table ![![34561, 20771, 3149, -2054, -4898]] 
 ![![997, 0, 0, 0, 0], ![0, 997, 0, 0, 0], ![0, 0, 997, 0, 0], ![408, 643, 414, 1, 0], ![289, 453, 952, 0, 1]] where
  M :=![![![34561, 20771, 3149, -2054, -4898], ![58776, 34866, 5287, -3498, -8216], ![98592, 59345, 8998, -5858, -13992], ![54564, 32295, 4903, -3245, -7608], ![86814, 52165, 7909, -5156, -12295]]]
  hmulB := by decide  
  f := ![![![73, -13, -37, 6, 18]], ![![-216, 48, 47, -38, 24]], ![![-288, -107, 220, 142, -152]], ![![-228, -19, 106, 37, -40]], ![![-353, -84, 221, 120, -129]]]
  g := ![![![2295, 3571, 5533, -2054, -4898], ![3872, 6024, 9303, -3498, -8216], ![6552, 10195, 15802, -5858, -13992], ![3588, 5582, 8617, -3245, -7608], ![5761, 8964, 13889, -5156, -12295]]]
  hle1 := by decide   
  hle2 := by decide  


def P997P0 : CertificateIrreducibleZModOfList' 997 3 2 9 [54, 479, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [301, 140, 208], [658, 856, 789], [0, 1]]
 g := ![![[456, 722, 305], [158, 957], [864, 183, 555], [416, 767], [682, 67], [190, 401, 994], [504, 772, 562], [385, 475, 447], [1]], ![[580, 563, 166, 16], [459, 858], [70, 620, 912, 970], [70, 983], [423, 308], [349, 0, 320, 554], [33, 174, 141, 73], [272, 361, 186, 767], [545, 315, 935, 987]], ![[694, 76, 871, 89], [805, 983], [507, 552, 264, 828], [239, 208], [303, 867], [393, 579, 409, 441], [275, 40, 783, 71], [278, 737, 919, 279], [930, 810, 877, 10]]]
 h' := ![![[301, 140, 208], [773, 977, 91], [203, 294, 720], [549, 26, 620], [413, 289, 955], [707, 470, 678], [700, 716, 388], [147, 227, 791], [943, 518, 959], [0, 1]], ![[658, 856, 789], [214, 465, 955], [279, 435, 509], [421, 226, 739], [520, 837, 232], [775, 407, 168], [286, 777, 502], [214, 187, 490], [440, 19, 441], [301, 140, 208]], ![[0, 1], [456, 552, 948], [892, 268, 765], [912, 745, 635], [816, 868, 807], [226, 120, 151], [960, 501, 107], [11, 583, 713], [183, 460, 594], [658, 856, 789]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [670, 900], []]
 b := ![[], [741, 603, 475], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI997N0 : CertifiedPrimeIdeal' SI997N0 997 where
  n := 3
  hpos := by decide
  P := [54, 479, 38, 1]
  hirr := P997P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![71705, -7120, -40421, -10797, 28207]
  a := ![-1, -4, -2, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3686, -5860, -22491, -10797, 28207]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI997N0 : Ideal.IsPrime I997N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI997N0 B_one_repr
lemma NI997N0 : Nat.card (O ⧸ I997N0) = 991026973 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI997N0

def I997N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73, 13, 37, -6, -18]] i)))

def SI997N1: IdealEqSpanCertificate' Table ![![-73, 13, 37, -6, -18]] 
 ![![997, 0, 0, 0, 0], ![0, 997, 0, 0, 0], ![352, 169, 1, 0, 0], ![166, 851, 0, 1, 0], ![63, 63, 0, 0, 1]] where
  M :=![![![-73, 13, 37, -6, -18], ![216, -48, -47, 38, -24], ![288, 107, -220, -142, 152], ![-1020, 205, 523, -87, -272], ![1014, -129, -299, 64, -17]]]
  hmulB := by decide  
  f := ![![![-34561, -20771, -3149, 2054, 4898]], ![![-58776, -34866, -5287, 3498, 8216]], ![![-22264, -13303, -2017, 1324, 3136]], ![![-55978, -33251, -5042, 3331, 7836]], ![![-5985, -3568, -541, 356, 841]]]
  g := ![![![-11, 0, 37, -6, -18], ![12, -23, -47, 38, -24], ![92, 149, -220, -142, 152], ![-154, 3, 523, -87, -272], ![97, -3, -299, 64, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P997P1 : CertificateIrreducibleZModOfList' 997 2 2 9 [213, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [989, 996], [0, 1]]
 g := ![![[763, 220], [420], [772, 580], [480], [306], [961, 794], [964, 100], [536, 267], [989, 1]], ![[0, 777], [420], [120, 417], [480], [306], [591, 203], [164, 897], [394, 730], [981, 996]]]
 h' := ![![[989, 996], [46, 255], [69, 438], [777, 885], [773, 597], [689, 165], [50, 781], [487, 10], [707, 848], [0, 1]], ![[0, 1], [0, 742], [553, 559], [676, 112], [982, 400], [366, 832], [781, 216], [407, 987], [902, 149], [989, 996]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [415]]
 b := ![[], [830, 706]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI997N1 : CertifiedPrimeIdeal' SI997N1 997 where
  n := 2
  hpos := by decide
  P := [213, 8, 1]
  hirr := P997P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-76446, -10386, 22391, 12069, 5610]
  a := ![3, -11, -14, -1, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10346, -14462, 22391, 12069, 5610]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI997N1 : Ideal.IsPrime I997N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI997N1 B_one_repr
lemma NI997N1 : Nat.card (O ⧸ I997N1) = 994009 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI997N1
def MulI997N0 : IdealMulLeCertificate' Table 
  ![![34561, 20771, 3149, -2054, -4898]] ![![-73, 13, 37, -6, -18]]
  ![![997, 0, 0, 0, 0]] where
 M := ![![![-997, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC997 : ContainsPrimesAboveP 997 ![I997N0, I997N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI997N0
    exact isPrimeI997N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 997 (by decide) (𝕀 ⊙ MulI997N0)
instance hp1009 : Fact (Nat.Prime 1009) := {out := by norm_num}

def I1009N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7268, 576, -1603, -2349, -2537]] i)))

def SI1009N0: IdealEqSpanCertificate' Table ![![7268, 576, -1603, -2349, -2537]] 
 ![![1009, 0, 0, 0, 0], ![0, 1009, 0, 0, 0], ![370, 375, 1, 0, 0], ![246, 503, 0, 1, 0], ![576, 11, 0, 0, 1]] where
  M :=![![![7268, 576, -1603, -2349, -2537], ![30444, 5477, -4874, -8280, -9396], ![112752, 24454, -15547, -28540, -33120], ![183498, 43574, -23036, -44527, -52382], ![221133, 51748, -28217, -54049, -63436]]]
  hmulB := by decide  
  f := ![![![558182, -339688, -48795, -41011, 87331]], ![![-1047972, 637729, 91658, 77072, -164044]], ![![-182848, 111265, 16001, 13462, -28638]], ![![-387654, 235897, 33912, 28519, -60692]], ![![308553, -187773, -26973, -22669, 48274]]]
  g := ![![![2616, 1795, -1603, -2349, -2537], ![9200, 6047, -4874, -8280, -9396], ![31678, 20391, -15547, -28540, -33120], ![49388, 31373, -23036, -44527, -52382], ![59957, 38174, -28217, -54049, -63436]]]
  hle1 := by decide   
  hle2 := by decide  


def P1009P0 : CertificateIrreducibleZModOfList' 1009 2 2 9 [369, 908, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [101, 1008], [0, 1]]
 g := ![![[522, 834], [635], [886], [522], [880, 56], [551, 222], [746, 337], [270, 979], [101, 1]], ![[0, 175], [635], [886], [522], [482, 953], [775, 787], [477, 672], [267, 30], [202, 1008]]]
 h' := ![![[101, 1008], [967, 420], [741, 309], [506, 208], [178, 391], [499, 159], [183, 952], [261, 58], [64, 751], [0, 1]], ![[0, 1], [0, 589], [671, 700], [325, 801], [318, 618], [414, 850], [480, 57], [65, 951], [240, 258], [101, 1008]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [975]]
 b := ![[], [354, 992]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI1009N0 : CertifiedPrimeIdeal' SI1009N0 1009 where
  n := 2
  hpos := by decide
  P := [369, 908, 1]
  hirr := P1009P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16197, -7540, -1363, 765, 19238]
  a := ![1, -6, -8, -2, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10685, -92, -1363, 765, 19238]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI1009N0 : Ideal.IsPrime I1009N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI1009N0 B_one_repr
lemma NI1009N0 : Nat.card (O ⧸ I1009N0) = 1018081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI1009N0

def I1009N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67, -17, 3, 12, 22]] i)))

def SI1009N1: IdealEqSpanCertificate' Table ![![-67, -17, 3, 12, 22]] 
 ![![1009, 0, 0, 0, 0], ![0, 1009, 0, 0, 0], ![632, 374, 1, 0, 0], ![878, 504, 0, 1, 0], ![395, 453, 0, 0, 1]] where
  M :=![![![-67, -17, 3, 12, 22], ![-264, -54, 47, 50, 48], ![-576, -219, 38, 190, 200], ![-1068, -237, 77, 213, 356], ![-1422, -335, 221, 324, 325]]]
  hmulB := by decide  
  f := ![![![-21799, 13211, 1901, 1600, -3398]], ![![40776, -24896, -3581, -2994, 6400]], ![![1384, -907, -130, -102, 232]], ![![1450, -971, -139, -107, 248]], ![![9721, -5974, -859, -714, 1535]]]
  g := ![![![-21, -17, 3, 12, 22], ![-92, -64, 47, 50, 48], ![-268, -199, 38, 190, 200], ![-374, -295, 77, 213, 356], ![-549, -390, 221, 324, 325]]]
  hle1 := by decide   
  hle2 := by decide  


def P1009P1 : CertificateIrreducibleZModOfList' 1009 2 2 9 [808, 681, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [328, 1008], [0, 1]]
 g := ![![[599, 758], [861], [384], [40], [819, 639], [118, 893], [480, 576], [642, 405], [328, 1]], ![[0, 251], [861], [384], [40], [539, 370], [412, 116], [725, 433], [294, 604], [656, 1008]]]
 h' := ![![[328, 1008], [665, 887], [563, 319], [874, 626], [152, 324], [511, 395], [625, 778], [899, 985], [343, 831], [0, 1]], ![[0, 1], [0, 122], [259, 690], [366, 383], [479, 685], [919, 614], [532, 231], [90, 24], [481, 178], [328, 1008]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [311]]
 b := ![[], [732, 660]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI1009N1 : CertifiedPrimeIdeal' SI1009N1 1009 where
  n := 2
  hpos := by decide
  P := [808, 681, 1]
  hirr := P1009P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2312, 1172, 1852, 916, -4176]
  a := ![4, 2, 2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-320, 732, 1852, 916, -4176]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI1009N1 : Ideal.IsPrime I1009N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI1009N1 B_one_repr
lemma NI1009N1 : Nat.card (O ⧸ I1009N1) = 1018081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI1009N1

def I1009N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1624, 1586, 517, 217, 19]] i)))

def SI1009N2: IdealEqSpanCertificate' Table ![![1624, 1586, 517, 217, 19]] 
 ![![1009, 0, 0, 0, 0], ![260, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![489, 0, 0, 1, 0], ![65, 0, 0, 0, 1]] where
  M :=![![![1624, 1586, 517, 217, 19], ![-228, 1943, 1228, 1072, 868], ![-10416, 796, 3271, 4192, 4288], ![-25614, -4496, 4168, 7023, 7950], ![-29115, -4246, 5257, 8423, 9384]]]
  hmulB := by decide  
  f := ![![![-365054, 221030, 32769, 26499, -57129]], ![![-93388, 56543, 8384, 6780, -14616]], ![![-2346, 1430, 202, 169, -363]], ![![-176100, 106606, 15821, 12778, -27559]], ![![-24361, 14760, 2180, 1774, -3815]]]
  g := ![![![-515, 1586, 517, 217, 19], ![-1080, 1943, 1228, 1072, 868], ![-2533, 796, 3271, 4192, 4288], ![-2795, -4496, 4168, 7023, 7950], ![-3637, -4246, 5257, 8423, 9384]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI1009N2 : Nat.card (O ⧸ I1009N2) = 1009 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI1009N2)

lemma isPrimeI1009N2 : Ideal.IsPrime I1009N2 := prime_ideal_of_norm_prime hp1009.out _ NI1009N2
def MulI1009N0 : IdealMulLeCertificate' Table 
  ![![7268, 576, -1603, -2349, -2537]] ![![-67, -17, 3, 12, 22]]
  ![![6400654, 1603005, -753588, -1510879, -1793825]] where
 M := ![![![6400654, 1603005, -753588, -1510879, -1793825]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI1009N1 : IdealMulLeCertificate' Table 
  ![![6400654, 1603005, -753588, -1510879, -1793825]] ![![1624, 1586, 517, 217, 19]]
  ![![1009, 0, 0, 0, 0]] where
 M := ![![![108805419145, 27075712845, -12914839787, -25771968810, -30563106428]]]
 hmul := by decide  
 g := ![![![![107834905, 26834205, -12799643, -25542090, -30290492]]]]
 hle2 := by decide  


def PBC1009 : ContainsPrimesAboveP 1009 ![I1009N0, I1009N1, I1009N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI1009N0
    exact isPrimeI1009N1
    exact isPrimeI1009N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 1009 (by decide) (𝕀 ⊙ MulI1009N0 ⊙ MulI1009N1)
instance hp1013 : Fact (Nat.Prime 1013) := {out := by norm_num}

def I1013N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-338371, 205877, 29613, 24852, -52944]] i)))

def SI1013N0: IdealEqSpanCertificate' Table ![![-338371, 205877, 29613, 24852, -52944]] 
 ![![1013, 0, 0, 0, 0], ![0, 1013, 0, 0, 0], ![350, 965, 1, 0, 0], ![296, 543, 0, 1, 0], ![780, 741, 0, 0, 1]] where
  M :=![![![-338371, 205877, 29613, 24852, -52944], ![635328, -386554, -55603, -46662, 99408], ![-1192896, 725795, 104402, 87610, -186648], ![802224, -488099, -70207, -58915, 125516], ![-814164, 495371, 71249, 59794, -127387]]]
  hmulB := by decide  
  f := ![![![18361, 10901, 1627, -1108, -2600]], ![![31200, 18496, 2717, -1946, -4432]], ![![36118, 21417, 3155, -2240, -5128]], ![![22120, 13117, 1934, -1369, -3140]], ![![37008, 21951, 3244, -2280, -5251]]]
  g := ![![![22939, -2600, 29613, 24852, -52944], ![-43070, 4883, -55603, -46662, 99408], ![80868, -9169, 104402, 87610, -186648], ![-54382, 6165, -70207, -58915, 125516], ![55194, -6253, 71249, 59794, -127387]]]
  hle1 := by decide   
  hle2 := by decide  


def P1013P0 : CertificateIrreducibleZModOfList' 1013 2 2 9 [830, 825, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [188, 1012], [0, 1]]
 g := ![![[776, 858], [873], [888, 806], [780], [317, 240], [900, 998], [764, 717], [692, 119], [188, 1]], ![[0, 155], [873], [466, 207], [780], [865, 773], [106, 15], [831, 296], [778, 894], [376, 1012]]]
 h' := ![![[188, 1012], [180, 387], [424, 845], [884, 364], [270, 502], [594, 647], [18, 441], [11, 354], [975, 72], [0, 1]], ![[0, 1], [0, 626], [243, 168], [432, 649], [437, 511], [670, 366], [873, 572], [718, 659], [329, 941], [188, 1012]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [982]]
 b := ![[], [444, 491]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI1013N0 : CertifiedPrimeIdeal' SI1013N0 1013 where
  n := 2
  hpos := by decide
  P := [830, 825, 1]
  hirr := P1013P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1024962, -113607, 260617, 139538, 51182]
  a := ![7, 23, 45, -23, -136]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-171240, -360616, 260617, 139538, 51182]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI1013N0 : Ideal.IsPrime I1013N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI1013N0 B_one_repr
lemma NI1013N0 : Nat.card (O ⧸ I1013N0) = 1026169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI1013N0

def I1013N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1730651, 1052988, 151460, 127108, -270788]] i)))

def SI1013N1: IdealEqSpanCertificate' Table ![![-1730651, 1052988, 151460, 127108, -270788]] 
 ![![1013, 0, 0, 0, 0], ![0, 1013, 0, 0, 0], ![42, 392, 1, 0, 0], ![885, 684, 0, 1, 0], ![943, 243, 0, 0, 1]] where
  M :=![![![-1730651, 1052988, 151460, 127108, -270788], ![3249456, -1977087, -284380, -238656, 508432], ![-6101184, 3712164, 533953, 448104, -954624], ![4103016, -2496436, -359080, -301343, 641992], ![-4164204, 2533628, 364436, 305844, -651547]]]
  hmulB := by decide  
  f := ![![![-2143, -1516, -164, 268, 212]], ![![-2544, -2363, -1204, 96, 1072]], ![![-1086, -980, -471, 48, 424]], ![![-3591, -2924, -956, 301, 908]], ![![-2609, -1981, -444, 272, 457]]]
  g := ![![![133041, -78440, 151460, 127108, -270788], ![-249800, 147277, -284380, -238656, 508432], ![469014, -276532, 533953, 448104, -954624], ![-315425, 185960, -359080, -301343, 641992], ![320105, -188743, 364436, 305844, -651547]]]
  hle1 := by decide   
  hle2 := by decide  


def P1013P1 : CertificateIrreducibleZModOfList' 1013 2 2 9 [367, 110, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [903, 1012], [0, 1]]
 g := ![![[257, 472], [864], [787, 557], [978], [529, 397], [878, 225], [310, 837], [675, 641], [903, 1]], ![[0, 541], [864], [297, 456], [978], [418, 616], [440, 788], [423, 176], [62, 372], [793, 1012]]]
 h' := ![![[903, 1012], [162, 333], [889, 77], [699, 348], [353, 84], [921, 481], [699, 998], [460, 695], [863, 590], [0, 1]], ![[0, 1], [0, 680], [523, 936], [913, 665], [230, 929], [687, 532], [323, 15], [998, 318], [795, 423], [903, 1012]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [226]]
 b := ![[], [137, 113]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI1013N1 : CertifiedPrimeIdeal' SI1013N1 1013 where
  n := 2
  hpos := by decide
  P := [367, 110, 1]
  hirr := P1013P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-65057, -7446, 16086, 9296, 5782]
  a := ![1, 7, 12, -5, -35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14235, -13896, 16086, 9296, 5782]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI1013N1 : Ideal.IsPrime I1013N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI1013N1 B_one_repr
lemma NI1013N1 : Nat.card (O ⧸ I1013N1) = 1026169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI1013N1

def I1013N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![188, -113, -18, -15, 31]] i)))

def SI1013N2: IdealEqSpanCertificate' Table ![![188, -113, -18, -15, 31]] 
 ![![1013, 0, 0, 0, 0], ![669, 1, 0, 0, 0], ![185, 0, 1, 0, 0], ![589, 0, 0, 1, 0], ![517, 0, 0, 0, 1]] where
  M :=![![![188, -113, -18, -15, 31], ![-372, 216, 41, 26, -60], ![720, -417, -76, -38, 104], ![-438, 285, 17, 15, -46], ![405, -275, -10, -27, 52]]]
  hmulB := by decide  
  f := ![![![17494, 9715, 1144, -1417, -2761]], ![![11586, 6433, 757, -939, -1829]], ![![3262, 1806, 210, -267, -517]], ![![10232, 5672, 663, -834, -1619]], ![![9011, 4992, 582, -736, -1427]]]
  g := ![![![71, -113, -18, -15, 31], ![-135, 216, 41, 26, -60], ![259, -417, -76, -38, 104], ![-177, 285, 17, 15, -46], ![173, -275, -10, -27, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI1013N2 : Nat.card (O ⧸ I1013N2) = 1013 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI1013N2)

lemma isPrimeI1013N2 : Ideal.IsPrime I1013N2 := prime_ideal_of_norm_prime hp1013.out _ NI1013N2
def MulI1013N0 : IdealMulLeCertificate' Table 
  ![![-338371, 205877, 29613, 24852, -52944]] ![![-1730651, 1052988, 151460, 127108, -270788]]
  ![![1396353770849, -849590858619, -122203578475, -102555319600, 218482270252]] where
 M := ![![![1396353770849, -849590858619, -122203578475, -102555319600, 218482270252]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI1013N1 : IdealMulLeCertificate' Table 
  ![![1396353770849, -849590858619, -122203578475, -102555319600, 218482270252]] ![![188, -113, -18, -15, 31]]
  ![![1013, 0, 0, 0, 0]] where
 M := ![![![623980281260740, -379651599748866, -54608384250281, -45828283995583, 97631869006763]]]
 hmul := by decide  
 g := ![![![![615972636980, -374779466682, -53907585637, -45240161891, 96378942751]]]]
 hle2 := by decide  


def PBC1013 : ContainsPrimesAboveP 1013 ![I1013N0, I1013N1, I1013N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI1013N0
    exact isPrimeI1013N1
    exact isPrimeI1013N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 1013 (by decide) (𝕀 ⊙ MulI1013N0 ⊙ MulI1013N1)
instance hp1019 : Fact (Nat.Prime 1019) := {out := by norm_num}

def I1019N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2432, -2354, -1011, 205, 857]] i)))

def SI1019N0: IdealEqSpanCertificate' Table ![![-2432, -2354, -1011, 205, 857]] 
 ![![1019, 0, 0, 0, 0], ![0, 1019, 0, 0, 0], ![0, 0, 1019, 0, 0], ![0, 0, 0, 1019, 0], ![405, 480, 478, 785, 1]] where
  M :=![![![-2432, -2354, -1011, 205, 857], ![-10284, -2791, 664, -308, 820], ![-9840, -8492, 1105, 2968, -1232], ![12534, -5072, -10010, 27, 5526], ![-24069, -2938, 4963, -835, -384]]]
  hmulB := by decide  
  f := ![![![-1774, 1086, 155, 129, -281]], ![![3372, -2029, -296, -252, 516]], ![![-6192, 3844, 539, 440, -1008]], ![![4362, -2536, -386, -343, 622]], ![![1335, -672, -122, -125, 137]]]
  g := ![![![-343, -406, -403, -660, 857], ![-336, -389, -384, -632, 820], ![480, 572, 579, 952, -1232], ![-2184, -2608, -2602, -4257, 5526], ![129, 178, 185, 295, -384]]]
  hle1 := by decide   
  hle2 := by decide  


def P1019P0 : CertificateIrreducibleZModOfList' 1019 4 2 9 [228, 982, 556, 296, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [144, 827, 384, 476], [101, 68, 882, 113], [478, 123, 772, 430], [0, 1]]
 g := ![![[53, 198, 688, 316], [756, 160, 334, 437], [145, 117, 124], [93, 974, 1009, 501], [238, 914, 183, 73], [245, 313, 13, 279], [907, 766, 85, 601], [285, 445, 723, 1], []], ![[591, 83, 762, 491, 316, 178], [1004, 951, 631, 884, 355, 926], [849, 876, 368], [698, 142, 173, 989, 538, 302], [971, 299, 174, 535, 740, 423], [986, 1005, 789, 63, 191, 260], [252, 901, 732, 78, 278, 949], [806, 27, 65, 342, 890, 764], [797, 812, 680, 301, 472, 235]], ![[92, 362, 502, 153, 343, 276], [300, 840, 710, 660, 3, 668], [708, 35, 814], [572, 176, 104, 409, 852, 206], [949, 275, 918, 136, 162, 979], [207, 424, 852, 789, 252, 402], [198, 936, 295, 62, 465, 192], [88, 718, 80, 232, 604, 42], [458, 532, 149, 14, 844, 1012]], ![[940, 963, 111, 810, 445, 532], [503, 415, 801, 418, 698, 719], [466, 840, 507], [164, 175, 259, 679, 977, 613], [441, 254, 639, 791, 347, 739], [749, 192, 993, 547, 923, 736], [166, 810, 853, 344, 767, 65], [588, 1014, 520, 747, 811, 71], [231, 942, 70, 222, 761, 544]]]
 h' := ![![[144, 827, 384, 476], [862, 240, 639, 112], [889, 670, 556, 496], [195, 268, 621, 782], [762, 736, 658, 712], [185, 524, 82, 748], [61, 203, 152, 865], [236, 795, 899, 443], [0, 0, 0, 1], [0, 1]], ![[101, 68, 882, 113], [870, 346, 319, 526], [358, 795, 321, 868], [256, 390, 744, 849], [262, 789, 395, 144], [893, 828, 1012, 172], [258, 63, 708, 971], [188, 863, 619, 561], [999, 23, 245, 518], [144, 827, 384, 476]], ![[478, 123, 772, 430], [871, 431, 495, 470], [970, 643, 278, 207], [231, 917, 349, 627], [102, 738, 196, 934], [503, 59, 636, 192], [117, 672, 1, 184], [818, 199, 465, 284], [625, 813, 601, 976], [101, 68, 882, 113]], ![[0, 1], [805, 2, 585, 930], [531, 949, 883, 467], [877, 463, 324, 799], [508, 794, 789, 248], [62, 627, 308, 926], [915, 81, 158, 18], [692, 181, 55, 750], [271, 183, 173, 543], [478, 123, 772, 430]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [991, 92, 4], []]
 b := ![[], [], [265, 595, 759, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI1019N0 : CertifiedPrimeIdeal' SI1019N0 1019 where
  n := 4
  hpos := by decide
  P := [228, 982, 556, 296, 1]
  hirr := P1019P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6906807105, -1610673684, 872370853, 1565026747, 1877391662]
  a := ![3, 2, -5, 11, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-752944485, -885926076, -879804557, -1444737417, 1877391662]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI1019N0 : Ideal.IsPrime I1019N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI1019N0 B_one_repr
lemma NI1019N0 : Nat.card (O ⧸ I1019N0) = 1078193566321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI1019N0

def I1019N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1774, -1086, -155, -129, 281]] i)))

def SI1019N1: IdealEqSpanCertificate' Table ![![1774, -1086, -155, -129, 281]] 
 ![![1019, 0, 0, 0, 0], ![936, 1, 0, 0, 0], ![244, 0, 1, 0, 0], ![487, 0, 0, 1, 0], ![526, 0, 0, 0, 1]] where
  M :=![![![1774, -1086, -155, -129, 281], ![-3372, 2029, 296, 252, -516], ![6192, -3844, -539, -440, 1008], ![-4362, 2536, 386, 343, -622], ![4119, -2650, -355, -275, 718]]]
  hmulB := by decide  
  f := ![![![2432, 2354, 1011, -205, -857]], ![![2244, 2165, 928, -188, -788]], ![![592, 572, 241, -52, -204]], ![![1150, 1130, 493, -98, -415]], ![![1279, 1218, 517, -105, -442]]]
  g := ![![![953, -1086, -155, -129, 281], ![-1792, 2029, 296, 252, -516], ![3356, -3844, -539, -440, 1008], ![-2269, 2536, 386, 343, -622], ![2284, -2650, -355, -275, 718]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI1019N1 : Nat.card (O ⧸ I1019N1) = 1019 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI1019N1)

lemma isPrimeI1019N1 : Ideal.IsPrime I1019N1 := prime_ideal_of_norm_prime hp1019.out _ NI1019N1
def MulI1019N0 : IdealMulLeCertificate' Table 
  ![![-2432, -2354, -1011, 205, 857]] ![![1774, -1086, -155, -129, 281]]
  ![![1019, 0, 0, 0, 0]] where
 M := ![![![-1019, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC1019 : ContainsPrimesAboveP 1019 ![I1019N0, I1019N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI1019N0
    exact isPrimeI1019N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 1019 (by decide) (𝕀 ⊙ MulI1019N0)


lemma PB1705I18_primes (p : ℕ) :
  p ∈ Set.range ![967, 971, 977, 983, 991, 997, 1009, 1013, 1019] ↔ Nat.Prime p ∧ 953 < p ∧ p ≤ 1019 := by
  rw [← List.mem_ofFn']
  convert primes_range 953 1019 (by omega)

def PB1705I18 : PrimesBelowBoundCertificateInterval O 953 1019 1705 where
  m := 9
  g := ![2, 2, 3, 3, 3, 2, 3, 3, 2]
  P := ![967, 971, 977, 983, 991, 997, 1009, 1013, 1019]
  hP := PB1705I18_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I967N0, I967N1]
    · exact ![I971N0, I971N1]
    · exact ![I977N0, I977N1, I977N2]
    · exact ![I983N0, I983N1, I983N2]
    · exact ![I991N0, I991N1, I991N2]
    · exact ![I997N0, I997N1]
    · exact ![I1009N0, I1009N1, I1009N2]
    · exact ![I1013N0, I1013N1, I1013N2]
    · exact ![I1019N0, I1019N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC967
    · exact PBC971
    · exact PBC977
    · exact PBC983
    · exact PBC991
    · exact PBC997
    · exact PBC1009
    · exact PBC1013
    · exact PBC1019
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![904231063, 935089]
    · exact ![915498611, 942841]
    · exact ![932574833, 977, 977]
    · exact ![949862087, 983, 983]
    · exact ![973242271, 991, 991]
    · exact ![991026973, 994009]
    · exact ![1018081, 1018081, 1009]
    · exact ![1026169, 1026169, 1013]
    · exact ![1078193566321, 1019]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI967N0
      exact NI967N1
    · dsimp ; intro j
      fin_cases j
      exact NI971N0
      exact NI971N1
    · dsimp ; intro j
      fin_cases j
      exact NI977N0
      exact NI977N1
      exact NI977N2
    · dsimp ; intro j
      fin_cases j
      exact NI983N0
      exact NI983N1
      exact NI983N2
    · dsimp ; intro j
      fin_cases j
      exact NI991N0
      exact NI991N1
      exact NI991N2
    · dsimp ; intro j
      fin_cases j
      exact NI997N0
      exact NI997N1
    · dsimp ; intro j
      fin_cases j
      exact NI1009N0
      exact NI1009N1
      exact NI1009N2
    · dsimp ; intro j
      fin_cases j
      exact NI1013N0
      exact NI1013N1
      exact NI1013N2
    · dsimp ; intro j
      fin_cases j
      exact NI1019N0
      exact NI1019N1
  β := ![I977N1, I977N2, I983N1, I983N2, I991N1, I991N2, I1009N2, I1013N2, I1019N1]
  Il := ![[], [], [I977N1, I977N2], [I983N1, I983N2], [I991N1, I991N2], [], [I1009N2], [I1013N2], [I1019N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
