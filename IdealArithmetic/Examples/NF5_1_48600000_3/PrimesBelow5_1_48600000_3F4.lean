
import IdealArithmetic.Examples.NF5_1_48600000_3.RI5_1_48600000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-145, -443, -427, -30, -124]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-145, -443, -427, -30, -124]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![134, 24, 22, 1, 0], ![8, 75, 126, 0, 1]] where
  M :=![![![-145, -443, -427, -30, -124], ![-248, -765, -746, -50, -214], ![-428, -1318, -1297, -108, -364], ![-150, -465, -477, -43, -162], ![-208, -630, -578, 6, -205]]]
  hmulB := by decide  
  f := ![![![471, 401, -351, 68, -134]], ![![-268, -199, 184, -34, 70]], ![![140, 82, -85, 16, -32]], ![![380, 323, -283, 55, -108]], ![![8, -9, 2, 0, 1]]]
  g := ![![![31, 61, 101, -30, -124], ![52, 105, 174, -50, -214], ![108, 182, 299, -108, -364], ![44, 81, 133, -43, -162], ![4, 93, 160, 6, -205]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [116, 10, 73, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 117, 50], [75, 39, 107], [0, 1]]
 g := ![![[50, 95, 14], [67, 67], [30, 135, 47], [140, 109, 76], [97, 84, 47], [84, 1], []], ![[117, 86, 81, 142], [35, 105], [4, 27, 42, 131], [155, 27, 79, 104], [85, 8, 37, 107], [24, 108], [16, 145]], ![[32, 1, 30, 38], [130, 57], [89, 54, 148, 38], [139, 61, 143, 97], [11, 93, 48, 78], [148, 30], [116, 145]]]
 h' := ![![[9, 117, 50], [126, 71, 93], [131, 105, 58], [88, 121, 138], [52, 62, 95], [147, 143, 138], [0, 0, 1], [0, 1]], ![[75, 39, 107], [69, 31, 112], [19, 62, 133], [48, 33, 128], [132, 2, 54], [148, 95, 129], [109, 41, 39], [9, 117, 50]], ![[0, 1], [153, 55, 109], [2, 147, 123], [10, 3, 48], [70, 93, 8], [149, 76, 47], [19, 116, 117], [75, 39, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 84], []]
 b := ![[], [95, 29, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [116, 10, 73, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1688858, -2722593, 3761443, 10929952, -12307542]
  a := ![0, -1, -4, 5, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8712370, 4191237, 8369763, 10929952, -12307542]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![471, 401, -351, 68, -134]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![471, 401, -351, 68, -134]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![89, 114, 1, 0, 0], ![142, 5, 0, 1, 0], ![51, 70, 0, 0, 1]] where
  M :=![![![471, 401, -351, 68, -134], ![-268, -199, 184, -34, 70], ![140, 82, -85, 16, -32], ![-102, -51, 57, -13, 24], ![-52, -28, 32, -10, 11]]]
  hmulB := by decide  
  f := ![![![-145, -443, -427, -30, -124]], ![![-248, -765, -746, -50, -214]], ![![-265, -815, -792, -54, -228]], ![![-140, -428, -413, -29, -120]], ![![-159, -489, -475, -32, -137]]]
  g := ![![![184, 315, -351, 68, -134], ![-98, -165, 184, -34, 70], ![45, 76, -85, 16, -32], ![-29, -52, 57, -13, 24], ![-13, -28, 32, -10, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P1 : CertificateIrreducibleZModOfList' 157 2 2 7 [85, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [147, 156], [0, 1]]
 g := ![![[74, 10], [101], [108, 90], [90, 58], [60, 3], [100], [1]], ![[131, 147], [101], [150, 67], [138, 99], [30, 154], [100], [1]]]
 h' := ![![[147, 156], [31, 18], [83, 27], [43, 103], [81, 134], [138, 72], [72, 147], [0, 1]], ![[0, 1], [8, 139], [127, 130], [112, 54], [154, 23], [46, 85], [15, 10], [147, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123]]
 b := ![[], [72, 140]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N1 : CertifiedPrimeIdeal' SI157N1 157 where
  n := 2
  hpos := by decide
  P := [85, 10, 1]
  hirr := P157P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1366, -4988, 4273, 2473, 2359]
  a := ![3, -64, 1, -3, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5434, -4265, 4273, 2473, 2359]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N1 B_one_repr
lemma NI157N1 : Nat.card (O ⧸ I157N1) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-145, -443, -427, -30, -124]] ![![471, 401, -351, 68, -134]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2055, 1065, -1160, 178, -439]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![2055, 1065, -1160, 178, -439]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![32, 33, 39, 1, 0], ![113, 44, 14, 0, 1]] where
  M :=![![![2055, 1065, -1160, 178, -439], ![-878, -140, 344, -42, 95], ![190, -403, 109, 202, -31], ![-126, 219, -186, -101, 303], ![118, 609, -214, -730, 202]]]
  hmulB := by decide  
  f := ![![![648301, 1994247, 1945710, 137994, 562651]], ![![1125302, 3461556, 3377306, 239526, 976633]], ![![1953266, 6008467, 5862229, 415762, 1695211]], ![![826850, 2543484, 2481579, 175999, 717611]], ![![926453, 2849874, 2780512, 197200, 804055]]]
  g := ![![![282, 89, -12, 178, -439], ![-63, -18, 4, -42, 95], ![-17, -35, -45, 202, -31], ![-191, -60, -3, -101, 303], ![4, 97, 156, -730, 202]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [160, 110, 155, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 1, 108], [97, 161, 55], [0, 1]]
 g := ![![[79, 56, 14], [28, 102, 144], [81, 40], [137, 24], [47, 58], [117, 8, 1], []], ![[93, 10, 143, 20], [99, 9, 105, 112], [119, 24], [77, 131], [5, 85], [58, 40, 49, 106], [129, 91]], ![[25, 27, 123, 158], [64, 59, 128, 121], [137, 9], [120, 150], [132, 26], [68, 77, 106, 55], [19, 91]]]
 h' := ![![[74, 1, 108], [84, 43, 60], [131, 160, 12], [41, 133, 23], [114, 140, 26], [25, 31, 59], [0, 0, 1], [0, 1]], ![[97, 161, 55], [32, 150, 123], [12, 51, 141], [151, 155, 137], [75, 94, 72], [68, 52, 133], [158, 86, 161], [74, 1, 108]], ![[0, 1], [85, 133, 143], [147, 115, 10], [15, 38, 3], [151, 92, 65], [154, 80, 134], [12, 77, 1], [97, 161, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84, 107], []]
 b := ![[], [151, 146, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [160, 110, 155, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-156354, -279927, 313146, 908826, -908865]
  a := ![1, -3, -2, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![450693, 59625, -137466, 908826, -908865]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-239, -382, 584, 1692, -1980]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-239, -382, 584, 1692, -1980]] 
 ![![163, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![74, 0, 0, 1, 0], ![104, 0, 0, 0, 1]] where
  M :=![![![-239, -382, 584, 1692, -1980], ![-3960, -10139, 2182, 9664, 3096], ![6192, 11520, -11053, -33540, 32088], ![28992, 77556, -10284, -57007, -50310], ![-14212, -22482, 32338, 93764, -107317]]]
  hmulB := by decide  
  f := ![![![-57824148749, -177873614198, -173544406404, -12308150900, -50184730620]], ![![-4518006733, -13897899129, -13559642702, -961679676, -3921111780]], ![![-15968298246, -49120289412, -47924766733, -3398929836, -13858651848]], ![![-26644658830, -81961980724, -79967134848, -5671445039, -23124508614]], ![![-37383576380, -114996104330, -112197251710, -7957275796, -32444657653]]]
  g := ![![![369, -382, 584, 1692, -1980], ![-6265, -10139, 2182, 9664, 3096], ![-3138, 11520, -11053, -33540, 32088], ![55574, 77556, -10284, -57007, -50310], ![19002, -22482, 32338, 93764, -107317]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 25, -1, -26, -12]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![5, 25, -1, -26, -12]] 
 ![![163, 0, 0, 0, 0], ![75, 1, 0, 0, 0], ![80, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![80, 0, 0, 0, 1]] where
  M :=![![![5, 25, -1, -26, -12], ![-24, -55, 36, 122, -90], ![-180, -474, 71, 368, 276], ![366, 837, -375, -1309, 552], ![612, 1600, -280, -1354, -757]]]
  hmulB := by decide  
  f := ![![![-717613, -2207533, -2154035, -152740, -622902]], ![![-337833, -1039246, -1014057, -71906, -293244]], ![![-365468, -1124258, -1097009, -77788, -317232]], ![![-255825, -786972, -767898, -54451, -222060]], ![![-358280, -1102146, -1075434, -76258, -310993]]]
  g := ![![![4, 25, -1, -26, -12], ![9, -55, 36, 122, -90], ![-82, -474, 71, 368, 276], ![-12, 837, -375, -1309, 552], ![250, 1600, -280, -1354, -757]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![2055, 1065, -1160, 178, -439]] ![![-239, -382, 584, 1692, -1980]]
  ![![-491621, -1271679, 318496, 1365978, 163243]] where
 M := ![![![-491621, -1271679, 318496, 1365978, 163243]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![-491621, -1271679, 318496, 1365978, 163243]] ![![5, 25, -1, -26, -12]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![570585575, 1311197102, -580625397, -2034252388, 838700363]]]
 hmul := by decide  
 g := ![![![![3500525, 8044154, -3562119, -12480076, 5145401]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -3, 13, 0, 4]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-17, -3, 13, 0, 4]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![96, 3, 80, 1, 0], ![121, 41, 45, 0, 1]] where
  M :=![![![-17, -3, 13, 0, 4], ![8, 3, 6, 2, 4], ![8, 28, 5, -16, 10], ![6, 15, 9, -1, -24], ![-12, -28, 22, 54, -25]]]
  hmulB := by decide  
  f := ![![![-3, 15, -5, 2, -2]], ![![-4, -13, 12, -2, 4]], ![![8, 16, -5, 4, -2]], ![![2, 16, -5, 3, -2]], ![![-1, 12, -2, 2, -1]]]
  g := ![![![-3, -1, -1, 0, 4], ![-4, -1, -2, 2, 4], ![2, -2, 5, -16, 10], ![18, 6, 7, -1, -24], ![-13, 5, -19, 54, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [117, 88, 89, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [134, 66, 104], [111, 100, 63], [0, 1]]
 g := ![![[163, 81, 89], [123, 144, 64], [141, 62, 128], [45, 19], [24, 112], [151, 78, 1], []], ![[115, 149, 144, 117], [113, 48, 25, 71], [104, 147, 0, 60], [4, 157], [20, 36], [1, 61, 99, 91], [165, 128]], ![[19, 37, 109, 96], [130, 62, 153, 49], [137, 50, 122, 50], [108, 152], [86, 97], [151, 11, 52, 47], [39, 128]]]
 h' := ![![[134, 66, 104], [138, 10, 16], [36, 31, 8], [133, 92, 104], [87, 133, 112], [35, 131, 121], [0, 0, 1], [0, 1]], ![[111, 100, 63], [101, 108, 135], [78, 100, 16], [87, 146, 95], [87, 71, 149], [151, 46, 6], [154, 49, 100], [134, 66, 104]], ![[0, 1], [126, 49, 16], [77, 36, 143], [46, 96, 135], [149, 130, 73], [58, 157, 40], [76, 118, 66], [111, 100, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [159, 74], []]
 b := ![[], [88, 50, 86], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [117, 88, 89, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5138703, 11279820, -6052860, -20529692, 12206766]
  a := ![1, 19, 3, -7, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2987847, -2560530, 6509090, -20529692, 12206766]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -15, 5, -2, 2]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![3, -15, 5, -2, 2]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![73, 8, 1, 0, 0], ![89, 84, 0, 1, 0], ![75, 140, 0, 0, 1]] where
  M :=![![![3, -15, 5, -2, 2], ![4, 13, -12, 2, -4], ![-8, -16, 5, -4, 2], ![6, 9, -9, 5, -6], ![0, -2, -4, 6, -1]]]
  hmulB := by decide  
  f := ![![![17, 3, -13, 0, -4]], ![![-8, -3, -6, -2, -4]], ![![7, 1, -6, 0, -2]], ![![5, 0, -10, -1, -4]], ![![1, -1, -11, -2, -5]]]
  g := ![![![-2, -1, 5, -2, 2], ![6, 3, -12, 2, -4], ![-1, 0, 5, -4, 2], ![4, 3, -9, 5, -6], ![-1, -2, -4, 6, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P1 : CertificateIrreducibleZModOfList' 167 2 2 7 [28, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 166], [0, 1]]
 g := ![![[75, 6], [4, 7], [56, 98], [75], [75], [62, 31], [1]], ![[0, 161], [0, 160], [0, 69], [75], [75], [92, 136], [1]]]
 h' := ![![[71, 166], [55, 138], [102, 95], [115, 76], [85, 143], [101, 143], [139, 71], [0, 1]], ![[0, 1], [0, 29], [0, 72], [0, 91], [51, 24], [67, 24], [3, 96], [71, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132]]
 b := ![[], [162, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N1 : CertifiedPrimeIdeal' SI167N1 167 where
  n := 2
  hpos := by decide
  P := [28, 96, 1]
  hirr := P167P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2671, 4848, -5427, -15031, 14631]
  a := ![-1, 0, -2, 9, -20]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3828, -4416, -5427, -15031, 14631]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N1 B_one_repr
lemma NI167N1 : Nat.card (O ⧸ I167N1) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-17, -3, 13, 0, 4]] ![![3, -15, 5, -2, 2]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![-167, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0, 0, 0]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![0, 0, 0, 0, 173]] where
  M :=![![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![0, 0, 0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 5 2 7 [165, 145, 141, 128, 62, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 48, 40, 10, 36], [153, 34, 76, 121, 159], [66, 134, 118, 8, 29], [58, 129, 112, 34, 122], [0, 1]]
 g := ![![[109, 110, 81, 50, 130], [2, 103, 155, 140], [76, 83, 134, 11, 152], [7, 81, 5, 83, 88], [115, 133, 22, 38], [1], []], ![[75, 166, 127, 57, 120, 87, 44, 139], [172, 123, 17, 148], [126, 85, 160, 148, 112, 95, 13, 124], [171, 93, 104, 21, 58, 33, 106, 67], [109, 45, 152, 157], [164, 73, 8, 149, 139, 136, 0, 36], [102, 168, 121, 85]], ![[57, 32, 103, 40, 79, 90, 56, 151], [10, 59, 106, 106], [50, 116, 39, 94, 128, 169, 33, 142], [78, 93, 169, 64, 154, 0, 93, 137], [61, 47, 46, 52], [94, 66, 65, 164, 3, 4, 96, 167], [18, 97, 30, 23]], ![[83, 72, 27, 151, 102, 40, 58, 159], [31, 16, 138, 137], [67, 105, 50, 101, 98, 90, 123, 148], [140, 24, 152, 125, 54, 155, 129, 118], [23, 67, 156, 13], [126, 84, 116, 121, 142, 47, 97, 10], [45, 22, 49, 149]], ![[34, 78, 127, 66, 52, 27, 161, 117], [59, 116, 64, 77], [119, 80, 116, 99, 36, 81, 19, 167], [128, 118, 108, 86, 93, 83, 91, 78], [21, 107, 39, 77], [57, 40, 22, 43, 80, 163, 160, 142], [149, 68, 139, 6]]]
 h' := ![![[7, 48, 40, 10, 36], [152, 72, 169, 21, 86], [89, 46, 157, 121, 113], [56, 127, 96, 151, 49], [119, 61, 53, 61, 61], [8, 28, 32, 45, 111], [0, 0, 1], [0, 1]], ![[153, 34, 76, 121, 159], [143, 120, 59, 33, 132], [18, 169, 42, 154, 54], [164, 89, 140, 35, 151], [1, 65, 112, 112, 45], [101, 159, 42, 77, 26], [0, 28, 36, 22, 172], [7, 48, 40, 10, 36]], ![[66, 134, 118, 8, 29], [25, 124, 158, 143, 140], [34, 62, 1, 9, 25], [1, 144, 46, 35, 165], [52, 152, 117, 24, 158], [16, 91, 107, 109, 15], [25, 93, 91, 76, 41], [153, 34, 76, 121, 159]], ![[58, 129, 112, 34, 122], [62, 165, 83, 36, 75], [92, 66, 88, 53, 39], [3, 172, 24, 112, 14], [128, 141, 153, 168, 4], [64, 50, 161, 155, 79], [45, 94, 169, 86, 135], [66, 134, 118, 8, 29]], ![[0, 1], [7, 38, 50, 113, 86], [153, 3, 58, 9, 115], [5, 160, 40, 13, 140], [24, 100, 84, 154, 78], [78, 18, 4, 133, 115], [58, 131, 49, 162, 171], [58, 129, 112, 34, 122]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [166, 14, 122, 12], [], [], []]
 b := ![[], [91, 69, 144, 117, 115], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 5
  hpos := by decide
  P := [165, 145, 141, 128, 62, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![391971677693, 901942837968, -396626137682, -1391914225810, 565335840098]
  a := ![0, 0, -6, -6, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2265732241, 5213542416, -2292636634, -8045746970, 3267837226]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2649, 2513, -2113, 422, -806]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![2649, 2513, -2113, 422, -806]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![14, 125, 1, 0, 0], ![13, 8, 0, 1, 0], ![31, 94, 0, 0, 1]] where
  M :=![![![2649, 2513, -2113, 422, -806], ![-1612, -1381, 1206, -234, 460], ![920, 688, -635, 120, -242], ![-702, -489, 465, -89, 180], ![-348, -260, 242, -50, 91]]]
  hmulB := by decide  
  f := ![![![4111, 12647, 12341, 876, 3568]], ![![7136, 21951, 21420, 1522, 6196]], ![![5374, 16531, 16131, 1146, 4666]], ![![643, 1978, 1930, 137, 558]], ![![4491, 13815, 13481, 958, 3899]]]
  g := ![![![289, 1894, -2113, 422, -806], ![-166, -1081, 1206, -234, 460], ![88, 569, -635, 120, -242], ![-65, -418, 465, -89, 180], ![-33, -216, 242, -50, 91]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [16, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 178], [0, 1]]
 g := ![![[116, 56], [29, 14], [13], [161], [130, 117], [121, 60], [1]], ![[0, 123], [0, 165], [13], [161], [105, 62], [99, 119], [1]]]
 h' := ![![[113, 178], [73, 134], [126, 67], [79, 152], [68, 124], [33, 81], [163, 113], [0, 1]], ![[0, 1], [0, 45], [0, 112], [71, 27], [118, 55], [57, 98], [44, 66], [113, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [106, 90]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [16, 66, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2757, 2742, -3781, -10125, 10529]
  a := ![13, -1, -2, 7, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-777, -2421, -3781, -10125, 10529]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-38785293, -119307943, -116404146, -8255638, -33661187]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-38785293, -119307943, -116404146, -8255638, -33661187]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![10, 95, 1, 0, 0], ![57, 99, 0, 1, 0], ![66, 172, 0, 0, 1]] where
  M :=![![![-38785293, -119307943, -116404146, -8255638, -33661187], ![-67322374, -207091228, -202050902, -14329894, -58428101], ![-116856202, -359462879, -350714029, -24873410, -101417783], ![-42989682, -132241119, -129022548, -9150565, -37310115], ![-53533198, -164674165, -160666216, -11394802, -46460680]]]
  hmulB := by decide  
  f := ![![![-156263, -188977, 146596, -31086, 55831]], ![![111662, 122892, -98212, 20378, -37427]], ![![50114, 54243, -43587, 9008, -16612]], ![![12339, 8124, -7914, 1427, -3027]], ![![49836, 48567, -40450, 8146, -15428]]]
  g := ![![![21326625, 98023007, -116404146, -8255638, -33661187], ![37018130, 170145460, -202050902, -14329894, -58428101], ![64254984, 295333498, -350714029, -24873410, -101417783], ![23638467, 108648864, -129022548, -9150565, -37310115], ![29435964, 135295747, -160666216, -11394802, -46460680]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P1 : CertificateIrreducibleZModOfList' 179 2 2 7 [138, 178, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 178], [0, 1]]
 g := ![![[131, 48], [68, 56], [68], [13], [106, 46], [83, 1], [1]], ![[0, 131], [124, 123], [68], [13], [152, 133], [84, 178], [1]]]
 h' := ![![[1, 178], [103, 76], [24, 45], [169, 28], [50, 27], [2, 15], [41, 1], [0, 1]], ![[0, 1], [0, 103], [69, 134], [18, 151], [77, 152], [17, 164], [42, 178], [1, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [115, 128]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N1 : CertifiedPrimeIdeal' SI179N1 179 where
  n := 2
  hpos := by decide
  P := [138, 178, 1]
  hirr := P179P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![179, -222, -386, -2155, 3235]
  a := ![-1, -3, 1, -3, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-484, -1713, -386, -2155, 3235]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N1 B_one_repr
lemma NI179N1 : Nat.card (O ⧸ I179N1) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![175, 124, -117, 22, -45]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![175, 124, -117, 22, -45]] 
 ![![179, 0, 0, 0, 0], ![138, 1, 0, 0, 0], ![109, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![175, 124, -117, 22, -45], ![-90, -50, 52, -8, 21], ![42, 15, -19, -6, -3], ![-24, 6, 9, -1, -9], ![-22, -19, 14, 24, -10]]]
  hmulB := by decide  
  f := ![![![100409, 308872, 301363, 21372, 87147]], ![![78384, 241120, 235258, 16684, 68031]], ![![62833, 193283, 188584, 13374, 54534]], ![![18572, 57130, 55741, 3953, 16119]], ![![23773, 73129, 71351, 5060, 20633]]]
  g := ![![![-17, 124, -117, 22, -45], ![3, -50, 52, -8, 21], ![2, 15, -19, -6, -3], ![-8, 6, 9, -1, -9], ![4, -19, 14, 24, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![2649, 2513, -2113, 422, -806]] ![![-38785293, -119307943, -116404146, -8255638, -33661187]]
  ![![-100409, -308872, -301363, -21372, -87147]] where
 M := ![![![-100409, -308872, -301363, -21372, -87147]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![-100409, -308872, -301363, -21372, -87147]] ![![175, 124, -117, 22, -45]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1219, -666, 10, -84, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![1219, -666, 10, -84, 0]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![42, 80, 1, 0, 0], ![109, 39, 0, 1, 0], ![130, 48, 0, 0, 1]] where
  M :=![![![1219, -666, 10, -84, 0], ![0, 1219, -656, 188, -252], ![-504, -1260, 815, -176, 312], ![564, 1158, -786, 143, -264], ![200, 520, -312, 4, -121]]]
  hmulB := by decide  
  f := ![![![-2448185, -7530894, -7347602, -521108, -2124744]], ![![-4249488, -13071905, -12753752, -904524, -3688068]], ![![-2487066, -7650496, -7464293, -529384, -2158488]], ![![-2404949, -7397895, -7217840, -511905, -2087220]], ![![-2903970, -8932940, -8715524, -618124, -2520313]]]
  g := ![![![55, 10, 10, -84, 0], ![220, 323, -656, 188, -252], ![-310, -412, 815, -176, 312], ![289, 393, -786, 143, -264], ![158, 172, -312, 4, -121]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [59, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [172, 180], [0, 1]]
 g := ![![[129, 135], [55], [151, 117], [80], [2, 48], [152, 81], [1]], ![[0, 46], [55], [3, 64], [80], [113, 133], [147, 100], [1]]]
 h' := ![![[172, 180], [165, 139], [141, 69], [154, 152], [63, 73], [82, 49], [122, 172], [0, 1]], ![[0, 1], [0, 42], [63, 112], [53, 29], [130, 108], [3, 132], [22, 9], [172, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [153]]
 b := ![[], [118, 167]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [59, 9, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1725, 2878, -3059, -9604, 10239]
  a := ![3, 0, 3, -7, 16]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-851, 722, -3059, -9604, 10239]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 45, -12, -20, -31]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![23, 45, -12, -20, -31]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![56, 89, 1, 0, 0], ![14, 5, 0, 1, 0], ![97, 101, 0, 0, 1]] where
  M :=![![![23, 45, -12, -20, -31], ![-62, -132, 64, 202, -91], ![-182, -517, 23, 270, 515], ![606, 1455, -516, -1927, 405], ![674, 1847, -166, -1154, -1522]]]
  hmulB := by decide  
  f := ![![![-14709, -44967, -43570, -3128, -12587]], ![![-25174, -77644, -75950, -5362, -21971]], ![![-17172, -52837, -51553, -3656, -14908]], ![![-1922, -5897, -5736, -409, -1658]], ![![-22041, -67766, -66064, -4692, -19102]]]
  g := ![![![22, 24, -12, -20, -31], ![13, 13, 64, 202, -91], ![-305, -309, 23, 270, 515], ![95, 89, -516, -1927, 405], ![960, 973, -166, -1154, -1522]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P1 : CertificateIrreducibleZModOfList' 181 2 2 7 [95, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [117, 180], [0, 1]]
 g := ![![[155, 43], [42], [68, 15], [154], [144, 117], [158, 114], [1]], ![[118, 138], [42], [13, 166], [154], [77, 64], [102, 67], [1]]]
 h' := ![![[117, 180], [51, 119], [56, 59], [15, 167], [76, 110], [13, 29], [86, 117], [0, 1]], ![[0, 1], [37, 62], [81, 122], [6, 14], [95, 71], [148, 152], [19, 64], [117, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [120, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N1 : CertifiedPrimeIdeal' SI181N1 181 where
  n := 2
  hpos := by decide
  P := [95, 64, 1]
  hirr := P181P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1050, 1684, -1556, -5301, 5729]
  a := ![1, 1, 1, -5, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2173, -2276, -1556, -5301, 5729]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N1 B_one_repr
lemma NI181N1 : Nat.card (O ⧸ I181N1) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25419, -19907, 18009, -3410, 6878]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![-25419, -19907, 18009, -3410, 6878]] 
 ![![181, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![37, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![138, 0, 0, 0, 1]] where
  M :=![![![-25419, -19907, 18009, -3410, 6878], ![13756, 8971, -8776, 1570, -3352], ![-6704, -3004, 3547, -580, 1358], ![4710, 1545, -2181, 343, -870], ![2560, 1150, -1376, 286, -527]]]
  hmulB := by decide  
  f := ![![![11362763197, 34953143285, 34102430149, 2418619332, 9861575524]], ![![862300052, 2652532377, 2587973258, 183544754, 748377568]], ![![2511917709, 7726942653, 7538879120, 534673884, 2180056538]], ![![2015691517, 6200494826, 6049583008, 429049729, 1749389104]], ![![8749970806, 26915898714, 26260801448, 1862473782, 7593971329]]]
  g := ![![![-7162, -19907, 18009, -3410, 6878], ![3562, 8971, -8776, 1570, -3352], ![-1499, -3004, 3547, -580, 1358], ![974, 1545, -2181, 343, -870], ![572, 1150, -1376, 286, -527]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![1219, -666, 10, -84, 0]] ![![23, 45, -12, -20, -31]]
  ![![16605, 15377, -13678, 5656, -6053]] where
 M := ![![![16605, 15377, -13678, 5656, -6053]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![16605, 15377, -13678, 5656, -6053]] ![![-25419, -19907, 18009, -3410, 6878]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![-107715091, -149742386, 111568219, -24339070, 42359973]]]
 hmul := by decide  
 g := ![![![![-595111, -827306, 616399, -134470, 234033]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4967, 13320, -2922, -14200, -2568]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![4967, 13320, -2922, -14200, -2568]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![60, 62, 133, 1, 0], ![68, 103, 12, 0, 1]] where
  M :=![![![4967, 13320, -2922, -14200, -2568], ![-5136, -7873, 12966, 37964, -45168], ![-90336, -230976, 50261, 221012, 68724], ![113892, 242130, -149850, -487429, 331518], ![296940, 751914, -179646, -762936, -155911]]]
  hmulB := by decide  
  f := ![![![15764312809, 48492807144, 47312556546, 3355510544, 13681615872]], ![![27363231744, 84172392169, 82123747818, 5824396772, 23748147504]], ![![47496295008, 146103969264, 142547992483, 10109817068, 41221337820]], ![![46999264728, 144575047972, 141056283107, 10004021759, 40789972530]], ![![23466493672, 72185585627, 70428684240, 4994957148, 20366225681]]]
  g := ![![![5401, 6064, 10034, -14200, -2568], ![4128, 11993, -23530, 37964, -45168], ![-94368, -110012, -157953, 221012, 68724], ![35688, -19286, 317801, -487429, 331518], ![296728, 335669, 540114, -762936, -155911]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [142, 165, 129, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [190, 37, 129], [63, 153, 62], [0, 1]]
 g := ![![[152, 46, 34], [50, 117, 52], [66, 84, 17], [76, 94, 154], [168, 131, 5], [50, 62, 1], []], ![[168, 145, 146, 117], [104, 10, 70, 85], [150, 142, 121, 51], [159, 57, 4, 158], [131, 141, 97, 104], [52, 71, 26, 51], [147, 24]], ![[147, 101, 6, 141], [145, 81, 24, 190], [16, 126, 82, 142], [145, 122, 99, 171], [158, 50, 8, 42], [124, 138, 102, 74], [23, 24]]]
 h' := ![![[190, 37, 129], [158, 135, 15], [178, 150, 166], [95, 67, 141], [19, 34, 125], [158, 136, 177], [0, 0, 1], [0, 1]], ![[63, 153, 62], [168, 163, 37], [41, 106, 54], [54, 186, 38], [111, 19, 18], [14, 81, 122], [137, 149, 153], [190, 37, 129]], ![[0, 1], [108, 84, 139], [75, 126, 162], [108, 129, 12], [75, 138, 48], [30, 165, 83], [130, 42, 37], [63, 153, 62]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [162, 71], []]
 b := ![[], [83, 72, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [142, 165, 129, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4762, 4104, -2072, -5833, 2481]
  a := ![4, 0, 0, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![974, 577, 3895, -5833, 2481]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34991, -107636, -105016, -7448, -30368]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-34991, -107636, -105016, -7448, -30368]] 
 ![![191, 0, 0, 0, 0], ![46, 1, 0, 0, 0], ![176, 0, 1, 0, 0], ![66, 0, 0, 1, 0], ![178, 0, 0, 0, 1]] where
  M :=![![![-34991, -107636, -105016, -7448, -30368], ![-60736, -186831, -182284, -12928, -52712], ![-105424, -324296, -316403, -22440, -91496], ![-38784, -119304, -116400, -8255, -33660], ![-48296, -148564, -144948, -10280, -41915]]]
  hmulB := by decide  
  f := ![![![11919, 12556, -10184, 2088, -3872]], ![![2830, 2985, -2420, 496, -920]], ![![11008, 11592, -9403, 1928, -3576]], ![![4098, 4320, -3504, 721, -1332]], ![![11098, 11692, -9484, 1944, -3603]]]
  g := ![![![153383, -107636, -105016, -7448, -30368], ![266238, -186831, -182284, -12928, -52712], ![462128, -324296, -316403, -22440, -91496], ![170010, -119304, -116400, -8255, -33660], ![211706, -148564, -144948, -10280, -41915]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26823, -82420, -80398, -5704, -23248]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![-26823, -82420, -80398, -5704, -23248]] 
 ![![191, 0, 0, 0, 0], ![71, 1, 0, 0, 0], ![116, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![166, 0, 0, 0, 1]] where
  M :=![![![-26823, -82420, -80398, -5704, -23248], ![-46496, -143063, -139570, -9900, -40360], ![-80720, -248296, -242273, -17180, -70060], ![-29700, -91362, -89118, -6323, -25770], ![-36980, -113758, -110982, -7872, -32093]]]
  hmulB := by decide  
  f := ![![![2039, 5132, -1322, -5456, -664]], ![![751, 1901, -468, -1964, -336]], ![![1060, 2664, -697, -2860, -300]], ![![470, 1094, -458, -1627, 590]], ![![2354, 5922, -1522, -6288, -781]]]
  g := ![![![100307, -82420, -80398, -5704, -23248], ![174127, -143063, -139570, -9900, -40360], ![302244, -248296, -242273, -17180, -70060], ![111188, -91362, -89118, -6323, -25770], ![138460, -113758, -110982, -7872, -32093]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![4967, 13320, -2922, -14200, -2568]] ![![-34991, -107636, -105016, -7448, -30368]]
  ![![2039, 5132, -1322, -5456, -664]] where
 M := ![![![2039, 5132, -1322, -5456, -664]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![2039, 5132, -1322, -5456, -664]] ![![-26823, -82420, -80398, -5704, -23248]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![191, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -71, -81, -222, 448]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-5, -71, -81, -222, 448]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![85, 126, 138, 1, 0], ![21, 36, 29, 0, 1]] where
  M :=![![![-5, -71, -81, -222, 448], ![896, 2235, -600, -2406, -218], ![-436, -194, 1853, 4920, -7436], ![-7218, -18711, 3621, 16781, 7380], ![108, -2580, -5076, -12346, 24161]]]
  hmulB := by decide  
  f := ![![![-112377, -345775, -337401, -23924, -97570]], ![![-195140, -600227, -585606, -41534, -169342]], ![![-338684, -1041850, -1016491, -72092, -293944]], ![![-419703, -1291078, -1259664, -89337, -364264]], ![![-100321, -308603, -301094, -21354, -87069]]]
  g := ![![![49, 61, 91, -222, 448], ![1088, 1623, 1750, -2406, -218], ![-1360, -1826, -2391, 4920, -7436], ![-8231, -12429, -13089, 16781, 7380], ![2809, 3540, 5171, -12346, 24161]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [172, 176, 104, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 6, 43], [3, 186, 150], [0, 1]]
 g := ![![[96, 24, 112], [4, 108], [98, 184], [0, 14], [186, 126], [71, 8], [1]], ![[90, 153, 168, 84], [20, 184], [36, 83], [151, 9], [29, 181], [55, 84], [74, 53, 57, 184]], ![[67, 121, 189, 110], [3, 7], [116, 64], [45, 96], [43, 84], [120, 16], [171, 7, 186, 9]]]
 h' := ![![[86, 6, 43], [147, 28, 43], [16, 145, 84], [184, 74, 143], [50, 75, 20], [2, 159, 60], [21, 17, 89], [0, 1]], ![[3, 186, 150], [26, 125, 131], [68, 14, 50], [108, 108, 58], [5, 44, 190], [174, 122, 48], [131, 13, 108], [86, 6, 43]], ![[0, 1], [127, 40, 19], [185, 34, 59], [114, 11, 185], [83, 74, 176], [96, 105, 85], [144, 163, 189], [3, 186, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [184, 43], []]
 b := ![[], [119, 22, 192], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [172, 176, 104, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-155560317, -202831028, 429739533, 1209605699, -1542917909]
  a := ![7, 2, -24, 23, -94]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-365651651, -502943546, -630835376, 1209605699, -1542917909]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![112377, 345775, 337401, 23924, 97570]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![112377, 345775, 337401, 23924, 97570]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![118, 111, 1, 0, 0], ![147, 19, 0, 1, 0], ![187, 2, 0, 0, 1]] where
  M :=![![![112377, 345775, 337401, 23924, 97570], ![195140, 600227, 585606, 41534, 169342], ![338684, 1041850, 1016491, 72092, 293944], ![124602, 383277, 373953, 26521, 108138], ![155160, 477282, 465666, 33026, 134659]]]
  hmulB := by decide  
  f := ![![![5, 71, 81, 222, -448]], ![![-896, -2235, 600, 2406, 218]], ![![-510, -1241, 385, 1494, -110]], ![![-47, -69, 102, 319, -358]], ![![-5, 59, 111, 304, -557]]]
  g := ![![![-318463, -195624, 337401, 23924, 97570], ![-552740, -339533, 585606, 41534, 169342], ![-959442, -589359, 1016491, 72092, 293944], ![-352965, -216817, 373953, 26521, 108138], ![-439531, -269992, 465666, 33026, 134659]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P1 : CertificateIrreducibleZModOfList' 193 2 2 7 [97, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [111, 192], [0, 1]]
 g := ![![[164, 2], [169], [151], [108], [8], [172], [111, 1]], ![[0, 191], [169], [151], [108], [8], [172], [29, 192]]]
 h' := ![![[111, 192], [18, 52], [149, 13], [163, 99], [88, 109], [51, 104], [41, 65], [0, 1]], ![[0, 1], [0, 141], [48, 180], [151, 94], [28, 84], [15, 89], [115, 128], [111, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [137, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N1 : CertifiedPrimeIdeal' SI193N1 193 where
  n := 2
  hpos := by decide
  P := [97, 82, 1]
  hirr := P193P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![480, -4284, -9686, -22528, 43260]
  a := ![1, 3, -8, 8, -33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18832, 7318, -9686, -22528, 43260]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N1 B_one_repr
lemma NI193N1 : Nat.card (O ⧸ I193N1) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-5, -71, -81, -222, 448]] ![![112377, 345775, 337401, 23924, 97570]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![-193, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-137, -419, -403, -26, -114]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-137, -419, -403, -26, -114]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![98, 112, 119, 1, 0], ![105, 87, 106, 0, 1]] where
  M :=![![![-137, -419, -403, -26, -114], ![-228, -707, -708, -70, -192], ![-384, -1188, -1223, -124, -402], ![-210, -603, -393, 169, -186], ![-264, -782, -532, 110, -17]]]
  hmulB := by decide  
  f := ![![![1679, 2149, -1639, 352, -624]], ![![-1248, -1441, 1134, -238, 432]], ![![864, 912, -739, 152, -282]], ![![644, 797, -614, 131, -234]], ![![807, 998, -769, 164, -293]]]
  g := ![![![73, 63, 75, -26, -114], ![136, 121, 142, -70, -192], ![274, 242, 285, -124, -402], ![14, -17, -4, 169, -186], ![-47, -59, -60, 110, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [100, 173, 183, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 94, 17], [189, 102, 180], [0, 1]]
 g := ![![[51, 140, 138], [160, 47], [6, 96, 188], [73, 55], [74, 33], [67, 196], [1]], ![[176, 132, 77, 69], [27, 191], [97, 70, 191, 195], [66, 157], [11, 164], [171, 29], [62, 128, 166, 185]], ![[84, 105, 128, 50], [157, 178], [107, 121, 109, 108], [112, 174], [179, 136], [85, 19], [59, 83, 149, 12]]]
 h' := ![![[22, 94, 17], [38, 193, 27], [188, 40, 176], [146, 73, 42], [123, 82, 45], [148, 60, 69], [97, 24, 14], [0, 1]], ![[189, 102, 180], [48, 87, 125], [160, 29, 114], [22, 140, 9], [186, 140, 74], [33, 169, 178], [114, 81, 63], [22, 94, 17]], ![[0, 1], [59, 114, 45], [183, 128, 104], [114, 181, 146], [171, 172, 78], [12, 165, 147], [89, 92, 120], [189, 102, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 172], []]
 b := ![[], [60, 29, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [100, 173, 183, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1499029, -8136384, -6593473, -14488035, 37879889]
  a := ![3, 0, 7, -3, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12990152, -8533131, -11663886, -14488035, 37879889]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![65, 64, -40, 10, -16]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![65, 64, -40, 10, -16]] 
 ![![197, 0, 0, 0, 0], ![63, 1, 0, 0, 0], ![168, 0, 1, 0, 0], ![140, 0, 0, 1, 0], ![174, 0, 0, 0, 1]] where
  M :=![![![65, 64, -40, 10, -16], ![-32, -15, 40, -4, 14], ![28, 38, 11, 4, 2], ![-12, 0, 18, -1, 6], ![-4, 6, 16, 0, 5]]]
  hmulB := by decide  
  f := ![![![-3, 16, 12, -46, -4]], ![![-1, 5, 4, -14, -2]], ![![-4, 10, 11, -36, -2]], ![![0, 16, 6, -41, 2]], ![![2, 26, 8, -52, -7]]]
  g := ![![![21, 64, -40, 10, -16], ![-39, -15, 40, -4, 14], ![-26, 38, 11, 4, 2], ![-20, 0, 18, -1, 6], ![-20, 6, 16, 0, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![99, 83, -73, 14, -28]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![99, 83, -73, 14, -28]] 
 ![![197, 0, 0, 0, 0], ![94, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![100, 0, 0, 1, 0], ![151, 0, 0, 0, 1]] where
  M :=![![![99, 83, -73, 14, -28], ![-56, -41, 38, -6, 14], ![28, 14, -17, 4, -4], ![-18, -3, 9, -11, 6], ![-8, 2, 6, -6, -5]]]
  hmulB := by decide  
  f := ![![![-6013, -18481, -18005, -1280, -5206]], ![![-2922, -8981, -8750, -622, -2530]], ![![-977, -3003, -2926, -208, -846]], ![![-3086, -9485, -9241, -657, -2672]], ![![-4651, -14295, -13927, -990, -4027]]]
  g := ![![![-14, 83, -73, 14, -28], ![6, -41, 38, -6, 14], ![-3, 14, -17, 4, -4], ![1, -3, 9, -11, 6], ![5, 2, 6, -6, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-137, -419, -403, -26, -114]] ![![65, 64, -40, 10, -16]]
  ![![-6013, -18481, -18005, -1280, -5206]] where
 M := ![![![-6013, -18481, -18005, -1280, -5206]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![-6013, -18481, -18005, -1280, -5206]] ![![99, 83, -73, 14, -28]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![197, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB434I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB434I4 : PrimesBelowBoundCertificateInterval O 151 197 434 where
  m := 9
  g := ![2, 3, 2, 1, 3, 3, 3, 2, 3]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB434I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0, I179N1, I179N2]
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
    · exact ![4330747, 163, 163]
    · exact ![4657463, 27889]
    · exact ![154963892093]
    · exact ![32041, 32041, 179]
    · exact ![32761, 32761, 181]
    · exact ![6967871, 191, 191]
    · exact ![7189057, 37249]
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
      exact NI163N1
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
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
  β := ![I163N1, I163N2, I179N2, I181N2, I191N1, I191N2, I197N1, I197N2]
  Il := ![[], [I163N1, I163N2], [], [], [I179N2], [I181N2], [I191N1, I191N2], [], [I197N1, I197N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
