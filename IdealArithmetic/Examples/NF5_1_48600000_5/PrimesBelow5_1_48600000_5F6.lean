
import IdealArithmetic.Examples.NF5_1_48600000_5.RI5_1_48600000_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12108, 593, 17752, 15842, 14031]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![-12108, 593, 17752, 15842, 14031]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![50, 189, 1, 0, 0], ![59, 156, 0, 1, 0], ![19, 133, 0, 0, 1]] where
  M :=![![![-12108, 593, 17752, 15842, 14031], ![-59746, -32827, 60932, 67188, 66990], ![-134178, -99694, 101351, 128120, 134574], ![-232821, -208315, 132534, 195877, 216291], ![823, -17855, -24404, -15644, -10828]]]
  hmulB := by decide  
  f := ![![![-194714, -347783, 502056, -189812, 44241]], ![![291142, -293487, -986708, 624488, -1227354]], ![![178572, -270479, -631445, 420916, -881934]], ![![120801, -289562, -458086, 329379, -748758]], ![![145275, -159533, -496148, 317090, -631111]]]
  g := ![![![-8175, -29930, 17752, 15842, 14031], ![-32464, -120389, 60932, 67188, 66990], ![-59602, -222335, 101351, 128120, 134574], ![-87649, -329108, 132534, 195877, 216291], ![9143, 32977, -24404, -15644, -10828]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [100, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [155, 256], [0, 1]]
 g := ![![[37, 18], [21], [68], [72], [68], [222], [124], [1]], ![[0, 239], [21], [68], [72], [68], [222], [124], [1]]]
 h' := ![![[155, 256], [113, 180], [97, 110], [27, 140], [206, 103], [18, 117], [170, 42], [157, 155], [0, 1]], ![[0, 1], [0, 77], [185, 147], [139, 117], [237, 154], [163, 140], [255, 215], [24, 102], [155, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [149]]
 b := ![[], [73, 203]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 2
  hpos := by decide
  P := [100, 102, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1368, -3198, 468, 754, -588]
  a := ![5, -7, -8, -8, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-226, -510, 468, 754, -588]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, -74, -644, 376, -648]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![233, -74, -644, 376, -648]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![245, 92, 1, 0, 0], ![76, 140, 0, 1, 0], ![110, 97, 0, 0, 1]] where
  M :=![![![233, -74, -644, 376, -648], ![544, 3581, -692, -536, 3552], ![-3016, -9490, 6597, -1228, -5160], ![6116, 11672, -15532, 5637, -300], ![-2916, -1386, 8664, -4464, 6157]]]
  hmulB := by decide  
  f := ![![![20985, 28906, 412, -10136, -14616]], ![![49504, 74205, 8308, -19448, -31584]], ![![37925, 54464, 3457, -16668, -25344]], ![![33224, 49188, 4828, -13507, -21492]], ![![27506, 40171, 3324, -11592, -18059]]]
  g := ![![![781, 270, -644, 376, -648], ![-700, -787, -692, -536, 3552], ![-3729, 218, 6597, -1228, -5160], ![13292, 2648, -15532, 5637, -300], ![-9586, -2999, 8664, -4464, 6157]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P1 : CertificateIrreducibleZModOfList' 257 2 2 8 [231, 143, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [114, 256], [0, 1]]
 g := ![![[123, 168], [9], [248], [241], [193], [137], [146], [1]], ![[0, 89], [9], [248], [241], [193], [137], [146], [1]]]
 h' := ![![[114, 256], [192, 93], [230, 3], [83, 48], [146, 193], [36, 129], [103, 213], [26, 114], [0, 1]], ![[0, 1], [0, 164], [58, 254], [158, 209], [46, 64], [93, 128], [227, 44], [172, 143], [114, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74]]
 b := ![[], [204, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N1 : CertifiedPrimeIdeal' SI257N1 257 where
  n := 2
  hpos := by decide
  P := [231, 143, 1]
  hirr := P257P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-65, 53228, -52158, 54076, 61152]
  a := ![-6, -56, 11, -57, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7557, -33660, -52158, 54076, 61152]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N1 B_one_repr
lemma NI257N1 : Nat.card (O ⧸ I257N1) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N1

def I257N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, 3, 20, -12, 21]] i)))

def SI257N2: IdealEqSpanCertificate' Table ![![-6, 3, 20, -12, 21]] 
 ![![257, 0, 0, 0, 0], ![209, 1, 0, 0, 0], ![133, 0, 1, 0, 0], ![132, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![-6, 3, 20, -12, 21], ![-18, -115, 24, 16, -114], ![98, 304, -213, 40, 162], ![-193, -365, 494, -181, 15], ![91, 37, -272, 142, -200]]]
  hmulB := by decide  
  f := ![![![-63328, 13903, 3780, -2942, -11733]], ![![-51386, 11280, 3068, -2386, -9519]], ![![-32802, 7199, 1959, -1522, -6075]], ![![-32581, 7149, 1946, -1511, -6033]], ![![-10193, 2238, 608, -474, -1889]]]
  g := ![![![-10, 3, 20, -12, 21], ![91, -115, 24, 16, -114], ![-183, 304, -213, 40, 162], ![131, -365, 494, -181, 15], ![70, 37, -272, 142, -200]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N2 : Nat.card (O ⧸ I257N2) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N2)

lemma isPrimeI257N2 : Ideal.IsPrime I257N2 := prime_ideal_of_norm_prime hp257.out _ NI257N2
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![-12108, 593, 17752, 15842, 14031]] ![![233, -74, -644, 376, -648]]
  ![![-63328, 13903, 3780, -2942, -11733]] where
 M := ![![![-63328, 13903, 3780, -2942, -11733]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI257N1 : IdealMulLeCertificate' Table 
  ![![-63328, 13903, 3780, -2942, -11733]] ![![-6, 3, 20, -12, 21]]
  ![![257, 0, 0, 0, 0]] where
 M := ![![![257, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1, I257N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
    exact isPrimeI257N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0 ⊙ MulI257N1)
instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14502, 33479, -35190, 10960, 7521]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![14502, 33479, -35190, 10960, 7521]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![0, 0, 0, 263, 0], ![151, 34, 198, 239, 1]] where
  M :=![![![14502, 33479, -35190, 10960, 7521], ![-36962, -36373, 103920, -48460, 50718], ![-2258, -141776, -34115, 55460, -196098], ![159119, 545705, -334374, 45575, 337119], ![-162697, -406309, 385926, -110138, -128204]]]
  hmulB := by decide  
  f := ![![![-382092, 84229, 22470, -18190, -71295]], ![![178970, -39527, -10512, 8560, 33450]], ![![-42010, 9164, 2483, -1952, -7770]], ![![-79763, 17473, 4698, -3749, -14811]], ![![-300884, 66145, 17712, -14239, -56018]]]
  g := ![![![-4263, -845, -5796, -6793, 7521], ![-29260, -6695, -37788, -46274, 50718], ![112580, 24812, 147503, 178414, -196098], ![-192950, -41507, -255072, -306182, 337119], ![72989, 15029, 97986, 116086, -128204]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 4 2 8 [40, 12, 37, 148, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 245, 76, 72], [169, 67, 19, 226], [192, 213, 168, 228], [0, 1]]
 g := ![![[256, 202, 194, 74], [2, 244, 110, 61], [200, 206, 111, 102], [239, 107, 66], [51, 118, 144], [117, 115, 75], [1], []], ![[15, 203, 129, 41, 19, 26], [38, 68, 116, 154, 173, 95], [129, 153, 241, 134, 222, 69], [49, 16, 133], [31, 202, 25], [0, 246, 181], [76, 18, 233], [138, 100, 187]], ![[64, 69, 243, 148, 85, 250], [9, 67, 75, 158, 255, 14], [22, 248, 244, 230, 26, 246], [221, 130, 102], [58, 132, 86], [105, 31, 108], [193, 87, 81], [140, 70, 54]], ![[131, 117, 196, 148, 186, 189], [252, 174, 220, 21, 5, 201], [182, 207, 154, 238, 234, 188], [202, 212, 190], [254, 179, 72], [101, 45, 166], [58, 224, 218], [109, 245, 173]]]
 h' := ![![[17, 245, 76, 72], [183, 212, 171, 211], [153, 170, 53, 245], [194, 157, 230, 188], [54, 148, 144, 132], [76, 216, 181, 251], [223, 251, 226, 115], [0, 0, 1], [0, 1]], ![[169, 67, 19, 226], [13, 99, 182, 112], [151, 238, 13, 35], [240, 10, 151, 187], [126, 7, 66, 213], [83, 249, 22, 5], [168, 131, 121, 203], [29, 44, 168, 170], [17, 245, 76, 72]], ![[192, 213, 168, 228], [50, 40, 116, 116], [109, 108, 249, 122], [57, 198, 167, 257], [84, 26, 98, 75], [33, 75, 260, 136], [258, 137, 99, 138], [80, 19, 101, 9], [169, 67, 19, 226]], ![[0, 1], [229, 175, 57, 87], [27, 10, 211, 124], [127, 161, 241, 157], [37, 82, 218, 106], [27, 249, 63, 134], [139, 7, 80, 70], [155, 200, 256, 84], [192, 213, 168, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [218, 47, 97], []]
 b := ![[], [], [34, 206, 16, 159], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 4
  hpos := by decide
  P := [40, 12, 37, 148, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2523534, 1631144, -1423344, -1737236, -3379008]
  a := ![1, -4, -1, -5, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1949634, 443032, 2538480, 3064052, -3379008]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 4784350561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-382092, 84229, 22470, -18190, -71295]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![-382092, 84229, 22470, -18190, -71295]] 
 ![![263, 0, 0, 0, 0], ![146, 1, 0, 0, 0], ![125, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![175, 0, 0, 0, 1]] where
  M :=![![![-382092, 84229, 22470, -18190, -71295], ![178970, -39527, -10512, 8560, 33450], ![-42010, 9164, 2483, -1952, -7770], ![-79763, 17473, 4698, -3749, -14811], ![-140243, 30955, 8238, -6700, -26200]]]
  hmulB := by decide  
  f := ![![![14502, 33479, -35190, 10960, 7521]], ![![7910, 18447, -19140, 5900, 4368]], ![![6884, 15373, -16855, 5420, 2829]], ![![991, 2966, -2208, 465, 1482]], ![![9031, 20732, -21948, 6874, 4517]]]
  g := ![![![-10967, 84229, 22470, -18190, -71295], ![5134, -39527, -10512, 8560, 33450], ![-1205, 9164, 2483, -1952, -7770], ![-2281, 17473, 4698, -3749, -14811], ![-4021, 30955, 8238, -6700, -26200]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![14502, 33479, -35190, 10960, 7521]] ![![-382092, 84229, 22470, -18190, -71295]]
  ![![263, 0, 0, 0, 0]] where
 M := ![![![263, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC263 : ContainsPrimesAboveP 263 ![I263N0, I263N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 263 (by decide) (𝕀 ⊙ MulI263N0)
instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1973, -151, -348, -226, -6]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![1973, -151, -348, -226, -6]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![124, 172, 95, 1, 0], ![246, 137, 156, 0, 1]] where
  M :=![![![1973, -151, -348, -226, -6], ![464, 1203, -766, -1148, -1344], ![2492, 2061, -1289, -1914, -2100], ![3782, 3336, -1570, -2629, -2970], ![278, -283, 338, 422, 497]]]
  hmulB := by decide  
  f := ![![![57, 325, -82, -38, 306]], ![![-536, -1631, 1186, -240, -840]], ![![1080, 2185, -2711, 946, 120]], ![![62, -119, -227, 157, -342]], ![![404, 722, -1042, 394, -91]]]
  g := ![![![117, 147, 82, -226, -6], ![1760, 1423, 1182, -1148, -1344], ![2812, 2301, 1889, -1914, -2100], ![3942, 3206, 2645, -2629, -2970], ![-648, -524, -436, 422, 497]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [251, 122, 115, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 91, 68], [151, 177, 201], [0, 1]]
 g := ![![[45, 147, 25], [81, 79], [199, 223, 56], [83, 44, 239], [107, 249], [64, 166], [154, 1], []], ![[193, 95, 25, 28], [149, 115], [67, 115, 6, 107], [204, 255, 24, 59], [232, 61], [192, 150], [243, 125], [55, 51]], ![[114, 214, 187, 123], [164, 199], [113, 208, 153, 250], [209, 259, 205, 194], [222, 126], [44, 143], [36, 211], [191, 51]]]
 h' := ![![[3, 91, 68], [75, 182, 264], [85, 54, 50], [149, 173, 104], [19, 105, 117], [75, 178, 49], [82, 60, 191], [0, 0, 1], [0, 1]], ![[151, 177, 201], [199, 21, 193], [163, 47, 148], [192, 89, 44], [202, 216, 142], [64, 168, 64], [81, 119, 227], [192, 134, 177], [3, 91, 68]], ![[0, 1], [196, 66, 81], [206, 168, 71], [30, 7, 121], [138, 217, 10], [213, 192, 156], [175, 90, 120], [146, 135, 91], [151, 177, 201]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [204, 119], []]
 b := ![[], [238, 73, 200], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [251, 122, 115, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7391818, -7675205, 3873970, 5556248, 6029931]
  a := ![-8, 27, 13, 26, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8103084, -6652232, -5444754, 5556248, 6029931]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 19465109 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57, 325, -82, -38, 306]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![57, 325, -82, -38, 306]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![217, 174, 1, 0, 0], ![171, 230, 0, 1, 0], ![91, 49, 0, 0, 1]] where
  M :=![![![57, 325, -82, -38, 306], ![-536, -1631, 1186, -240, -840], ![1080, 2185, -2711, 946, 120], ![-798, 646, 2658, -1645, 3138], ![-394, -3145, 308, 638, -3395]]]
  hmulB := by decide  
  f := ![![![1973, -151, -348, -226, -6]], ![![464, 1203, -766, -1148, -1344]], ![![1901, 664, -781, -932, -882]], ![![1665, 945, -882, -1135, -1164]], ![![753, 167, -256, -284, -245]]]
  g := ![![![-13, 31, -82, -38, 306], ![-522, -415, 1186, -240, -840], ![1549, 931, -2711, 946, 120], ![-2163, -882, 2658, -1645, 3138], ![493, -138, 308, 638, -3395]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P1 : CertificateIrreducibleZModOfList' 269 2 2 8 [35, 172, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [97, 268], [0, 1]]
 g := ![![[174, 263], [177], [34, 23], [6, 80], [166], [45], [263], [1]], ![[130, 6], [177], [113, 246], [234, 189], [166], [45], [263], [1]]]
 h' := ![![[97, 268], [76, 97], [155, 56], [59, 125], [27, 235], [69, 78], [90, 160], [234, 97], [0, 1]], ![[0, 1], [70, 172], [207, 213], [79, 144], [226, 34], [103, 191], [8, 109], [228, 172], [97, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129]]
 b := ![[], [167, 199]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N1 : CertifiedPrimeIdeal' SI269N1 269 where
  n := 2
  hpos := by decide
  P := [35, 172, 1]
  hirr := P269P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-271, -6576, -4025, 2987, -8179]
  a := ![10, -9, -15, -7, -31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4114, 1515, -4025, 2987, -8179]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N1 B_one_repr
lemma NI269N1 : Nat.card (O ⧸ I269N1) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N1
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![1973, -151, -348, -226, -6]] ![![57, 325, -82, -38, 306]]
  ![![269, 0, 0, 0, 0]] where
 M := ![![![269, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC269 : ContainsPrimesAboveP 269 ![I269N0, I269N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
    exact isPrimeI269N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 269 (by decide) (𝕀 ⊙ MulI269N0)
instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14457, 10011, -11852, -14384, -14888]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![14457, 10011, -11852, -14384, -14888]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![0, 0, 271, 0, 0], ![0, 0, 0, 271, 0], ![149, 15, 68, 206, 1]] where
  M :=![![![14457, 10011, -11852, -14384, -14888], ![58544, 48277, -38522, -52472, -56528], ![109000, 98859, -60723, -90994, -100888], ![162610, 161226, -73762, -125481, -143830], ![-15462, -6611, 17690, 18440, 17915]]]
  hmulB := by decide  
  f := ![![![-5809, 1277, 342, -276, -1088]], ![![2728, -579, -174, 132, 520]], ![![-652, 109, 73, -42, -124]], ![![-1198, 268, 30, -35, -262]], ![![-4125, 903, 220, -182, -801]]]
  g := ![![![8239, 861, 3692, 11264, -14888], ![31296, 3307, 14042, 42776, -56528], ![55872, 5949, 25091, 76354, -100888], ![79680, 8556, 35818, 108869, -143830], ![-9907, -1016, -4430, -13550, 17915]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 4 2 8 [35, 142, 85, 265, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 188, 185, 42], [215, 102, 144, 10], [265, 251, 213, 219], [0, 1]]
 g := ![![[60, 144, 249, 31], [6, 252, 265, 212], [257, 33, 91, 37], [54, 134, 243, 162], [89, 135, 110], [76, 9, 36], [1], []], ![[195, 184, 161, 148, 84, 240], [53, 134, 47, 119, 238, 12], [184, 190, 151, 210, 6, 208], [195, 27, 220, 81, 30, 42], [103, 53, 68], [206, 47, 187], [5, 69, 11], [182, 108, 138]], ![[52, 0, 195, 118, 208, 268], [139, 83, 125, 15, 229, 212], [74, 185, 150, 100, 31, 252], [177, 268, 25, 175, 14, 100], [35, 146, 241], [191, 151, 228], [174, 198, 238], [197, 228, 100]], ![[31, 252, 92, 70, 209, 252], [200, 150, 71, 209, 17, 82], [13, 265, 2, 162, 131, 44], [37, 0, 26, 88, 28, 50], [80, 28, 114], [114, 194, 110], [42, 268, 79], [196, 34, 265]]]
 h' := ![![[68, 188, 185, 42], [61, 78, 100, 64], [219, 69, 50, 36], [7, 113, 22, 151], [33, 253, 47, 220], [191, 188, 43, 142], [236, 129, 186, 6], [0, 0, 1], [0, 1]], ![[215, 102, 144, 10], [104, 78, 19, 194], [178, 138, 130, 44], [105, 140, 270, 26], [159, 140, 50, 1], [181, 135, 187, 136], [133, 135, 226, 27], [151, 9, 207, 163], [68, 188, 185, 42]], ![[265, 251, 213, 219], [4, 159, 84, 9], [238, 38, 168, 77], [76, 186, 225, 28], [3, 114, 103, 84], [259, 185, 218, 181], [13, 107, 115, 109], [35, 47, 191, 194], [215, 102, 144, 10]], ![[0, 1], [172, 227, 68, 4], [149, 26, 194, 114], [139, 103, 25, 66], [158, 35, 71, 237], [178, 34, 94, 83], [118, 171, 15, 129], [222, 215, 143, 185], [265, 251, 213, 219]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [196, 110, 113], []]
 b := ![[], [], [137, 266, 187, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 4
  hpos := by decide
  P := [35, 142, 85, 265, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![116035651, 995360728, -34566096, -256098216, 1110087360]
  a := ![-6, -4, 10, -14, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-609915059, -57771032, -278673456, -844775256, 1110087360]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 5393580481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5809, -1277, -342, 276, 1088]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![5809, -1277, -342, 276, 1088]] 
 ![![271, 0, 0, 0, 0], ![121, 1, 0, 0, 0], ![132, 0, 1, 0, 0], ![219, 0, 0, 1, 0], ![78, 0, 0, 0, 1]] where
  M :=![![![5809, -1277, -342, 276, 1088], ![-2728, 579, 174, -132, -520], ![652, -109, -73, 42, 124], ![1198, -268, -30, 35, 262], ![2130, -505, -128, 112, 355]]]
  hmulB := by decide  
  f := ![![![-14457, -10011, 11852, 14384, 14888]], ![![-6671, -4648, 5434, 6616, 6856]], ![![-7444, -5241, 5997, 7342, 7624]], ![![-12283, -8685, 9850, 12087, 12562]], ![![-4104, -2857, 3346, 4072, 4219]]]
  g := ![![![222, -1277, -342, 276, 1088], ![-97, 579, 174, -132, -520], ![17, -109, -73, 42, 124], ![35, -268, -30, 35, 262], ![103, -505, -128, 112, 355]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![14457, 10011, -11852, -14384, -14888]] ![![5809, -1277, -342, 276, 1088]]
  ![![271, 0, 0, 0, 0]] where
 M := ![![![-271, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC271 : ContainsPrimesAboveP 271 ![I271N0, I271N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI271N0
    exact isPrimeI271N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 271 (by decide) (𝕀 ⊙ MulI271N0)
instance hp277 : Fact (Nat.Prime 277) := {out := by norm_num}

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-558, -1028, 186, 548, 717]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![-558, -1028, 186, 548, 717]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![0, 0, 0, 277, 0], ![209, 252, 115, 175, 1]] where
  M :=![![![-558, -1028, 186, 548, 717], ![-2530, -2861, 474, 1468, 1854], ![-3322, -4195, 461, 1942, 2550], ![-3227, -4433, 60, 1669, 2349], ![1501, 1558, -408, -934, -1126]]]
  hmulB := by decide  
  f := ![![![0, -8, 0, 2, -9]], ![![14, 49, -30, 4, 30]], ![![-34, -79, 83, -26, -18]], ![![37, 19, -108, 55, -75]], ![![22, 18, -61, 29, -34]]]
  g := ![![![-543, -656, -297, -451, 717], ![-1408, -1697, -768, -1166, 1854], ![-1936, -2335, -1057, -1604, 2550], ![-1784, -2153, -975, -1478, 2349], ![855, 1030, 466, 708, -1126]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 4 2 8 [66, 227, 47, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 149, 158, 175], [111, 171, 248, 182], [107, 233, 148, 197], [0, 1]]
 g := ![![[146, 143, 257, 89], [50, 169, 228], [233, 274, 8, 3], [26, 205, 236], [13, 205, 272, 81], [270], [1], []], ![[187, 39, 41, 60, 275, 55], [210, 121, 207], [233, 138, 116, 238, 32, 185], [113, 152, 190], [227, 160, 112, 260, 20, 243], [230, 36, 28], [224, 148, 264], [25, 177, 155]], ![[97, 143, 55, 118, 231, 73], [114, 139, 220], [11, 104, 193, 149, 227, 38], [240, 123, 136], [259, 261, 242, 17, 111, 167], [141, 270, 9], [135, 200, 40], [118, 247, 161]], ![[269, 264, 177, 114, 60, 251], [51, 134, 196], [265, 227, 110, 74, 135, 209], [75, 200, 74], [216, 201, 216, 209, 25, 195], [77, 168, 83], [65, 158, 265], [158, 142, 29]]]
 h' := ![![[59, 149, 158, 175], [252, 29, 168, 56], [134, 174, 12, 134], [121, 166, 81, 130], [250, 109, 87, 76], [109, 252, 169, 9], [211, 50, 230], [0, 0, 1], [0, 1]], ![[111, 171, 248, 182], [56, 95, 201, 141], [204, 64, 72, 22], [268, 27, 51, 207], [109, 268, 254, 81], [121, 14, 86, 49], [204, 199, 183, 100], [169, 225, 64, 131], [59, 149, 158, 175]], ![[107, 233, 148, 197], [39, 150, 45, 40], [258, 65, 178, 135], [225, 27, 62, 71], [217, 136, 73, 238], [84, 106, 257, 183], [183, 172, 45, 3], [101, 137, 145, 58], [111, 171, 248, 182]], ![[0, 1], [194, 3, 140, 40], [76, 251, 15, 263], [122, 57, 83, 146], [45, 41, 140, 159], [267, 182, 42, 36], [232, 133, 96, 174], [190, 192, 67, 88], [107, 233, 148, 197]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [47, 141, 208], []]
 b := ![[], [], [7, 266, 1, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 4
  hpos := by decide
  P := [66, 227, 47, 0, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-653672692, -830001897, 281007748, 334467578, 447222713]
  a := ![-6, 19, 16, 20, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-339795017, -409856049, -184655611, -281333961, 447222713]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 5887339441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 8, 0, -2, 9]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![0, 8, 0, -2, 9]] 
 ![![277, 0, 0, 0, 0], ![60, 1, 0, 0, 0], ![139, 0, 1, 0, 0], ![232, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![0, 8, 0, -2, 9], ![-14, -49, 30, -4, -30], ![34, 79, -83, 26, 18], ![-37, -19, 108, -55, 75], ![-1, -70, -18, 28, -98]]]
  hmulB := by decide  
  f := ![![![558, 1028, -186, -548, -717]], ![![130, 233, -42, -124, -162]], ![![292, 531, -95, -282, -369]], ![![479, 877, -156, -465, -609]], ![![53, 102, -18, -54, -71]]]
  g := ![![![-1, 8, 0, -2, 9], ![2, -49, 30, -4, -30], ![1, 79, -83, 26, 18], ![-12, -19, 108, -55, 75], ![11, -70, -18, 28, -98]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N1 : Nat.card (O ⧸ I277N1) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N1)

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := prime_ideal_of_norm_prime hp277.out _ NI277N1
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![-558, -1028, 186, 548, 717]] ![![0, 8, 0, -2, 9]]
  ![![277, 0, 0, 0, 0]] where
 M := ![![![-277, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC277 : ContainsPrimesAboveP 277 ![I277N0, I277N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI277N0
    exact isPrimeI277N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 277 (by decide) (𝕀 ⊙ MulI277N0)
instance hp281 : Fact (Nat.Prime 281) := {out := by norm_num}

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![787, 957, -362, -398, -588]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![787, 957, -362, -398, -588]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![0, 0, 0, 281, 0], ![67, 255, 122, 145, 1]] where
  M :=![![![787, 957, -362, -398, -588], ![1972, 2569, -58, -1520, -1212], ![2732, 2467, -163, -1578, -3348], ![3940, 6792, -2430, -981, -780], ![-2032, -3049, 2440, 90, 863]]]
  hmulB := by decide  
  f := ![![![743919, -164031, -43740, 35438, 138840]], ![![-348556, 76855, 20494, -16604, -65052]], ![![81656, -18005, -4801, 3890, 15240]], ![![155148, -34210, -9122, 7391, 28956]], ![![-22447, 4949, 1320, -1069, -4189]]]
  g := ![![![143, 537, 254, 302, -588], ![296, 1109, 526, 620, -1212], ![808, 3047, 1453, 1722, -3348], ![200, 732, 330, 399, -780], ![-213, -794, -366, -445, 863]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 4 2 8 [250, 206, 26, 43, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 49, 222, 87], [238, 191, 197, 83], [168, 40, 143, 111], [0, 1]]
 g := ![![[194, 163, 51, 272], [280, 228, 2], [207, 107, 85], [204, 92, 123, 25], [220, 143, 174, 153], [213, 4, 163], [1], []], ![[217, 177, 276, 204, 71, 171], [107, 49, 158], [192, 234, 158], [181, 133, 195, 95, 99, 97], [126, 163, 171, 6, 170, 11], [66, 26, 252], [125, 79, 242], [255, 62, 263]], ![[256, 61, 111, 162, 151, 142], [28, 263, 62], [275, 190, 8], [143, 239, 274, 274, 62, 174], [243, 88, 6, 272, 106, 146], [245, 132, 125], [46, 41, 31], [117, 53, 145]], ![[199, 190, 77, 170, 141, 85], [251, 135, 106], [222, 176, 277], [67, 268, 96, 32, 225, 116], [104, 153, 3, 65, 217, 109], [195, 203, 1], [1, 53, 245], [135, 156, 238]]]
 h' := ![![[113, 49, 222, 87], [39, 13, 158, 159], [167, 144, 35, 149], [142, 43, 165, 180], [76, 106, 105, 276], [258, 236, 175, 49], [31, 75, 255, 238], [0, 0, 1], [0, 1]], ![[238, 191, 197, 83], [269, 181, 268, 193], [263, 143, 97, 57], [178, 204, 244, 224], [201, 153, 215, 126], [179, 261, 247, 32], [10, 217, 178, 231], [161, 87, 17, 234], [113, 49, 222, 87]], ![[168, 40, 143, 111], [248, 69, 52, 55], [144, 191, 117, 129], [274, 114, 100, 264], [235, 97, 175, 103], [253, 128, 17, 243], [244, 131, 252, 94], [137, 174, 239, 84], [238, 191, 197, 83]], ![[0, 1], [51, 18, 84, 155], [104, 84, 32, 227], [99, 201, 53, 175], [154, 206, 67, 57], [33, 218, 123, 238], [156, 139, 158, 280], [94, 20, 24, 244], [168, 40, 143, 111]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [207, 274, 133], []]
 b := ![[], [], [86, 24, 254, 232], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 4
  hpos := by decide
  P := [250, 206, 26, 43, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1044683, 8174533, -849998, -1687928, 8801397]
  a := ![-2, -3, 3, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2094836, -7957942, -3824272, -4547653, 8801397]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 6234839521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-743919, 164031, 43740, -35438, -138840]] i)))

def SI281N1: IdealEqSpanCertificate' Table ![![-743919, 164031, 43740, -35438, -138840]] 
 ![![281, 0, 0, 0, 0], ![256, 1, 0, 0, 0], ![109, 0, 1, 0, 0], ![251, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![-743919, 164031, 43740, -35438, -138840], ![348556, -76855, -20494, 16604, 65052], ![-81656, 18005, 4801, -3890, -15240], ![-155148, 34210, 9122, -7391, -28956], ![-273108, 60219, 16058, -13010, -50971]]]
  hmulB := by decide  
  f := ![![![-787, -957, 362, 398, 588]], ![![-724, -881, 330, 368, 540]], ![![-315, -380, 141, 160, 240]], ![![-717, -879, 332, 359, 528]], ![![-116, -139, 48, 62, 89]]]
  g := ![![![-115657, 164031, 43740, -35438, -138840], ![54190, -76855, -20494, 16604, 65052], ![-12695, 18005, 4801, -3890, -15240], ![-24121, 34210, 9122, -7391, -28956], ![-42460, 60219, 16058, -13010, -50971]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N1 : Nat.card (O ⧸ I281N1) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N1)

lemma isPrimeI281N1 : Ideal.IsPrime I281N1 := prime_ideal_of_norm_prime hp281.out _ NI281N1
def MulI281N0 : IdealMulLeCertificate' Table 
  ![![787, 957, -362, -398, -588]] ![![-743919, 164031, 43740, -35438, -138840]]
  ![![281, 0, 0, 0, 0]] where
 M := ![![![-281, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC281 : ContainsPrimesAboveP 281 ![I281N0, I281N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI281N0
    exact isPrimeI281N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 281 (by decide) (𝕀 ⊙ MulI281N0)
instance hp283 : Fact (Nat.Prime 283) := {out := by norm_num}

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![100, 266, -430, 230, 65]] i)))

def SI283N0: IdealEqSpanCertificate' Table ![![100, 266, -430, 230, 65]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![89, 235, 1, 0, 0], ![27, 5, 0, 1, 0], ![190, 52, 0, 0, 1]] where
  M :=![![![100, 266, -430, 230, 65], ![-590, -195, 1122, -400, 1250], ![-850, -3259, 655, 722, -2450], ![2023, 6847, -5548, 1577, 3991], ![-2017, -4430, 5252, -1880, -662]]]
  hmulB := by decide  
  f := ![![![-5568591474, 1227850634, 327415156, -265270276, -1039283923]], ![![2609108398, -575297255, -153407130, 124289760, 486946190]], ![![413161118, -91100260, -24292537, 19681702, 77109571]], ![![-489285469, 107885356, 28768402, -23308029, -91316902]], ![![-3266442005, 720236510, 192056218, -155603078, -609626452]]]
  g := ![![![70, 342, -430, 230, 65], ![-1156, -1155, 1122, -400, 1250], ![1367, -118, 655, 722, -2450], ![-1078, 3870, -5548, 1577, 3991], ![-1035, -4222, 5252, -1880, -662]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P0 : CertificateIrreducibleZModOfList' 283 2 2 8 [41, 225, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 282], [0, 1]]
 g := ![![[40, 214], [128, 9], [90], [112, 218], [139, 62], [138], [251], [1]], ![[0, 69], [84, 274], [90], [21, 65], [56, 221], [138], [251], [1]]]
 h' := ![![[58, 282], [129, 110], [123, 3], [219, 211], [244, 255], [252, 179], [163, 180], [242, 58], [0, 1]], ![[0, 1], [0, 173], [14, 280], [5, 72], [35, 28], [163, 104], [132, 103], [210, 225], [58, 282]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [95, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 2
  hpos := by decide
  P := [41, 225, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3213, -1031, -198, 7018, 4320]
  a := ![-10, 9, 20, 5, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3519, -757, -198, 7018, 4320]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N0 B_one_repr
lemma NI283N0 : Nat.card (O ⧸ I283N0) = 80089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N0

def I283N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12839, -31302, 30682, -9014, -9024]] i)))

def SI283N1: IdealEqSpanCertificate' Table ![![-12839, -31302, 30682, -9014, -9024]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![160, 224, 1, 0, 0], ![101, 137, 0, 1, 0], ![247, 280, 0, 0, 1]] where
  M :=![![![-12839, -31302, 30682, -9014, -9024], ![36076, 44935, -98680, 43336, -36036], ![-7300, 102124, 52235, -55344, 166044], ![-128738, -470454, 262164, -24777, -314058], ![141986, 373058, -331442, 88386, 138251]]]
  hmulB := by decide  
  f := ![![![-192921, -238494, 29886, 113806, 147876]], ![![-523364, -674803, 46376, 287384, 387084]], ![![-525708, -672204, 53603, 292992, 391668]], ![![-324145, -414805, 32646, 180409, 241338]], ![![-684983, -874360, 71716, 382912, 511091]]]
  g := ![![![-6299, -11104, 30682, -9014, -9024], ![71904, 92941, -98680, 43336, -36036], ![-154728, -178476, 52235, -55344, 166044], ![134275, 113553, 262164, -24777, -314058], ![35681, 84088, -331442, 88386, 138251]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P1 : CertificateIrreducibleZModOfList' 283 2 2 8 [72, 90, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [193, 282], [0, 1]]
 g := ![![[72, 23], [270, 42], [138], [212, 246], [37, 240], [236], [176], [1]], ![[266, 260], [169, 241], [138], [146, 37], [228, 43], [236], [176], [1]]]
 h' := ![![[193, 282], [87, 227], [10, 61], [18, 103], [166, 23], [191, 250], [153, 233], [211, 193], [0, 1]], ![[0, 1], [33, 56], [180, 222], [87, 180], [77, 260], [48, 33], [125, 50], [104, 90], [193, 282]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [208, 187]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N1 : CertifiedPrimeIdeal' SI283N1 283 where
  n := 2
  hpos := by decide
  P := [72, 90, 1]
  hirr := P283P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1905, -2006, 1171, 2216, 1200]
  a := ![-6, 7, 9, 6, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2507, -3194, 1171, 2216, 1200]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N1 : Ideal.IsPrime I283N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N1 B_one_repr
lemma NI283N1 : Nat.card (O ⧸ I283N1) = 80089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N1

def I283N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 69, -20, -12, 60]] i)))

def SI283N2: IdealEqSpanCertificate' Table ![![15, 69, -20, -12, 60]] 
 ![![283, 0, 0, 0, 0], ![214, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![48, 0, 0, 1, 0], ![173, 0, 0, 0, 1]] where
  M :=![![![15, 69, -20, -12, 60], ![-96, -329, 234, -64, -192], ![256, 485, -585, 170, 0], ![-122, 170, 538, -383, 606], ![-82, -649, 62, 140, -703]]]
  hmulB := by decide  
  f := ![![![-575311555, 126853735, 33826458, -27406040, -107372220]], ![![-434088750, 95714711, 25523014, -20678628, -81015360]], ![![-51045717, 11255362, 3001323, -2431658, -9526824]], ![![-98003318, 21609312, 5762278, -4668571, -18290670]], ![![-352438543, 77711190, 20722246, -16789068, -65776723]]]
  g := ![![![-85, 69, -20, -12, 60], ![356, -329, 234, -64, -192], ![-343, 485, -585, 170, 0], ![-482, 170, 538, -383, 606], ![891, -649, 62, 140, -703]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI283N2 : Nat.card (O ⧸ I283N2) = 283 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI283N2)

lemma isPrimeI283N2 : Ideal.IsPrime I283N2 := prime_ideal_of_norm_prime hp283.out _ NI283N2
def MulI283N0 : IdealMulLeCertificate' Table 
  ![![100, 266, -430, 230, 65]] ![![-12839, -31302, 30682, -9014, -9024]]
  ![![-8929334, -119046460, -6887740, 34470276, -145133921]] where
 M := ![![![-8929334, -119046460, -6887740, 34470276, -145133921]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI283N1 : IdealMulLeCertificate' Table 
  ![![-8929334, -119046460, -6887740, 34470276, -145133921]] ![![15, 69, -20, -12, 60]]
  ![![283, 0, 0, 0, 0]] where
 M := ![![![17226866560, 135261469043, -14102251674, -26965655000, 145239293999]]]
 hmul := by decide  
 g := ![![![![60872320, 477955721, -49831278, -95285000, 513213053]]]]
 hle2 := by decide  


def PBC283 : ContainsPrimesAboveP 283 ![I283N0, I283N1, I283N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI283N0
    exact isPrimeI283N1
    exact isPrimeI283N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 283 (by decide) (𝕀 ⊙ MulI283N0 ⊙ MulI283N1)
instance hp293 : Fact (Nat.Prime 293) := {out := by norm_num}

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![62, 88, -14, -44, -57]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![62, 88, -14, -44, -57]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![255, 156, 95, 1, 0], ![239, 243, 40, 0, 1]] where
  M :=![![![62, 88, -14, -44, -57], ![202, 245, -26, -116, -150], ![266, 347, -21, -142, -198], ![239, 353, 20, -105, -153], ![-129, -150, 36, 78, 94]]]
  hmulB := by decide  
  f := ![![![-24, 4, 4, -2, -3]], ![![10, -9, -2, 4, -6]], ![![2, 23, -11, 2, 18]], ![![-15, 6, -1, 1, 0]], ![![-11, -1, 0, 2, -5]]]
  g := ![![![85, 71, 22, -44, -57], ![224, 187, 58, -116, -150], ![286, 241, 73, -142, -198], ![217, 184, 55, -105, -153], ![-145, -120, -38, 78, 94]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 3 2 8 [287, 68, 114, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [264, 28, 130], [208, 264, 163], [0, 1]]
 g := ![![[44, 69, 216], [162, 25], [256, 38, 278], [89, 21], [80, 61], [40, 46, 124], [179, 1], []], ![[144, 12, 269, 72], [280, 6], [67, 257, 177, 208], [157, 254], [196, 16], [229, 238, 51, 28], [169, 255], [123, 199]], ![[134, 147, 22, 118], [0, 158], [230, 218, 32, 155], [71, 133], [109, 22], [192, 223, 66, 215], [213, 198], [90, 199]]]
 h' := ![![[264, 28, 130], [153, 26, 41], [71, 184, 5], [202, 97, 82], [66, 110, 263], [240, 128, 190], [195, 140, 36], [0, 0, 1], [0, 1]], ![[208, 264, 163], [264, 271, 140], [286, 151, 42], [291, 44, 270], [195, 270, 227], [22, 187, 289], [239, 260, 162], [114, 289, 264], [264, 28, 130]], ![[0, 1], [161, 289, 112], [109, 251, 246], [202, 152, 234], [77, 206, 96], [3, 271, 107], [33, 186, 95], [147, 4, 28], [208, 264, 163]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 193], []]
 b := ![[], [109, 210, 136], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 3
  hpos := by decide
  P := [287, 68, 114, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-440750, -453328, 216656, 344771, 362343]
  a := ![-3, 8, 6, 9, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-597124, -485621, -160513, 344771, 362343]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 25153757 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20, 20, -56, 26, -27]] i)))

def SI293N1: IdealEqSpanCertificate' Table ![![20, 20, -56, 26, -27]] 
 ![![293, 0, 0, 0, 0], ![51, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![248, 0, 0, 1, 0], ![130, 0, 0, 0, 1]] where
  M :=![![![20, 20, -56, 26, -27], ![2, 151, 38, -60, 210], ![-150, -565, 301, -22, -390], ![411, 953, -996, 309, 219], ![-257, -350, 694, -296, 214]]]
  hmulB := by decide  
  f := ![![![-33398, 7560, 2078, -1560, -6249]], ![![-5760, 1305, 360, -268, -1077]], ![![-2066, 467, 131, -94, -384]], ![![-28297, 6401, 1764, -1317, -5289]], ![![-14861, 3362, 924, -694, -2780]]]
  g := ![![![-10, 20, -56, 26, -27], ![-71, 151, 38, -60, 210], ![271, -565, 301, -22, -390], ![-462, 953, -996, 309, 219], ![173, -350, 694, -296, 214]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI293N1 : Nat.card (O ⧸ I293N1) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI293N1)

lemma isPrimeI293N1 : Ideal.IsPrime I293N1 := prime_ideal_of_norm_prime hp293.out _ NI293N1

def I293N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3077, -680, -180, 148, 576]] i)))

def SI293N2: IdealEqSpanCertificate' Table ![![3077, -680, -180, 148, 576]] 
 ![![293, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![113, 0, 1, 0, 0], ![259, 0, 0, 1, 0], ![153, 0, 0, 0, 1]] where
  M :=![![![3077, -680, -180, 148, 576], ![-1448, 313, 88, -64, -264], ![328, -84, -15, 24, 72], ![628, -156, -32, 41, 132], ![1132, -248, -68, 52, 209]]]
  hmulB := by decide  
  f := ![![![81, 456, -76, -84, 432]], ![![12, 73, -8, -16, 72]], ![![37, 188, -43, -28, 168]], ![![67, 404, -52, -83, 396]], ![![41, 224, -40, -40, 209]]]
  g := ![![![-231, -680, -180, 148, 576], ![100, 313, 88, -64, -264], ![-37, -84, -15, 24, 72], ![-63, -156, -32, 41, 132], ![-81, -248, -68, 52, 209]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI293N2 : Nat.card (O ⧸ I293N2) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI293N2)

lemma isPrimeI293N2 : Ideal.IsPrime I293N2 := prime_ideal_of_norm_prime hp293.out _ NI293N2
def MulI293N0 : IdealMulLeCertificate' Table 
  ![![62, 88, -14, -44, -57]] ![![20, 20, -56, 26, -27]]
  ![![81, 456, -76, -84, 432]] where
 M := ![![![81, 456, -76, -84, 432]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI293N1 : IdealMulLeCertificate' Table 
  ![![81, 456, -76, -84, 432]] ![![3077, -680, -180, 148, 576]]
  ![![293, 0, 0, 0, 0]] where
 M := ![![![293, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC293 : ContainsPrimesAboveP 293 ![I293N0, I293N1, I293N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI293N0
    exact isPrimeI293N1
    exact isPrimeI293N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 293 (by decide) (𝕀 ⊙ MulI293N0 ⊙ MulI293N1)
instance hp307 : Fact (Nat.Prime 307) := {out := by norm_num}

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7626, 228, -478, -384, 259]] i)))

def SI307N0: IdealEqSpanCertificate' Table ![![7626, 228, -478, -384, 259]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![0, 0, 307, 0, 0], ![305, 110, 73, 1, 0], ![49, 113, 283, 0, 1]] where
  M :=![![![7626, 228, -478, -384, 259], ![250, 5085, 206, -1724, -2822], ![4546, 5559, 539, -1518, -2350], ![3743, 4357, 1588, -117, -793], ![-1, -3414, 212, 1482, 2222]]]
  hmulB := by decide  
  f := ![![![708, 1752, -1684, 486, 535]], ![![-2042, -2679, 5546, -2396, 1846]], ![![550, -5259, -3229, 3150, -9034]], ![![125, -386, -499, 377, -898]], ![![-157, -5622, -1145, 2084, -7589]]]
  g := ![![![365, 43, -149, -384, 259], ![2164, 1673, 3012, -1724, -2822], ![1898, 1427, 2529, -1518, -2350], ![255, 348, 764, -117, -793], ![-1827, -1360, -2400, 1482, 2222]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P0 : CertificateIrreducibleZModOfList' 307 3 2 8 [233, 274, 66, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 3, 6], [138, 303, 301], [0, 1]]
 g := ![![[130, 231, 153], [292, 37, 149], [61, 81], [188, 304], [264, 269, 175], [33, 122, 299], [241, 1], []], ![[265, 280, 300, 103], [273, 246, 288, 62], [123, 63], [272, 199], [246, 106, 52, 109], [223, 169, 57, 212], [87, 16], [116, 36]], ![[123, 215, 214, 116], [28, 201, 19, 206], [65, 10], [303, 160], [176, 278, 90, 198], [231, 214, 147, 253], [33, 9], [128, 36]]]
 h' := ![![[103, 3, 6], [118, 254, 253], [62, 232, 145], [54, 181, 9], [195, 263, 35], [293, 156, 92], [28, 45, 91], [0, 0, 1], [0, 1]], ![[138, 303, 301], [195, 265, 205], [42, 126, 198], [173, 63, 129], [0, 48, 210], [289, 64, 261], [98, 296, 213], [159, 49, 303], [103, 3, 6]], ![[0, 1], [220, 95, 156], [294, 256, 271], [157, 63, 169], [266, 303, 62], [181, 87, 261], [290, 273, 3], [272, 258, 3], [138, 303, 301]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [237, 16], []]
 b := ![[], [60, 280, 202], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 3
  hpos := by decide
  P := [233, 274, 66, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4212399, 7473476, -8745283, 2555747, -773095]
  a := ![16, -7, -33, -7, -41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2401983, -606837, 76453, 2555747, -773095]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N0 B_one_repr
lemma NI307N0 : Nat.card (O ⧸ I307N0) = 28934443 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N0

def I307N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-168, 37, 10, -8, -31]] i)))

def SI307N1: IdealEqSpanCertificate' Table ![![-168, 37, 10, -8, -31]] 
 ![![307, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![222, 0, 0, 1, 0], ![209, 0, 0, 0, 1]] where
  M :=![![![-168, 37, 10, -8, -31], ![78, -19, -4, 4, 14], ![-18, 6, -1, 0, -2], ![-37, 5, 6, -3, -5], ![-61, 13, 2, -2, -14]]]
  hmulB := by decide  
  f := ![![![238, 207, -154, -210, -223]], ![![16, 14, -10, -14, -15]], ![![12, 11, -7, -10, -11]], ![![179, 157, -114, -157, -167]], ![![161, 140, -104, -142, -151]]]
  g := ![![![24, 37, 10, -8, -31], ![-11, -19, -4, 4, 14], ![1, 6, -1, 0, -2], ![5, 5, 6, -3, -5], ![10, 13, 2, -2, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N1 : Nat.card (O ⧸ I307N1) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N1)

lemma isPrimeI307N1 : Ideal.IsPrime I307N1 := prime_ideal_of_norm_prime hp307.out _ NI307N1

def I307N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![165, 321, -418, 150, 0]] i)))

def SI307N2: IdealEqSpanCertificate' Table ![![165, 321, -418, 150, 0]] 
 ![![307, 0, 0, 0, 0], ![144, 1, 0, 0, 0], ![70, 0, 1, 0, 0], ![107, 0, 0, 1, 0], ![190, 0, 0, 0, 1]] where
  M :=![![![165, 321, -418, 150, 0], ![-300, 47, 942, -536, 900], ![-364, -2465, 411, 406, -2508], ![2252, 6676, -5038, 1085, 3276], ![-1928, -4145, 4768, -1586, -563]]]
  hmulB := by decide  
  f := ![![![1256371, -276409, -74040, 59462, 233964]], ![![587396, -129223, -34618, 27796, 109380]], ![![286926, -63115, -16911, 13574, 53424]], ![![438751, -96515, -25858, 20759, 81696]], ![![779058, -171401, -45910, 36874, 145081]]]
  g := ![![![-107, 321, -418, 150, 0], ![-608, 47, 942, -536, 900], ![2472, -2465, 411, 406, -2508], ![-4381, 6676, -5038, 1085, 3276], ![1752, -4145, 4768, -1586, -563]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N2 : Nat.card (O ⧸ I307N2) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N2)

lemma isPrimeI307N2 : Ideal.IsPrime I307N2 := prime_ideal_of_norm_prime hp307.out _ NI307N2
def MulI307N0 : IdealMulLeCertificate' Table 
  ![![7626, 228, -478, -384, 259]] ![![-168, 37, 10, -8, -31]]
  ![![-1256371, 276409, 74040, -59462, -233964]] where
 M := ![![![-1256371, 276409, 74040, -59462, -233964]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI307N1 : IdealMulLeCertificate' Table 
  ![![-1256371, 276409, 74040, -59462, -233964]] ![![165, 321, -418, 150, 0]]
  ![![307, 0, 0, 0, 0]] where
 M := ![![![-307, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC307 : ContainsPrimesAboveP 307 ![I307N0, I307N1, I307N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI307N0
    exact isPrimeI307N1
    exact isPrimeI307N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 307 (by decide) (𝕀 ⊙ MulI307N0 ⊙ MulI307N1)


lemma PB434I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)

def PB434I6 : PrimesBelowBoundCertificateInterval O 251 307 434 where
  m := 9
  g := ![3, 2, 2, 2, 2, 2, 3, 3, 3]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB434I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0, I257N1, I257N2]
    · exact ![I263N0, I263N1]
    · exact ![I269N0, I269N1]
    · exact ![I271N0, I271N1]
    · exact ![I277N0, I277N1]
    · exact ![I281N0, I281N1]
    · exact ![I283N0, I283N1, I283N2]
    · exact ![I293N0, I293N1, I293N2]
    · exact ![I307N0, I307N1, I307N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC257
    · exact PBC263
    · exact PBC269
    · exact PBC271
    · exact PBC277
    · exact PBC281
    · exact PBC283
    · exact PBC293
    · exact PBC307
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![66049, 66049, 257]
    · exact ![4784350561, 263]
    · exact ![19465109, 72361]
    · exact ![5393580481, 271]
    · exact ![5887339441, 277]
    · exact ![6234839521, 281]
    · exact ![80089, 80089, 283]
    · exact ![25153757, 293, 293]
    · exact ![28934443, 307, 307]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
      exact NI257N2
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
      exact NI269N1
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
      exact NI277N1
    · dsimp ; intro j
      fin_cases j
      exact NI281N0
      exact NI281N1
    · dsimp ; intro j
      fin_cases j
      exact NI283N0
      exact NI283N1
      exact NI283N2
    · dsimp ; intro j
      fin_cases j
      exact NI293N0
      exact NI293N1
      exact NI293N2
    · dsimp ; intro j
      fin_cases j
      exact NI307N0
      exact NI307N1
      exact NI307N2
  β := ![I257N2, I263N1, I271N1, I277N1, I281N1, I283N2, I293N1, I293N2, I307N1, I307N2]
  Il := ![[I257N2], [I263N1], [], [I271N1], [I277N1], [I281N1], [I283N2], [I293N1, I293N2], [I307N1, I307N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
