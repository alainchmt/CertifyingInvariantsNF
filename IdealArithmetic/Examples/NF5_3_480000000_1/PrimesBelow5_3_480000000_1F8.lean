
import IdealArithmetic.Examples.NF5_3_480000000_1.RI5_3_480000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp367 : Fact (Nat.Prime 367) := {out := by norm_num}

def I367N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16721, 16457, 7605, -2331, -2326]] i)))

def SI367N0: IdealEqSpanCertificate' Table ![![16721, 16457, 7605, -2331, -2326]] 
 ![![367, 0, 0, 0, 0], ![0, 367, 0, 0, 0], ![0, 0, 367, 0, 0], ![0, 0, 0, 367, 0], ![170, 255, 208, 4, 1]] where
  M :=![![![16721, 16457, 7605, -2331, -2326], ![-18608, 15027, 37576, 1259, -9319], ![-37276, -14443, 13768, 4330, -2771], ![-1780, -28360, -37561, 1275, 9769], ![-5596, -11330, -10573, 1060, 2834]]]
  hmulB := by decide  
  f := ![![![-793, 248, -495, -135, 146]], ![![1168, -423, 766, 167, -259]], ![![-1036, 236, -590, -224, 121]], ![![-100, -187, 77, -138, -146]], ![![-146, -48, -31, -76, -46]]]
  g := ![![![1123, 1661, 1339, 19, -2326], ![4266, 6516, 5384, 105, -9319], ![1182, 1886, 1608, 42, -2771], ![-4530, -6865, -5639, -103, 9769], ![-1328, -2000, -1635, -28, 2834]]]
  hle1 := by decide   
  hle2 := by decide  


def P367P0 : CertificateIrreducibleZModOfList' 367 4 2 8 [6, 331, 242, 99, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [168, 305, 176, 219], [129, 30, 115, 363], [338, 31, 76, 152], [0, 1]]
 g := ![![[339, 342, 0, 50], [261, 33, 16, 170], [226, 140, 283, 240], [87, 192, 81, 209], [9, 73, 313], [275, 160, 337, 289], [268, 1], []], ![[127, 312, 66, 159, 247, 265], [340, 69, 56, 22, 149, 238], [83, 286, 333, 183, 34, 197], [214, 63, 152, 272, 308, 219], [1, 110, 364], [318, 311, 50, 326, 277, 262], [85, 279, 168, 108, 291, 295], [66, 125, 251]], ![[0, 175, 40, 359, 159, 358], [340, 141, 41, 294, 271, 96], [120, 242, 302, 315, 57, 366], [337, 340, 338, 229, 251, 342], [215, 218, 149], [224, 125, 359, 121, 210, 269], [31, 295, 280, 249, 304, 320], [109, 65, 16]], ![[320, 348, 256, 272, 213, 156], [42, 234, 105, 123, 339, 197], [62, 153, 217, 236, 57, 365], [12, 337, 329, 220, 254, 20], [74, 254, 110], [178, 236, 41, 238, 37, 286], [126, 111, 123, 188, 332, 5], [79, 198, 350]]]
 h' := ![![[168, 305, 176, 219], [269, 89, 285, 28], [112, 126, 38, 212], [212, 277, 19, 314], [40, 362, 341, 24], [185, 281, 204, 310], [227, 100, 139, 17], [0, 0, 1], [0, 1]], ![[129, 30, 115, 363], [197, 203, 89, 300], [49, 317, 353, 254], [228, 346, 163, 224], [3, 73, 189, 366], [3, 55, 128, 167], [227, 102, 244, 291], [303, 245, 90, 157], [168, 305, 176, 219]], ![[338, 31, 76, 152], [43, 187, 289, 185], [223, 322, 298, 38], [252, 0, 97, 183], [161, 343, 96, 181], [152, 85, 254, 140], [253, 332, 185, 93], [206, 264, 197, 108], [129, 30, 115, 363]], ![[0, 1], [133, 255, 71, 221], [28, 336, 45, 230], [278, 111, 88, 13], [236, 323, 108, 163], [310, 313, 148, 117], [345, 200, 166, 333], [0, 225, 79, 102], [338, 31, 76, 152]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [134, 43, 290], []]
 b := ![[], [], [8, 173, 327, 256], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI367N0 : CertifiedPrimeIdeal' SI367N0 367 where
  n := 4
  hpos := by decide
  P := [6, 331, 242, 99, 1]
  hirr := P367P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![200434470, 138687265, -6706973, 137849349, 138557942]
  a := ![0, 1, 1, 0, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-63636010, -95895335, -78547027, -1134557, 138557942]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI367N0 : Ideal.IsPrime I367N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI367N0 B_one_repr
lemma NI367N0 : Nat.card (O ⧸ I367N0) = 18141126721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI367N0

def I367N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-793, 248, -495, -135, 146]] i)))

def SI367N1: IdealEqSpanCertificate' Table ![![-793, 248, -495, -135, 146]] 
 ![![367, 0, 0, 0, 0], ![354, 1, 0, 0, 0], ![99, 0, 1, 0, 0], ![283, 0, 0, 1, 0], ![159, 0, 0, 0, 1]] where
  M :=![![![-793, 248, -495, -135, 146], ![1168, -423, 766, 167, -259], ![-1036, 236, -590, -224, 121], ![-100, -187, 77, -138, -146], ![-724, -251, -145, -383, -241]]]
  hmulB := by decide  
  f := ![![![16721, 16457, 7605, -2331, -2326]], ![![16078, 15915, 7438, -2245, -2269]], ![![4409, 4400, 2089, -617, -635]], ![![12889, 12613, 5762, -1794, -1767]], ![![7229, 7099, 3266, -1007, -1000]]]
  g := ![![![-67, 248, -495, -135, 146], ![188, -423, 766, 167, -259], ![49, 236, -590, -224, 121], ![329, -187, 77, -138, -146], ![679, -251, -145, -383, -241]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI367N1 : Nat.card (O ⧸ I367N1) = 367 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI367N1)

lemma isPrimeI367N1 : Ideal.IsPrime I367N1 := prime_ideal_of_norm_prime hp367.out _ NI367N1
def MulI367N0 : IdealMulLeCertificate' Table 
  ![![16721, 16457, 7605, -2331, -2326]] ![![-793, 248, -495, -135, 146]]
  ![![367, 0, 0, 0, 0]] where
 M := ![![![367, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC367 : ContainsPrimesAboveP 367 ![I367N0, I367N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI367N0
    exact isPrimeI367N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 367 (by decide) (𝕀 ⊙ MulI367N0)
instance hp373 : Fact (Nat.Prime 373) := {out := by norm_num}

def I373N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![81, 56, -2, 57, 47]] i)))

def SI373N0: IdealEqSpanCertificate' Table ![![81, 56, -2, 57, 47]] 
 ![![373, 0, 0, 0, 0], ![0, 373, 0, 0, 0], ![150, 229, 1, 0, 0], ![339, 41, 0, 1, 0], ![216, 112, 0, 0, 1]] where
  M :=![![![81, 56, -2, 57, 47], ![376, 257, -2, 268, 218], ![872, 598, -11, 627, 511], ![1856, 1266, -28, 1330, 1087], ![4224, 2884, -60, 3025, 2468]]]
  hmulB := by decide  
  f := ![![![-27, 30, -98, -11, 23]], ![![184, 1, 82, -24, -10]], ![![102, 13, 11, -19, 3]], ![![-5, 27, -80, -13, 20]], ![![40, 18, -32, -13, 10]]]
  g := ![![![-78, -19, -2, 57, 47], ![-368, -93, -2, 268, 218], ![-859, -214, -11, 627, 511], ![-1822, -452, -28, 1330, 1087], ![-4143, -1029, -60, 3025, 2468]]]
  hle1 := by decide   
  hle2 := by decide  


def P373P0 : CertificateIrreducibleZModOfList' 373 2 2 8 [342, 129, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [244, 372], [0, 1]]
 g := ![![[56, 12], [198], [101, 119], [152], [104, 184], [168, 103], [134, 229], [1]], ![[0, 361], [198], [43, 254], [152], [240, 189], [309, 270], [60, 144], [1]]]
 h' := ![![[244, 372], [145, 111], [147, 53], [21, 137], [240, 317], [359, 161], [51, 99], [31, 244], [0, 1]], ![[0, 1], [0, 262], [24, 320], [252, 236], [4, 56], [105, 212], [335, 274], [260, 129], [244, 372]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [224]]
 b := ![[], [137, 112]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI373N0 : CertifiedPrimeIdeal' SI373N0 373 where
  n := 2
  hpos := by decide
  P := [342, 129, 1]
  hirr := P373P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![136402, 99776, -17532, 72869, 157707]
  a := ![3, -2, 0, -3, -61]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-150137, -44333, -17532, 72869, 157707]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI373N0 : Ideal.IsPrime I373N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI373N0 B_one_repr
lemma NI373N0 : Nat.card (O ⧸ I373N0) = 139129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI373N0

def I373N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![121, 64, -14, 78, 66]] i)))

def SI373N1: IdealEqSpanCertificate' Table ![![121, 64, -14, 78, 66]] 
 ![![373, 0, 0, 0, 0], ![0, 373, 0, 0, 0], ![254, 310, 1, 0, 0], ![336, 75, 0, 1, 0], ![139, 12, 0, 0, 1]] where
  M :=![![![121, 64, -14, 78, 66], ![528, 359, -28, 356, 300], ![1200, 822, 3, 844, 684], ![2472, 1710, -8, 1797, 1458], ![5688, 3890, -68, 4078, 3325]]]
  hmulB := by decide  
  f := ![![![-6947, -4076, -1334, -7074, 3882]], ![![31056, 18203, 5996, 31580, -17340]], ![![20894, 12244, 4039, 21240, -11664]], ![![360, 207, 76, 357, -198]], ![![-2117, -1242, -406, -2156, 1183]]]
  g := ![![![-85, -6, -14, 78, 66], ![-412, -57, -28, 356, 300], ![-1014, -192, 3, 844, 684], ![-2150, -397, -8, 1797, 1458], ![-4851, -860, -68, 4078, 3325]]]
  hle1 := by decide   
  hle2 := by decide  


def P373P1 : CertificateIrreducibleZModOfList' 373 2 2 8 [364, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [319, 372], [0, 1]]
 g := ![![[367, 290], [175], [17, 264], [48], [69, 217], [177, 170], [89, 305], [1]], ![[0, 83], [175], [308, 109], [48], [287, 156], [322, 203], [31, 68], [1]]]
 h' := ![![[319, 372], [366, 214], [153, 290], [18, 96], [248, 222], [101, 219], [55, 258], [9, 319], [0, 1]], ![[0, 1], [0, 159], [159, 83], [56, 277], [196, 151], [211, 154], [297, 115], [314, 54], [319, 372]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [140]]
 b := ![[], [25, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI373N1 : CertifiedPrimeIdeal' SI373N1 373 where
  n := 2
  hpos := by decide
  P := [364, 54, 1]
  hirr := P373P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1979, 1127, -66, 893, 1191]
  a := ![1, 0, 1, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1198, -160, -66, 893, 1191]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI373N1 : Ideal.IsPrime I373N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI373N1 B_one_repr
lemma NI373N1 : Nat.card (O ⧸ I373N1) = 139129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI373N1

def I373N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18629, -6031, 11761, 3062, -3597]] i)))

def SI373N2: IdealEqSpanCertificate' Table ![![18629, -6031, 11761, 3062, -3597]] 
 ![![373, 0, 0, 0, 0], ![41, 1, 0, 0, 0], ![92, 0, 1, 0, 0], ![145, 0, 0, 1, 0], ![131, 0, 0, 0, 1]] where
  M :=![![![18629, -6031, 11761, 3062, -3597], ![-28776, 9343, -18186, -4719, 5589], ![22356, -7149, 14062, 3735, -4284], ![-2748, 960, -1791, -440, 666], ![6172, -1588, 3649, 1277, -989]]]
  hmulB := by decide  
  f := ![![![95441, -204544, -368759, -1414, 93351]], ![![12493, -21961, -41623, -377, 10500]], ![![24496, -49286, -90210, -491, 22812]], ![![35249, -79387, -141500, -369, 35850]], ![![33035, -71637, -128796, -456, 32611]]]
  g := ![![![-2115, -6031, 11761, 3062, -3597], ![3253, 9343, -18186, -4719, 5589], ![-2570, -7149, 14062, 3735, -4284], ![266, 960, -1791, -440, 666], ![-858, -1588, 3649, 1277, -989]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI373N2 : Nat.card (O ⧸ I373N2) = 373 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI373N2)

lemma isPrimeI373N2 : Ideal.IsPrime I373N2 := prime_ideal_of_norm_prime hp373.out _ NI373N2
def MulI373N0 : IdealMulLeCertificate' Table 
  ![![81, 56, -2, 57, 47]] ![![121, 64, -14, 78, 66]]
  ![![445209, 303944, -6360, 318661, 260159]] where
 M := ![![![445209, 303944, -6360, 318661, 260159]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI373N1 : IdealMulLeCertificate' Table 
  ![![445209, 303944, -6360, 318661, 260159]] ![![18629, -6031, 11761, 3062, -3597]]
  ![![373, 0, 0, 0, 0]] where
 M := ![![![135342677, 92943021, -2258515, 97175825, 79503458]]]
 hmul := by decide  
 g := ![![![![362849, 249177, -6055, 260525, 213146]]]]
 hle2 := by decide  


def PBC373 : ContainsPrimesAboveP 373 ![I373N0, I373N1, I373N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI373N0
    exact isPrimeI373N1
    exact isPrimeI373N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 373 (by decide) (𝕀 ⊙ MulI373N0 ⊙ MulI373N1)
instance hp379 : Fact (Nat.Prime 379) := {out := by norm_num}

def I379N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2771, 10320, 11745, -687, -3096]] i)))

def SI379N0: IdealEqSpanCertificate' Table ![![2771, 10320, 11745, -687, -3096]] 
 ![![379, 0, 0, 0, 0], ![0, 379, 0, 0, 0], ![0, 0, 379, 0, 0], ![203, 222, 179, 1, 0], ![99, 239, 323, 0, 1]] where
  M :=![![![2771, 10320, 11745, -687, -3096], ![-24768, -277, 22014, 2505, -5157], ![-20628, -15522, -2782, 2712, 1179], ![17100, -9975, -29241, -1264, 7236], ![2988, -5331, -10071, 33, 2627]]]
  hmulB := by decide  
  f := ![![![4625, 1479, 1485, 3549, -2088]], ![![-16704, -7879, -4140, -15195, 8559]], ![![34236, 18573, 7316, 33414, -18513]], ![![8689, 4848, 1792, 8606, -4752]], ![![20097, 11389, 4060, 20070, -11062]]]
  g := ![![![1184, 2382, 2994, -687, -3096], ![-60, 1784, 3270, 2505, -5157], ![-1815, -2373, -2293, 2712, 1179], ![-1168, -3849, -5647, -1264, 7236], ![-696, -1690, -2281, 33, 2627]]]
  hle1 := by decide   
  hle2 := by decide  


def P379P0 : CertificateIrreducibleZModOfList' 379 3 2 8 [282, 171, 104, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [289, 244, 128], [365, 134, 251], [0, 1]]
 g := ![![[339, 228, 36], [107, 280, 94], [87, 324], [163, 92, 169], [267, 94, 138], [3, 82, 314], [33, 275, 1], []], ![[373, 280, 158, 158], [154, 200, 75, 354], [241, 196], [88, 187, 137, 283], [43, 72, 252, 250], [77, 305, 292, 325], [49, 201, 284, 112], [356, 87]], ![[49, 6, 347, 83], [215, 217, 64, 316], [149, 16], [219, 276, 117, 362], [58, 249, 149, 377], [230, 194, 95, 118], [147, 204, 306, 324], [233, 87]]]
 h' := ![![[289, 244, 128], [146, 331, 6], [180, 366, 138], [272, 212, 18], [127, 9, 13], [291, 376, 119], [169, 187, 47], [0, 0, 1], [0, 1]], ![[365, 134, 251], [264, 249, 345], [212, 188, 152], [43, 62, 365], [193, 255, 241], [96, 188, 23], [325, 40, 293], [184, 288, 134], [289, 244, 128]], ![[0, 1], [23, 178, 28], [269, 204, 89], [225, 105, 375], [363, 115, 125], [294, 194, 237], [230, 152, 39], [57, 91, 244], [365, 134, 251]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [229, 284], []]
 b := ![[], [368, 133, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI379N0 : CertifiedPrimeIdeal' SI379N0 379 where
  n := 3
  hpos := by decide
  P := [282, 171, 104, 1]
  hirr := P379P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26343322, 20120993, -4916429, 12240695, 40514988]
  a := ![1, -4, -2, -5, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-17069925, -32665951, -40322802, 12240695, 40514988]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI379N0 : Ideal.IsPrime I379N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI379N0 B_one_repr
lemma NI379N0 : Nat.card (O ⧸ I379N0) = 54439939 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI379N0

def I379N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4625, 1479, 1485, 3549, -2088]] i)))

def SI379N1: IdealEqSpanCertificate' Table ![![4625, 1479, 1485, 3549, -2088]] 
 ![![379, 0, 0, 0, 0], ![0, 379, 0, 0, 0], ![336, 200, 1, 0, 0], ![262, 153, 0, 1, 0], ![23, 211, 0, 0, 1]] where
  M :=![![![4625, 1479, 1485, 3549, -2088], ![-16704, -7879, -4140, -15195, 8559], ![34236, 18573, 7316, 33414, -18513], ![-65700, -38274, -12771, -66589, 36585], ![92916, 54012, 18117, 94062, -51688]]]
  hmulB := by decide  
  f := ![![![2771, 10320, 11745, -687, -3096]], ![![-24768, -277, 22014, 2505, -5157]], ![![-10668, 8962, 22022, 720, -5463]], ![![-8038, 6996, 16929, 533, -4203]], ![![-13613, 458, 12942, 1353, -3052]]]
  g := ![![![-3631, -1050, 1485, 3549, -2088], ![13611, 3533, -4140, -15195, 8559], ![-28371, -6994, 7316, 33414, -18513], ![54961, 13152, -12771, -66589, 36585], ![-77704, -18614, 18117, 94062, -51688]]]
  hle1 := by decide   
  hle2 := by decide  


def P379P1 : CertificateIrreducibleZModOfList' 379 2 2 8 [201, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [290, 378], [0, 1]]
 g := ![![[189, 84], [72, 277], [227], [304, 311], [328, 149], [56, 226], [123, 341], [1]], ![[293, 295], [54, 102], [227], [292, 68], [332, 230], [29, 153], [94, 38], [1]]]
 h' := ![![[290, 378], [309, 40], [256, 203], [294, 201], [18, 93], [114, 161], [291, 329], [178, 290], [0, 1]], ![[0, 1], [160, 339], [2, 176], [218, 178], [79, 286], [187, 218], [193, 50], [140, 89], [290, 378]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [361]]
 b := ![[], [168, 370]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI379N1 : CertifiedPrimeIdeal' SI379N1 379 where
  n := 2
  hpos := by decide
  P := [201, 89, 1]
  hirr := P379P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4591, -1761, -1324, -5343, 6513]
  a := ![-1, 7, 6, 9, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4460, -775, -1324, -5343, 6513]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI379N1 : Ideal.IsPrime I379N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI379N1 B_one_repr
lemma NI379N1 : Nat.card (O ⧸ I379N1) = 143641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI379N1
def MulI379N0 : IdealMulLeCertificate' Table 
  ![![2771, 10320, 11745, -687, -3096]] ![![4625, 1479, 1485, 3549, -2088]]
  ![![379, 0, 0, 0, 0]] where
 M := ![![![379, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC379 : ContainsPrimesAboveP 379 ![I379N0, I379N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI379N0
    exact isPrimeI379N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 379 (by decide) (𝕀 ⊙ MulI379N0)
instance hp383 : Fact (Nat.Prime 383) := {out := by norm_num}

def I383N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-625, 287, -436, -23, 87]] i)))

def SI383N0: IdealEqSpanCertificate' Table ![![-625, 287, -436, -23, 87]] 
 ![![383, 0, 0, 0, 0], ![0, 383, 0, 0, 0], ![0, 0, 383, 0, 0], ![109, 196, 52, 1, 0], ![343, 218, 132, 0, 1]] where
  M :=![![![-625, 287, -436, -23, 87], ![696, -603, 620, -240, 18], ![72, 823, -363, 803, -351], ![-1752, -1123, -290, -1873, 1020], ![2416, 1617, 368, 2642, -1421]]]
  hmulB := by decide  
  f := ![![![1, 95, 130, -3, -33]], ![![-264, -31, 196, 32, -42]], ![![-168, -155, -63, 33, 27]], ![![-157, -10, 128, 20, -27]], ![![-207, 14, 206, 27, -44]]]
  g := ![![![-73, -37, -28, -23, 87], ![54, 111, 28, -240, 18], ![86, -209, 11, 803, -351], ![-385, 375, -98, -1873, 1020], ![527, -539, 132, 2642, -1421]]]
  hle1 := by decide   
  hle2 := by decide  


def P383P0 : CertificateIrreducibleZModOfList' 383 3 2 8 [28, 217, 82, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 354, 147], [250, 28, 236], [0, 1]]
 g := ![![[176, 5, 50], [375, 3, 378], [138, 85, 49], [252, 273, 309], [70, 269, 92], [355, 314, 223], [379, 301, 1], []], ![[113, 131, 237, 144], [37, 317, 259, 196], [343, 381, 184, 235], [263, 70, 122, 344], [256, 303, 115, 206], [342, 318, 13, 126], [78, 265, 99, 348], [103, 161]], ![[111, 256, 207, 61], [18, 291, 19, 369], [104, 173, 146, 245], [160, 336, 32, 15], [78, 102, 359, 167], [217, 342, 21, 91], [308, 280, 17, 82], [14, 161]]]
 h' := ![![[51, 354, 147], [224, 127, 81], [349, 46, 83], [221, 211, 7], [338, 199, 252], [18, 253, 104], [112, 100, 93], [0, 0, 1], [0, 1]], ![[250, 28, 236], [247, 168, 255], [271, 333, 277], [192, 25, 190], [68, 167, 307], [341, 123, 271], [341, 103, 69], [100, 57, 28], [51, 354, 147]], ![[0, 1], [228, 88, 47], [143, 4, 23], [168, 147, 186], [219, 17, 207], [10, 7, 8], [238, 180, 221], [62, 326, 354], [250, 28, 236]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [227, 40], []]
 b := ![[], [341, 159, 130], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI383N0 : CertifiedPrimeIdeal' SI383N0 383 where
  n := 3
  hpos := by decide
  P := [28, 217, 82, 1]
  hirr := P383P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9308900, -5493500, -1745344, -9455254, 4984806]
  a := ![0, -12, 0, -22, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1797584, 1987072, -438816, -9455254, 4984806]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI383N0 : Ideal.IsPrime I383N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI383N0 B_one_repr
lemma NI383N0 : Nat.card (O ⧸ I383N0) = 56181887 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI383N0

def I383N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, 253, 372, -8, -96]] i)))

def SI383N1: IdealEqSpanCertificate' Table ![![-25, 253, 372, -8, -96]] 
 ![![383, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![354, 0, 1, 0, 0], ![294, 0, 0, 1, 0], ![198, 0, 0, 0, 1]] where
  M :=![![![-25, 253, 372, -8, -96], ![-768, -125, 522, 80, -120], ![-480, -463, -205, 62, 60], ![624, -161, -786, -66, 183], ![120, -131, -288, -29, 56]]]
  hmulB := by decide  
  f := ![![![750409, -243209, 473922, 123184, -145068]], ![![38115, -12354, 24072, 6256, -7368]], ![![695934, -225551, 439517, 114244, -134538]], ![![575730, -186601, 363606, 94504, -111297]], ![![388554, -125923, 245388, 63791, -75118]]]
  g := ![![![-302, 253, 372, -8, -96], ![-477, -125, 522, 80, -120], ![135, -463, -205, 62, 60], ![693, -161, -786, -66, 183], ![267, -131, -288, -29, 56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI383N1 : Nat.card (O ⧸ I383N1) = 383 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI383N1)

lemma isPrimeI383N1 : Ideal.IsPrime I383N1 := prime_ideal_of_norm_prime hp383.out _ NI383N1

def I383N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-481, 156, -304, -79, 93]] i)))

def SI383N2: IdealEqSpanCertificate' Table ![![-481, 156, -304, -79, 93]] 
 ![![383, 0, 0, 0, 0], ![258, 1, 0, 0, 0], ![39, 0, 1, 0, 0], ![202, 0, 0, 1, 0], ![170, 0, 0, 0, 1]] where
  M :=![![![-481, 156, -304, -79, 93], ![744, -241, 470, 122, -144], ![-576, 186, -363, -95, 111], ![72, -24, 46, 12, -15], ![-152, 46, -94, -27, 28]]]
  hmulB := by decide  
  f := ![![![577, 174, -284, -77, 63]], ![![390, 119, -190, -52, 42]], ![![57, 18, -27, -8, 6]], ![![302, 90, -150, -40, 33]], ![![254, 76, -126, -35, 28]]]
  g := ![![![-75, 156, -304, -79, 93], ![116, -241, 470, 122, -144], ![-89, 186, -363, -95, 111], ![12, -24, 46, 12, -15], ![-20, 46, -94, -27, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI383N2 : Nat.card (O ⧸ I383N2) = 383 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI383N2)

lemma isPrimeI383N2 : Ideal.IsPrime I383N2 := prime_ideal_of_norm_prime hp383.out _ NI383N2
def MulI383N0 : IdealMulLeCertificate' Table 
  ![![-625, 287, -436, -23, 87]] ![![-25, 253, 372, -8, -96]]
  ![![577, 174, -284, -77, 63]] where
 M := ![![![577, 174, -284, -77, 63]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI383N1 : IdealMulLeCertificate' Table 
  ![![577, 174, -284, -77, 63]] ![![-481, 156, -304, -79, 93]]
  ![![383, 0, 0, 0, 0]] where
 M := ![![![383, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC383 : ContainsPrimesAboveP 383 ![I383N0, I383N1, I383N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI383N0
    exact isPrimeI383N1
    exact isPrimeI383N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 383 (by decide) (𝕀 ⊙ MulI383N0 ⊙ MulI383N1)
instance hp389 : Fact (Nat.Prime 389) := {out := by norm_num}

def I389N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-465, 185, -310, -44, 76]] i)))

def SI389N0: IdealEqSpanCertificate' Table ![![-465, 185, -310, -44, 76]] 
 ![![389, 0, 0, 0, 0], ![0, 389, 0, 0, 0], ![66, 290, 1, 0, 0], ![310, 152, 0, 1, 0], ![202, 265, 0, 0, 1]] where
  M :=![![![-465, 185, -310, -44, 76], ![608, -351, 458, -44, -56], ![-224, 415, -307, 284, -94], ![-680, -467, -98, -756, 407], ![912, 675, 108, 1059, -566]]]
  hmulB := by decide  
  f := ![![![-501, -143, 256, 44, -64]], ![![-512, -609, -374, 20, 68]], ![![-466, -479, -237, 22, 40]], ![![-598, -351, 58, 42, -25]], ![![-610, -490, -122, 35, 12]]]
  g := ![![![47, 197, -310, -44, 76], ![-12, -287, 458, -44, -56], ![-126, 183, -307, 284, -94], ![406, 90, -98, -756, 407], ![-566, -107, 108, 1059, -566]]]
  hle1 := by decide   
  hle2 := by decide  


def P389P0 : CertificateIrreducibleZModOfList' 389 2 2 8 [146, 351, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 388], [0, 1]]
 g := ![![[85, 46], [248], [191, 66], [62], [343], [309], [45], [38, 1]], ![[277, 343], [248], [365, 323], [62], [343], [309], [45], [76, 388]]]
 h' := ![![[38, 388], [71, 128], [122, 268], [190, 171], [92, 134], [34, 62], [333, 271], [287, 131], [0, 1]], ![[0, 1], [267, 261], [192, 121], [75, 218], [127, 255], [56, 327], [128, 118], [208, 258], [38, 388]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [351]]
 b := ![[], [361, 370]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI389N0 : CertifiedPrimeIdeal' SI389N0 389 where
  n := 2
  hpos := by decide
  P := [146, 351, 1]
  hirr := P389P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3206, 1302, 701, -681, 882]
  a := ![13, 5, 5, 6, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-26, -854, 701, -681, 882]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI389N0 : Ideal.IsPrime I389N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI389N0 B_one_repr
lemma NI389N0 : Nat.card (O ⧸ I389N0) = 151321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI389N0

def I389N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 23, 12, 2, 0]] i)))

def SI389N1: IdealEqSpanCertificate' Table ![![23, 23, 12, 2, 0]] 
 ![![389, 0, 0, 0, 0], ![0, 389, 0, 0, 0], ![113, 314, 1, 0, 0], ![306, 267, 0, 1, 0], ![32, 135, 0, 0, 1]] where
  M :=![![![23, 23, 12, 2, 0], ![0, 33, 42, 22, 6], ![24, 25, 11, 52, 36], ![144, 65, -48, 100, 93], ![312, 203, -18, 227, 188]]]
  hmulB := by decide  
  f := ![![![211, 11, 90, 110, -72]], ![![-576, -169, -198, -434, 258]], ![![-401, -132, -133, -316, 186]], ![![-234, -110, -66, -216, 123]], ![![-176, -54, -60, -135, 80]]]
  g := ![![![-5, -11, 12, 2, 0], ![-30, -51, 42, 22, 6], ![-47, -57, 11, 52, 36], ![-72, -62, -48, 100, 93], ![-188, -206, -18, 227, 188]]]
  hle1 := by decide   
  hle2 := by decide  


def P389P1 : CertificateIrreducibleZModOfList' 389 2 2 8 [178, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [316, 388], [0, 1]]
 g := ![![[361, 330], [269], [130, 80], [275], [385], [159], [278], [316, 1]], ![[0, 59], [269], [125, 309], [275], [385], [159], [278], [243, 388]]]
 h' := ![![[316, 388], [287, 313], [200, 293], [193, 344], [353, 100], [315, 159], [61, 275], [157, 94], [0, 1]], ![[0, 1], [0, 76], [206, 96], [366, 45], [55, 289], [378, 230], [214, 114], [297, 295], [316, 388]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [145]]
 b := ![[], [215, 267]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI389N1 : CertifiedPrimeIdeal' SI389N1 389 where
  n := 2
  hpos := by decide
  P := [178, 73, 1]
  hirr := P389P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![106, -136, -25, -261, 144]
  a := ![-1, -2, 0, -3, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![201, 149, -25, -261, 144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI389N1 : Ideal.IsPrime I389N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI389N1 B_one_repr
lemma NI389N1 : Nat.card (O ⧸ I389N1) = 151321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI389N1

def I389N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -4, -8, 0, 2]] i)))

def SI389N2: IdealEqSpanCertificate' Table ![![3, -4, -8, 0, 2]] 
 ![![389, 0, 0, 0, 0], ![348, 1, 0, 0, 0], ![132, 0, 1, 0, 0], ![198, 0, 0, 1, 0], ![253, 0, 0, 0, 1]] where
  M :=![![![3, -4, -8, 0, 2], ![16, 5, -8, -2, 2], ![8, 10, 7, 0, -2], ![-16, 0, 14, 1, -2], ![0, 4, 6, 4, -1]]]
  hmulB := by decide  
  f := ![![![759, -228, 476, 128, -146]], ![![676, -203, 424, 114, -130]], ![![260, -78, 163, 44, -50]], ![![386, -116, 242, 65, -74]], ![![495, -148, 310, 84, -95]]]
  g := ![![![5, -4, -8, 0, 2], ![-2, 5, -8, -2, 2], ![-10, 10, 7, 0, -2], ![-4, 0, 14, 1, -2], ![-7, 4, 6, 4, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI389N2 : Nat.card (O ⧸ I389N2) = 389 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI389N2)

lemma isPrimeI389N2 : Ideal.IsPrime I389N2 := prime_ideal_of_norm_prime hp389.out _ NI389N2
def MulI389N0 : IdealMulLeCertificate' Table 
  ![![-465, 185, -310, -44, 76]] ![![23, 23, 12, 2, 0]]
  ![![-759, 228, -476, -128, 146]] where
 M := ![![![-759, 228, -476, -128, 146]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI389N1 : IdealMulLeCertificate' Table 
  ![![-759, 228, -476, -128, 146]] ![![3, -4, -8, 0, 2]]
  ![![389, 0, 0, 0, 0]] where
 M := ![![![-389, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC389 : ContainsPrimesAboveP 389 ![I389N0, I389N1, I389N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI389N0
    exact isPrimeI389N1
    exact isPrimeI389N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 389 (by decide) (𝕀 ⊙ MulI389N0 ⊙ MulI389N1)
instance hp397 : Fact (Nat.Prime 397) := {out := by norm_num}

def I397N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3853, 1247, -2434, -632, 744]] i)))

def SI397N0: IdealEqSpanCertificate' Table ![![-3853, 1247, -2434, -632, 744]] 
 ![![397, 0, 0, 0, 0], ![0, 397, 0, 0, 0], ![0, 0, 397, 0, 0], ![259, 240, 169, 1, 0], ![19, 46, 231, 0, 1]] where
  M :=![![![-3853, 1247, -2434, -632, 744], ![5952, -1935, 3758, 972, -1152], ![-4608, 1489, -2907, -760, 882], ![552, -205, 370, 74, -123], ![-1232, 357, -748, -223, 196]]]
  hmulB := by decide  
  f := ![![![-1, 31, 44, 0, -12]], ![![-96, -17, 62, 4, -12]], ![![-48, -49, -21, 18, 0]], ![![-79, -11, 57, 10, -15]], ![![-39, -29, -3, 11, -2]]]
  g := ![![![367, 299, -170, -632, 744], ![-564, -459, 266, 972, -1152], ![442, 361, -197, -760, 882], ![-41, -31, 41, 74, -123], ![133, 113, -21, -223, 196]]]
  hle1 := by decide   
  hle2 := by decide  


def P397P0 : CertificateIrreducibleZModOfList' 397 3 2 8 [212, 105, 175, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [363, 227, 387], [256, 169, 10], [0, 1]]
 g := ![![[326, 25, 81], [64, 271], [60, 69, 386], [124, 382, 163], [64, 1], [355, 246], [351, 56], [1]], ![[186, 54, 21, 127], [250, 111], [127, 173, 25, 69], [325, 309, 269, 31], [298, 229], [202, 78], [188, 305], [310, 382, 136, 191]], ![[46, 206, 1, 205], [93, 195], [248, 64, 93, 160], [232, 303, 257, 169], [123, 163], [55, 370], [383, 355], [216, 167, 358, 206]]]
 h' := ![![[363, 227, 387], [186, 39, 9], [381, 363, 335], [311, 10, 66], [52, 347, 231], [330, 79, 396], [307, 160, 55], [185, 292, 222], [0, 1]], ![[256, 169, 10], [228, 291, 337], [53, 184, 184], [78, 223, 335], [340, 343, 236], [271, 93, 232], [51, 9, 152], [181, 390, 59], [363, 227, 387]], ![[0, 1], [270, 67, 51], [327, 247, 275], [143, 164, 393], [333, 104, 327], [216, 225, 166], [220, 228, 190], [256, 112, 116], [256, 169, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [138, 314], []]
 b := ![[], [335, 57, 349], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI397N0 : CertifiedPrimeIdeal' SI397N0 397 where
  n := 3
  hpos := by decide
  P := [212, 105, 175, 1]
  hirr := P397P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-708847, -433766, -110617, -743302, 416442]
  a := ![3, -4, 7, -8, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![463209, 400006, 73827, -743302, 416442]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI397N0 : Ideal.IsPrime I397N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI397N0 B_one_repr
lemma NI397N0 : Nat.card (O ⧸ I397N0) = 62570773 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI397N0

def I397N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![187, -249, -513, -7, 130]] i)))

def SI397N1: IdealEqSpanCertificate' Table ![![187, -249, -513, -7, 130]] 
 ![![397, 0, 0, 0, 0], ![190, 1, 0, 0, 0], ![212, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![375, 0, 0, 0, 1]] where
  M :=![![![187, -249, -513, -7, 130], ![1040, 331, -484, -109, 109], ![436, 605, 440, -48, -109], ![-956, 24, 895, 137, -181], ![-164, 154, 355, 106, -20]]]
  hmulB := by decide  
  f := ![![![-222113, -132694, -41583, -228209, 125002]], ![![-103782, -62021, -19420, -106649, 58415]], ![![-124248, -74168, -23290, -127602, 69901]], ![![4624, 2627, 931, 4624, -2548]], ![![-225815, -134715, -42368, -231834, 127009]]]
  g := ![![![271, -249, -513, -7, 130], ![3, 331, -484, -109, 109], ![-419, 605, 440, -48, -109], ![-325, 24, 895, 137, -181], ![-248, 154, 355, 106, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI397N1 : Nat.card (O ⧸ I397N1) = 397 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI397N1)

lemma isPrimeI397N1 : Ideal.IsPrime I397N1 := prime_ideal_of_norm_prime hp397.out _ NI397N1

def I397N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22677, 13275, 4377, 23044, -12653]] i)))

def SI397N2: IdealEqSpanCertificate' Table ![![22677, 13275, 4377, 23044, -12653]] 
 ![![397, 0, 0, 0, 0], ![266, 1, 0, 0, 0], ![352, 0, 1, 0, 0], ![294, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![22677, 13275, 4377, 23044, -12653], ![-101224, -59255, -19538, -102861, 56479], ![225916, 132247, 43606, 229569, -126052], ![-453596, -265526, -87553, -460930, 253088], ![640572, 374978, 123643, 650929, -357413]]]
  hmulB := by decide  
  f := ![![![-2679, -1008, 561, 160, -149]], ![![-1798, -683, 370, 107, -99]], ![![-2372, -896, 490, 139, -132]], ![![-1982, -743, 419, 113, -115]], ![![-186, -73, 37, 0, -18]]]
  g := ![![![-28955, 13275, 4377, 23044, -12653], ![129246, -59255, -19538, -102861, 56479], ![-288456, 132247, 43606, 229569, -126052], ![579164, -265526, -87553, -460930, 253088], ![-817900, 374978, 123643, 650929, -357413]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI397N2 : Nat.card (O ⧸ I397N2) = 397 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI397N2)

lemma isPrimeI397N2 : Ideal.IsPrime I397N2 := prime_ideal_of_norm_prime hp397.out _ NI397N2
def MulI397N0 : IdealMulLeCertificate' Table 
  ![![-3853, 1247, -2434, -632, 744]] ![![187, -249, -513, -7, 130]]
  ![![-2679, -1008, 561, 160, -149]] where
 M := ![![![-2679, -1008, 561, 160, -149]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI397N1 : IdealMulLeCertificate' Table 
  ![![-2679, -1008, 561, 160, -149]] ![![22677, 13275, 4377, 23044, -12653]]
  ![![397, 0, 0, 0, 0]] where
 M := ![![![397, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC397 : ContainsPrimesAboveP 397 ![I397N0, I397N1, I397N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI397N0
    exact isPrimeI397N1
    exact isPrimeI397N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 397 (by decide) (𝕀 ⊙ MulI397N0 ⊙ MulI397N1)
instance hp401 : Fact (Nat.Prime 401) := {out := by norm_num}

def I401N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![85569, -24401, 52446, 17196, -17962]] i)))

def SI401N0: IdealEqSpanCertificate' Table ![![85569, -24401, 52446, 17196, -17962]] 
 ![![401, 0, 0, 0, 0], ![0, 401, 0, 0, 0], ![0, 0, 401, 0, 0], ![0, 0, 0, 401, 0], ![113, 136, 342, 241, 1]] where
  M :=![![![85569, -24401, 52446, 17196, -17962], ![-143696, 31009, -83194, -38038, 33626], ![134504, -10361, 69047, 53516, -40244], ![-89128, -41097, -22280, -79546, 43339], ![127632, 51341, 36506, 109269, -66274]]]
  hmulB := by decide  
  f := ![![![-11775, -1289, 8868, 1232, -2042]], ![![-16336, -14349, -5042, 2210, 1654]], ![![6616, -7659, -16559, -358, 4142]], ![![24736, 12737, -4780, -2988, 707]], ![![11673, -4099, -16216, -1007, 3945]]]
  g := ![![![5275, 6031, 15450, 10838, -17962], ![-9834, -11327, -28886, -20304, 33626], ![11676, 13623, 34495, 24320, -40244], ![-12435, -14801, -37018, -26245, 43339], ![18994, 22605, 56614, 40103, -66274]]]
  hle1 := by decide   
  hle2 := by decide  


def P401P0 : CertificateIrreducibleZModOfList' 401 4 2 8 [41, 74, 146, 237, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [314, 313, 24, 212], [196, 331, 229, 288], [55, 157, 148, 302], [0, 1]]
 g := ![![[364, 322, 383, 116], [84, 190, 45], [207, 262, 183], [122, 224, 8], [160, 321, 367, 36], [397, 126, 379], [284, 164, 1], []], ![[311, 316, 388, 51, 28, 296], [189, 329, 186], [306, 93, 323], [69, 140, 390], [307, 148, 222, 83, 11, 370], [203, 82, 352], [270, 52, 299], [83, 321, 305, 161, 100, 368]], ![[137, 153, 249, 298, 269, 357], [31, 186, 250], [99, 255, 320], [47, 377, 186], [245, 383, 258, 215, 214, 324], [298, 329, 121], [386, 240, 242], [30, 11, 375, 2, 232, 302]], ![[25, 29, 207, 170, 114, 352], [21, 251, 308], [335, 367, 63], [331, 147, 14], [324, 0, 345, 382, 235, 166], [237, 52, 328], [23, 336, 180], [97, 31, 180, 64, 187, 121]]]
 h' := ![![[314, 313, 24, 212], [87, 5, 70, 328], [137, 237, 21, 268], [95, 398, 269, 298], [257, 5, 391, 295], [389, 67, 27, 395], [386, 330, 93, 102], [0, 0, 0, 1], [0, 1]], ![[196, 331, 229, 288], [42, 113, 91, 208], [217, 34, 108, 304], [357, 223, 28, 137], [299, 160, 222, 297], [186, 313, 387, 335], [331, 87, 140, 261], [145, 313, 9, 353], [314, 313, 24, 212]], ![[55, 157, 148, 302], [353, 330, 27, 209], [356, 198, 87, 148], [399, 217, 340, 221], [205, 123, 393, 304], [87, 210, 216, 140], [26, 140, 79, 11], [333, 94, 275, 182], [196, 331, 229, 288]], ![[0, 1], [23, 354, 213, 57], [214, 333, 185, 82], [77, 365, 165, 146], [307, 113, 197, 307], [351, 212, 172, 333], [309, 245, 89, 27], [394, 395, 117, 266], [55, 157, 148, 302]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [158, 384, 68], []]
 b := ![[], [], [370, 170, 48, 139], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI401N0 : CertifiedPrimeIdeal' SI401N0 401 where
  n := 4
  hpos := by decide
  P := [41, 74, 146, 237, 1]
  hirr := P401P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-301674617, -128968136, -159489560, -453401383, 727002809]
  a := ![1, -4, -4, -5, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-205618434, -246886160, -620435038, -438057552, 727002809]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI401N0 : Ideal.IsPrime I401N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI401N0 B_one_repr
lemma NI401N0 : Nat.card (O ⧸ I401N0) = 25856961601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI401N0

def I401N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11775, 1289, -8868, -1232, 2042]] i)))

def SI401N1: IdealEqSpanCertificate' Table ![![11775, 1289, -8868, -1232, 2042]] 
 ![![401, 0, 0, 0, 0], ![78, 1, 0, 0, 0], ![166, 0, 1, 0, 0], ![304, 0, 0, 1, 0], ![354, 0, 0, 0, 1]] where
  M :=![![![11775, 1289, -8868, -1232, 2042], ![16336, 14349, 5042, -2210, -1654], ![-6616, 7659, 16559, 358, -4142], ![-24736, -12737, 4780, 2988, -707], ![-9096, -3183, 3830, 1039, -796]]]
  hmulB := by decide  
  f := ![![![-85569, 24401, -52446, -17196, 17962]], ![![-16286, 4669, -9994, -3250, 3410]], ![![-35758, 10127, -21883, -7252, 7536]], ![![-64648, 18601, -39704, -12838, 13509]], ![![-75858, 21413, -46390, -15453, 16022]]]
  g := ![![![2581, 1289, -8868, -1232, 2042], ![-1702, 14349, 5042, -2210, -1654], ![-4976, 7659, 16559, 358, -4142], ![-1204, -12737, 4780, 2988, -707], ![-1074, -3183, 3830, 1039, -796]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI401N1 : Nat.card (O ⧸ I401N1) = 401 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI401N1)

lemma isPrimeI401N1 : Ideal.IsPrime I401N1 := prime_ideal_of_norm_prime hp401.out _ NI401N1
def MulI401N0 : IdealMulLeCertificate' Table 
  ![![85569, -24401, 52446, 17196, -17962]] ![![11775, 1289, -8868, -1232, 2042]]
  ![![401, 0, 0, 0, 0]] where
 M := ![![![-401, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC401 : ContainsPrimesAboveP 401 ![I401N0, I401N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI401N0
    exact isPrimeI401N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 401 (by decide) (𝕀 ⊙ MulI401N0)
instance hp409 : Fact (Nat.Prime 409) := {out := by norm_num}

def I409N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16767, -6595, 11149, 1665, -2776]] i)))

def SI409N0: IdealEqSpanCertificate' Table ![![16767, -6595, 11149, 1665, -2776]] 
 ![![409, 0, 0, 0, 0], ![0, 409, 0, 0, 0], ![258, 215, 1, 0, 0], ![154, 326, 0, 1, 0], ![48, 66, 0, 0, 1]] where
  M :=![![![16767, -6595, 11149, 1665, -2776], ![-22208, 12371, -16520, 1201, 2219], ![8876, -14417, 11170, -9354, 2911], ![22748, 15792, 3197, 25435, -13685], ![-30396, -22862, -3423, -35636, 18992]]]
  hmulB := by decide  
  f := ![![![-801, -24, 631, 1045, 542]], ![![4336, 1495, -2138, 4011, 3677]], ![![1810, 791, -732, 2789, 2294]], ![![3226, 1233, -1465, 3636, 3172]], ![![756, 341, -273, 875, 743]]]
  g := ![![![-7293, -6756, 11149, 1665, -2776], ![9654, 7399, -16520, 1201, 2219], ![-3844, 1079, 11170, -9354, 2911], ![-9932, -19707, 3197, 25435, -13685], ![13274, 27083, -3423, -35636, 18992]]]
  hle1 := by decide   
  hle2 := by decide  


def P409P0 : CertificateIrreducibleZModOfList' 409 2 2 8 [49, 343, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [66, 408], [0, 1]]
 g := ![![[7, 192], [309], [225], [306, 213], [87, 92], [225], [54], [66, 1]], ![[0, 217], [309], [225], [49, 196], [24, 317], [225], [54], [132, 408]]]
 h' := ![![[66, 408], [360, 292], [116, 206], [139, 15], [236, 366], [234, 58], [25, 15], [38, 217], [0, 1]], ![[0, 1], [0, 117], [215, 203], [311, 394], [261, 43], [381, 351], [197, 394], [45, 192], [66, 408]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [36, 222]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI409N0 : CertifiedPrimeIdeal' SI409N0 409 where
  n := 2
  hpos := by decide
  P := [49, 343, 1]
  hirr := P409P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1389, 324, -362, 641, 63]
  a := ![4, 1, -1, 2, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-17, -330, -362, 641, 63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI409N0 : Ideal.IsPrime I409N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI409N0 B_one_repr
lemma NI409N0 : Nat.card (O ⧸ I409N0) = 167281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI409N0

def I409N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17985, 7791, -5505, -2114, 1039]] i)))

def SI409N1: IdealEqSpanCertificate' Table ![![17985, 7791, -5505, -2114, 1039]] 
 ![![409, 0, 0, 0, 0], ![0, 409, 0, 0, 0], ![296, 169, 1, 0, 0], ![283, 13, 0, 1, 0], ![44, 246, 0, 0, 1]] where
  M :=![![![17985, 7791, -5505, -2114, 1039], ![8312, 19789, 19810, -1623, -5303], ![-21212, 1615, 21412, 2061, -5086], ![-24500, -23540, -10351, 3392, 3200], ![-11004, -7588, -527, 1399, 367]]]
  hmulB := by decide  
  f := ![![![-27399, -19248, -3741, -30848, 16573]], ![![132584, 82573, 23200, 139377, -75971]], ![![34212, 19745, 6740, 34502, -18979]], ![![-13233, -9808, -1560, -15378, 8209]], ![![74664, 46343, 13141, 78342, -42720]]]
  g := ![![![5379, 1736, -5505, -2114, 1039], ![-12623, -4896, 19810, -1623, -5303], ![-16427, -5850, 21412, 2061, -5086], ![4740, 2187, -10351, 3392, 3200], ![-653, -66, -527, 1399, 367]]]
  hle1 := by decide   
  hle2 := by decide  


def P409P1 : CertificateIrreducibleZModOfList' 409 2 2 8 [379, 282, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [127, 408], [0, 1]]
 g := ![![[236, 259], [136], [131], [81, 144], [194, 205], [406], [319], [127, 1]], ![[0, 150], [136], [131], [373, 265], [53, 204], [406], [319], [254, 408]]]
 h' := ![![[127, 408], [39, 48], [7, 172], [385, 130], [94, 397], [317, 156], [35, 107], [129, 208], [0, 1]], ![[0, 1], [0, 361], [174, 237], [126, 279], [206, 12], [88, 253], [127, 302], [369, 201], [127, 408]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129]]
 b := ![[], [301, 269]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI409N1 : CertifiedPrimeIdeal' SI409N1 409 where
  n := 2
  hpos := by decide
  P := [379, 282, 1]
  hirr := P409P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2306, -1046, -8010, -406, 1706]
  a := ![7, -1, -26, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5900, 2294, -8010, -406, 1706]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI409N1 : Ideal.IsPrime I409N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI409N1 B_one_repr
lemma NI409N1 : Nat.card (O ⧸ I409N1) = 167281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI409N1

def I409N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, -11, 19, 5, -6]] i)))

def SI409N2: IdealEqSpanCertificate' Table ![![31, -11, 19, 5, -6]] 
 ![![409, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![386, 0, 1, 0, 0], ![141, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![31, -11, 19, 5, -6], ![-48, 15, -32, -9, 9], ![36, -13, 24, 4, -9], ![-12, -2, -1, -5, -3], ![-4, -12, 7, -8, -10]]]
  hmulB := by decide  
  f := ![![![127, 128, 97, 99, -78]], ![![14, 15, 12, 11, -9]], ![![122, 122, 92, 96, -75]], ![![39, 41, 32, 29, -24]], ![![12, 9, 5, 11, -7]]]
  g := ![![![-18, -11, 19, 5, -6], ![31, 15, -32, -9, 9], ![-22, -13, 24, 4, -9], ![3, -2, -1, -5, -3], ![-2, -12, 7, -8, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI409N2 : Nat.card (O ⧸ I409N2) = 409 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI409N2)

lemma isPrimeI409N2 : Ideal.IsPrime I409N2 := prime_ideal_of_norm_prime hp409.out _ NI409N2
def MulI409N0 : IdealMulLeCertificate' Table 
  ![![16767, -6595, 11149, 1665, -2776]] ![![17985, 7791, -5505, -2114, 1039]]
  ![![-1129, -935, 1640, 392, -408]] where
 M := ![![![-1129, -935, 1640, 392, -408]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI409N1 : IdealMulLeCertificate' Table 
  ![![-1129, -935, 1640, 392, -408]] ![![31, -11, 19, 5, -6]]
  ![![409, 0, 0, 0, 0]] where
 M := ![![![65849, -18814, 44581, 10634, -13497]]]
 hmul := by decide  
 g := ![![![![161, -46, 109, 26, -33]]]]
 hle2 := by decide  


def PBC409 : ContainsPrimesAboveP 409 ![I409N0, I409N1, I409N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI409N0
    exact isPrimeI409N1
    exact isPrimeI409N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 409 (by decide) (𝕀 ⊙ MulI409N0 ⊙ MulI409N1)
instance hp419 : Fact (Nat.Prime 419) := {out := by norm_num}

def I419N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19031, -6170, 12020, 3122, -3678]] i)))

def SI419N0: IdealEqSpanCertificate' Table ![![19031, -6170, 12020, 3122, -3678]] 
 ![![419, 0, 0, 0, 0], ![0, 419, 0, 0, 0], ![61, 288, 1, 0, 0], ![30, 49, 0, 1, 0], ![153, 28, 0, 0, 1]] where
  M :=![![![19031, -6170, 12020, 3122, -3678], ![-29424, 9539, -18584, -4828, 5688], ![22752, -7370, 14367, 3738, -4398], ![-2880, 926, -1816, -481, 564], ![5904, -1890, 3716, 988, -1141]]]
  hmulB := by decide  
  f := ![![![1045, -234, -1268, -94, 306]], ![![2448, 1401, -280, -300, 24]], ![![1835, 932, -373, -220, 60]], ![![354, 145, -120, -41, 24]], ![![543, 8, -480, -54, 113]]]
  g := ![![![-585, -8396, 12020, 3122, -3678], ![904, 12981, -18584, -4828, 5688], ![-699, -10036, 14367, 3738, -4398], ![86, 1269, -1816, -481, 564], ![-181, -2598, 3716, 988, -1141]]]
  hle1 := by decide   
  hle2 := by decide  


def P419P0 : CertificateIrreducibleZModOfList' 419 2 2 8 [252, 137, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [282, 418], [0, 1]]
 g := ![![[368, 281], [101, 180], [348], [80], [148], [370, 257], [276], [282, 1]], ![[0, 138], [162, 239], [348], [80], [148], [357, 162], [276], [145, 418]]]
 h' := ![![[282, 418], [107, 117], [167, 246], [124, 102], [256, 164], [197, 188], [323, 393], [166, 81], [0, 1]], ![[0, 1], [0, 302], [404, 173], [396, 317], [414, 255], [0, 231], [114, 26], [382, 338], [282, 418]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [347]]
 b := ![[], [48, 383]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI419N0 : CertifiedPrimeIdeal' SI419N0 419 where
  n := 2
  hpos := by decide
  P := [252, 137, 1]
  hirr := P419P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![510, 47, -721, -78, 87]
  a := ![1, 0, -5, -1, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![80, 499, -721, -78, 87]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI419N0 : Ideal.IsPrime I419N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI419N0 B_one_repr
lemma NI419N0 : Nat.card (O ⧸ I419N0) = 175561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI419N0

def I419N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55865, -18185, 35331, 9124, -10851]] i)))

def SI419N1: IdealEqSpanCertificate' Table ![![55865, -18185, 35331, 9124, -10851]] 
 ![![419, 0, 0, 0, 0], ![0, 419, 0, 0, 0], ![180, 365, 1, 0, 0], ![83, 317, 0, 1, 0], ![97, 196, 0, 0, 1]] where
  M :=![![![55865, -18185, 35331, 9124, -10851], ![-86808, 27817, -54618, -14419, 16521], ![66084, -22201, 42236, 10415, -13368], ![-10068, 1624, -5307, -2550, 678], ![13572, -8132, 10965, 181, -5503]]]
  hmulB := by decide  
  f := ![![![43, 7840, 10785, -326, -2787]], ![![-22296, -2781, 16332, 2387, -3765]], ![![-19440, 913, 18848, 1944, -4473]], ![![-16817, -564, 14436, 1738, -3387]], ![![-10411, 505, 10116, 1040, -2401]]]
  g := ![![![-14340, -32648, 35331, 9124, -10851], ![22288, 50826, -54618, -14419, 16521], ![-16955, -38472, 42236, 10415, -13368], ![2604, 6239, -5307, -2550, 678], ![-3440, -7134, 10965, 181, -5503]]]
  hle1 := by decide   
  hle2 := by decide  


def P419P1 : CertificateIrreducibleZModOfList' 419 2 2 8 [165, 356, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 418], [0, 1]]
 g := ![![[411, 37], [222, 257], [186], [366], [15], [91, 337], [251], [63, 1]], ![[228, 382], [72, 162], [186], [366], [15], [372, 82], [251], [126, 418]]]
 h' := ![![[63, 418], [242, 325], [154, 393], [393, 387], [191, 273], [69, 68], [181, 143], [80, 33], [0, 1]], ![[0, 1], [186, 94], [192, 26], [53, 32], [211, 146], [163, 351], [391, 276], [64, 386], [63, 418]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [156]]
 b := ![[], [57, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI419N1 : CertifiedPrimeIdeal' SI419N1 419 where
  n := 2
  hpos := by decide
  P := [165, 356, 1]
  hirr := P419P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3882, 3278, -76, 4956, 2964]
  a := ![3, 4, 0, 9, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1626, -5062, -76, 4956, 2964]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI419N1 : Ideal.IsPrime I419N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI419N1 B_one_repr
lemma NI419N1 : Nat.card (O ⧸ I419N1) = 175561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI419N1

def I419N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![267, 102, -101, -23, 26]] i)))

def SI419N2: IdealEqSpanCertificate' Table ![![267, 102, -101, -23, 26]] 
 ![![419, 0, 0, 0, 0], ![370, 1, 0, 0, 0], ![266, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![246, 0, 0, 0, 1]] where
  M :=![![![267, 102, -101, -23, 26], ![208, 319, 250, 3, -43], ![-172, 120, 316, 98, -17], ![-172, -179, -103, 206, 160], ![324, 233, 3, 371, 287]]]
  hmulB := by decide  
  f := ![![![262401, 151657, 51587, 264819, -145628]], ![![228934, 132301, 45014, 231031, -127049]], ![![172778, 99899, 33948, 174408, -95905]], ![![17009, 9739, 3388, 17080, -9403]], ![![171606, 99310, 33675, 173308, -95290]]]
  g := ![![![-38, 102, -101, -23, 26], ![-415, 319, 250, 3, -43], ![-308, 120, 316, 98, -17], ![106, -179, -103, 206, 160], ![-417, 233, 3, 371, 287]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI419N2 : Nat.card (O ⧸ I419N2) = 419 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI419N2)

lemma isPrimeI419N2 : Ideal.IsPrime I419N2 := prime_ideal_of_norm_prime hp419.out _ NI419N2
def MulI419N0 : IdealMulLeCertificate' Table 
  ![![19031, -6170, 12020, 3122, -3678]] ![![55865, -18185, 35331, 9124, -10851]]
  ![![2311751743, -749586021, 1460156317, 379165556, -446766561]] where
 M := ![![![2311751743, -749586021, 1460156317, 379165556, -446766561]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI419N1 : IdealMulLeCertificate' Table 
  ![![2311751743, -749586021, 1460156317, 379165556, -446766561]] ![![267, 102, -101, -23, 26]]
  ![![419, 0, 0, 0, 0]] where
 M := ![![![208095093, -67748110, 131612928, 33981319, -40427215]]]
 hmul := by decide  
 g := ![![![![496647, -161690, 314112, 81101, -96485]]]]
 hle2 := by decide  


def PBC419 : ContainsPrimesAboveP 419 ![I419N0, I419N1, I419N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI419N0
    exact isPrimeI419N1
    exact isPrimeI419N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 419 (by decide) (𝕀 ⊙ MulI419N0 ⊙ MulI419N1)


lemma PB1072I8_primes (p : ℕ) :
  p ∈ Set.range ![367, 373, 379, 383, 389, 397, 401, 409, 419] ↔ Nat.Prime p ∧ 359 < p ∧ p ≤ 419 := by
  rw [← List.mem_ofFn']
  convert primes_range 359 419 (by omega)

def PB1072I8 : PrimesBelowBoundCertificateInterval O 359 419 1072 where
  m := 9
  g := ![2, 3, 2, 3, 3, 3, 2, 3, 3]
  P := ![367, 373, 379, 383, 389, 397, 401, 409, 419]
  hP := PB1072I8_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I367N0, I367N1]
    · exact ![I373N0, I373N1, I373N2]
    · exact ![I379N0, I379N1]
    · exact ![I383N0, I383N1, I383N2]
    · exact ![I389N0, I389N1, I389N2]
    · exact ![I397N0, I397N1, I397N2]
    · exact ![I401N0, I401N1]
    · exact ![I409N0, I409N1, I409N2]
    · exact ![I419N0, I419N1, I419N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC367
    · exact PBC373
    · exact PBC379
    · exact PBC383
    · exact PBC389
    · exact PBC397
    · exact PBC401
    · exact PBC409
    · exact PBC419
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![18141126721, 367]
    · exact ![139129, 139129, 373]
    · exact ![54439939, 143641]
    · exact ![56181887, 383, 383]
    · exact ![151321, 151321, 389]
    · exact ![62570773, 397, 397]
    · exact ![25856961601, 401]
    · exact ![167281, 167281, 409]
    · exact ![175561, 175561, 419]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI367N0
      exact NI367N1
    · dsimp ; intro j
      fin_cases j
      exact NI373N0
      exact NI373N1
      exact NI373N2
    · dsimp ; intro j
      fin_cases j
      exact NI379N0
      exact NI379N1
    · dsimp ; intro j
      fin_cases j
      exact NI383N0
      exact NI383N1
      exact NI383N2
    · dsimp ; intro j
      fin_cases j
      exact NI389N0
      exact NI389N1
      exact NI389N2
    · dsimp ; intro j
      fin_cases j
      exact NI397N0
      exact NI397N1
      exact NI397N2
    · dsimp ; intro j
      fin_cases j
      exact NI401N0
      exact NI401N1
    · dsimp ; intro j
      fin_cases j
      exact NI409N0
      exact NI409N1
      exact NI409N2
    · dsimp ; intro j
      fin_cases j
      exact NI419N0
      exact NI419N1
      exact NI419N2
  β := ![I367N1, I373N2, I383N1, I383N2, I389N2, I397N1, I397N2, I401N1, I409N2, I419N2]
  Il := ![[I367N1], [I373N2], [], [I383N1, I383N2], [I389N2], [I397N1, I397N2], [I401N1], [I409N2], [I419N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
