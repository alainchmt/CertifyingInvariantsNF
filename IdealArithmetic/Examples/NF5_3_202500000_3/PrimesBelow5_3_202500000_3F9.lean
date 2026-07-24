
import IdealArithmetic.Examples.NF5_3_202500000_3.RI5_3_202500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp421 : Fact (Nat.Prime 421) := {out := by norm_num}

def I421N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![253, 185, 209, -144, -388]] i)))

def SI421N0: IdealEqSpanCertificate' Table ![![253, 185, 209, -144, -388]] 
 ![![421, 0, 0, 0, 0], ![0, 421, 0, 0, 0], ![0, 0, 421, 0, 0], ![226, 264, 296, 1, 0], ![407, 137, 86, 0, 1]] where
  M :=![![![253, 185, 209, -144, -388], ![528, 362, 457, -310, -832], ![1176, 773, 1000, -686, -1896], ![708, 645, 425, -341, -804], ![468, 245, 467, -302, -879]]]
  hmulB := by decide  
  f := ![![![-47, 35, 65, -40, -116]], ![![48, -18, -21, 10, 32]], ![![24, 39, 44, -42, -104]], ![![22, 35, 53, -45, -116]], ![![-25, 36, 65, -44, -123]]]
  g := ![![![453, 217, 181, -144, -388], ![972, 466, 389, -310, -832], ![2204, 1049, 872, -686, -1896], ![962, 477, 405, -341, -804], ![1013, 476, 393, -302, -879]]]
  hle1 := by decide   
  hle2 := by decide  


def P421P0 : CertificateIrreducibleZModOfList' 421 3 2 8 [286, 118, 347, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [212, 258, 97], [283, 162, 324], [0, 1]]
 g := ![![[276, 345, 339], [344, 63], [119, 386, 317], [295, 327], [295, 189], [326, 276, 169], [19, 3], [1]], ![[365, 61, 317, 1], [344, 112], [262, 134, 159, 135], [97, 75], [306, 372], [71, 420, 39, 254], [354, 327], [305, 368, 248, 366]], ![[142, 80, 266, 17], [252, 7], [334, 172, 326, 146], [404, 114], [164, 138], [123, 173, 405, 337], [266, 135], [332, 324, 153, 55]]]
 h' := ![![[212, 258, 97], [409, 391, 265], [67, 79, 399], [213, 48, 321], [386, 271, 300], [226, 295, 56], [161, 404, 13], [135, 303, 74], [0, 1]], ![[283, 162, 324], [321, 3, 25], [255, 343, 310], [333, 216, 244], [17, 330, 370], [128, 206, 218], [104, 126, 36], [394, 65, 121], [212, 258, 97]], ![[0, 1], [103, 27, 131], [326, 420, 133], [1, 157, 277], [166, 241, 172], [265, 341, 147], [141, 312, 372], [4, 53, 226], [283, 162, 324]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101, 198], []]
 b := ![[], [390, 30, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI421N0 : CertifiedPrimeIdeal' SI421N0 421 where
  n := 3
  hpos := by decide
  P := [286, 118, 347, 1]
  hirr := P421P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![142389430, 34658927, 144596684, -116431159, -308861434]
  a := ![153, 6, 189, -140, -391]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![361430962, 173602141, 145297632, -116431159, -308861434]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI421N0 : Ideal.IsPrime I421N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI421N0 B_one_repr
lemma NI421N0 : Nat.card (O ⧸ I421N0) = 74618461 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI421N0

def I421N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, -35, -65, 40, 116]] i)))

def SI421N1: IdealEqSpanCertificate' Table ![![47, -35, -65, 40, 116]] 
 ![![421, 0, 0, 0, 0], ![0, 421, 0, 0, 0], ![71, 250, 1, 0, 0], ![387, 361, 0, 1, 0], ![335, 77, 0, 0, 1]] where
  M :=![![![47, -35, -65, 40, 116], ![-48, 18, 21, -10, -32], ![-24, -39, -44, 42, 104], ![-108, -33, -143, 113, 284], ![36, -23, -3, 2, 11]]]
  hmulB := by decide  
  f := ![![![-253, -185, -209, 144, 388]], ![![-528, -362, -457, 310, 832]], ![![-359, -248, -309, 210, 564]], ![![-687, -482, -585, 399, 1072]], ![![-299, -214, -251, 172, 463]]]
  g := ![![![-118, -17, -65, 40, 116], ![31, 2, 21, -10, -32], ![-114, -29, -44, 42, 104], ![-306, -64, -143, 113, 284], ![-10, -2, -3, 2, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P421P1 : CertificateIrreducibleZModOfList' 421 2 2 8 [92, 379, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 420], [0, 1]]
 g := ![![[27, 346], [106], [286, 220], [277], [99], [406, 67], [144], [42, 1]], ![[245, 75], [106], [264, 201], [277], [99], [273, 354], [144], [84, 420]]]
 h' := ![![[42, 420], [247, 205], [211, 384], [171, 124], [371, 73], [117, 283], [376, 270], [346, 409], [0, 1]], ![[0, 1], [16, 216], [341, 37], [327, 297], [69, 348], [215, 138], [349, 151], [263, 12], [42, 420]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [345]]
 b := ![[], [377, 383]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI421N1 : CertifiedPrimeIdeal' SI421N1 421 where
  n := 2
  hpos := by decide
  P := [92, 379, 1]
  hirr := P421P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-366394, 145094, -927541, 572369, 1446314]
  a := ![-183, -72, -226, 103, 468]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1521456, -204183, -927541, 572369, 1446314]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI421N1 : Ideal.IsPrime I421N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI421N1 B_one_repr
lemma NI421N1 : Nat.card (O ⧸ I421N1) = 177241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI421N1
def MulI421N0 : IdealMulLeCertificate' Table 
  ![![253, 185, 209, -144, -388]] ![![47, -35, -65, 40, 116]]
  ![![421, 0, 0, 0, 0]] where
 M := ![![![-421, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC421 : ContainsPrimesAboveP 421 ![I421N0, I421N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI421N0
    exact isPrimeI421N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 421 (by decide) (𝕀 ⊙ MulI421N0)
instance hp431 : Fact (Nat.Prime 431) := {out := by norm_num}

def I431N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![230795, 162777, 193410, -131871, -356432]] i)))

def SI431N0: IdealEqSpanCertificate' Table ![![230795, 162777, 193410, -131871, -356432]] 
 ![![431, 0, 0, 0, 0], ![0, 431, 0, 0, 0], ![0, 0, 431, 0, 0], ![0, 0, 0, 431, 0], ![42, 58, 323, 3, 1]] where
  M :=![![![230795, 162777, 193410, -131871, -356432], ![470172, 331515, 394060, -268732, -726308], ![958656, 675388, 803527, -548224, -1481488], ![744018, 522814, 623800, -426251, -1151342], ![327270, 231026, 274246, -186890, -505221]]]
  hmulB := by decide  
  f := ![![![31, -19, 22, -11, -34]], ![![-12, 41, -68, 32, 76]], ![![-240, -68, -183, 128, 512]], ![![774, -104, 1216, -711, -2342]], ![![-174, -48, -137, 95, 377]]]
  g := ![![![35269, 48343, 267566, 2175, -356432], ![71868, 98509, 545224, 4432, -726308], ![146592, 200932, 1112121, 9040, -1481488], ![113922, 156150, 864286, 7025, -1151342], ![49992, 68524, 379259, 3083, -505221]]]
  hle1 := by decide   
  hle2 := by decide  


def P431P0 : CertificateIrreducibleZModOfList' 431 4 2 8 [98, 393, 209, 393, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [353, 175, 384, 11], [181, 393, 290, 328], [366, 293, 188, 92], [0, 1]]
 g := ![![[423, 67, 171, 29], [237, 104, 261, 69], [416, 26, 401, 119], [427, 121, 264, 128], [216, 8, 228], [296, 165, 315, 97], [373, 38, 1], []], ![[257, 345, 308, 364, 55, 361], [182, 132, 364, 52, 269, 24], [405, 9, 213, 129, 16, 36], [412, 368, 235, 192, 229, 163], [47, 417, 240], [25, 303, 417, 154, 79, 106], [317, 196, 354], [312, 43, 237, 83, 330, 38]], ![[326, 302, 121, 116, 43, 173], [223, 87, 57, 80, 167, 66], [4, 105, 109, 336, 160, 196], [277, 82, 40, 193, 161, 4], [58, 334, 11], [383, 322, 71, 191, 410, 164], [260, 12, 60], [85, 383, 86, 215, 172, 289]], ![[176, 12, 60, 111, 416, 358], [277, 313, 285, 309, 361, 176], [273, 372, 176, 213, 311, 22], [337, 7, 418, 273, 238, 196], [121, 404, 294], [312, 343, 427, 48, 262, 4], [298, 211, 75], [296, 112, 68, 85, 210, 302]]]
 h' := ![![[353, 175, 384, 11], [48, 404, 90, 93], [177, 127, 347, 345], [392, 64, 133, 375], [303, 386, 303, 220], [300, 346, 99, 39], [81, 106, 107, 236], [0, 0, 0, 1], [0, 1]], ![[181, 393, 290, 328], [112, 237, 339, 165], [53, 142, 147, 136], [334, 12, 300, 84], [215, 130, 268, 384], [293, 392, 191, 204], [413, 202, 10, 281], [4, 274, 95, 148], [353, 175, 384, 11]], ![[366, 293, 188, 92], [375, 342, 295, 283], [31, 152, 425, 222], [20, 247, 295, 118], [44, 57, 430, 291], [388, 351, 274, 154], [71, 159, 169, 94], [333, 37, 141, 102], [181, 393, 290, 328]], ![[0, 1], [297, 310, 138, 321], [315, 10, 374, 159], [227, 108, 134, 285], [74, 289, 292, 398], [115, 204, 298, 34], [254, 395, 145, 251], [222, 120, 195, 180], [366, 293, 188, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [385, 178, 289], []]
 b := ![[], [], [394, 367, 170, 166], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI431N0 : CertifiedPrimeIdeal' SI431N0 431 where
  n := 4
  hpos := by decide
  P := [98, 393, 209, 393, 1]
  hirr := P431P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-145539694, -46531992, -121614046, 103299460, 287066964]
  a := ![38, -1, 47, -37, -97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-28311722, -38738784, -215415878, -1758472, 287066964]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI431N0 : Ideal.IsPrime I431N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI431N0 B_one_repr
lemma NI431N0 : Nat.card (O ⧸ I431N0) = 34507149121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI431N0

def I431N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, -19, 22, -11, -34]] i)))

def SI431N1: IdealEqSpanCertificate' Table ![![31, -19, 22, -11, -34]] 
 ![![431, 0, 0, 0, 0], ![187, 1, 0, 0, 0], ![373, 0, 1, 0, 0], ![373, 0, 0, 1, 0], ![104, 0, 0, 0, 1]] where
  M :=![![![31, -19, 22, -11, -34], ![-12, 41, -68, 32, 76], ![-240, -68, -183, 128, 512], ![774, -104, 1216, -711, -2342], ![-402, 8, -566, 340, 1157]]]
  hmulB := by decide  
  f := ![![![230795, 162777, 193410, -131871, -356432]], ![![101227, 71394, 84830, -57839, -156332]], ![![201961, 142439, 169247, -115397, -311904]], ![![201463, 142085, 168830, -115114, -311138]], ![![56450, 39814, 47306, -32254, -87179]]]
  g := ![![![7, -19, 22, -11, -34], ![-5, 41, -68, 32, 76], ![-47, -68, -183, 128, 512], ![175, -104, 1216, -711, -2342], ![-88, 8, -566, 340, 1157]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI431N1 : Nat.card (O ⧸ I431N1) = 431 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI431N1)

lemma isPrimeI431N1 : Ideal.IsPrime I431N1 := prime_ideal_of_norm_prime hp431.out _ NI431N1
def MulI431N0 : IdealMulLeCertificate' Table 
  ![![230795, 162777, 193410, -131871, -356432]] ![![31, -19, 22, -11, -34]]
  ![![431, 0, 0, 0, 0]] where
 M := ![![![431, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC431 : ContainsPrimesAboveP 431 ![I431N0, I431N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI431N0
    exact isPrimeI431N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 431 (by decide) (𝕀 ⊙ MulI431N0)
instance hp433 : Fact (Nat.Prime 433) := {out := by norm_num}

def I433N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25655, -505, -6842, 3343, 11440]] i)))

def SI433N0: IdealEqSpanCertificate' Table ![![25655, -505, -6842, 3343, 11440]] 
 ![![433, 0, 0, 0, 0], ![0, 433, 0, 0, 0], ![0, 0, 433, 0, 0], ![377, 128, 107, 1, 0], ![187, 256, 369, 0, 1]] where
  M :=![![![25655, -505, -6842, 3343, 11440], ![16932, 23567, 32100, -21108, -58524], ![57600, 32724, 37043, -26016, -69168], ![44814, 26970, 32328, -22819, -60786], ![23994, 7614, 5778, -4566, -11161]]]
  hmulB := by decide  
  f := ![![![1037, 1177, -1258, 449, 242]], ![![-13260, -877, -15156, 9432, 33564]], ![![63216, -13716, 111707, -64128, -206304]], ![![12427, -2511, 21551, -12408, -40076]], ![![46613, -11757, 85991, -49045, -156371]]]
  g := ![![![-7792, -7753, -10591, 3343, 11440], ![43692, 40895, 55164, -21108, -58524], ![52656, 48660, 65459, -26016, -69168], ![46223, 42746, 57515, -22819, -60786], ![8851, 7966, 10653, -4566, -11161]]]
  hle1 := by decide   
  hle2 := by decide  


def P433P0 : CertificateIrreducibleZModOfList' 433 3 2 8 [11, 107, 135, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 47, 320], [201, 385, 113], [0, 1]]
 g := ![![[188, 26, 325], [259, 283], [132, 277], [107, 235], [31, 351, 144], [276, 156, 117], [243, 39], [1]], ![[306, 238, 191, 330], [343, 283], [88, 25], [23, 102], [87, 181, 136, 194], [288, 311, 290, 146], [14, 139], [242, 214, 431, 292]], ![[259, 374, 308, 232], [338, 266], [219, 374], [263, 208], [148, 336, 65, 287], [67, 78, 81, 110], [307, 148], [238, 382, 232, 141]]]
 h' := ![![[97, 47, 320], [290, 168, 217], [127, 330, 158], [359, 423, 267], [92, 208, 318], [428, 312, 421], [46, 172, 390], [422, 326, 298], [0, 1]], ![[201, 385, 113], [54, 294, 44], [128, 407, 158], [171, 303, 5], [104, 256, 202], [89, 97, 393], [56, 232, 381], [278, 287, 385], [97, 47, 320]], ![[0, 1], [58, 404, 172], [237, 129, 117], [204, 140, 161], [352, 402, 346], [150, 24, 52], [362, 29, 95], [99, 253, 183], [201, 385, 113]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [347, 192], []]
 b := ![[], [166, 164, 86], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI433N0 : CertifiedPrimeIdeal' SI433N0 433 where
  n := 3
  hpos := by decide
  P := [11, 107, 135, 1]
  hirr := P433P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2074437442, -658279253, -1864783480, 1649005286, 4135107640]
  a := ![-259, 5, -320, 250, 662]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3226361568, -2933760997, -3935711474, 1649005286, 4135107640]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI433N0 : Ideal.IsPrime I433N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI433N0 B_one_repr
lemma NI433N0 : Nat.card (O ⧸ I433N0) = 81182737 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI433N0

def I433N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1037, 1177, -1258, 449, 242]] i)))

def SI433N1: IdealEqSpanCertificate' Table ![![1037, 1177, -1258, 449, 242]] 
 ![![433, 0, 0, 0, 0], ![0, 433, 0, 0, 0], ![61, 219, 1, 0, 0], ![32, 82, 0, 1, 0], ![364, 152, 0, 0, 1]] where
  M :=![![![1037, 1177, -1258, 449, 242], ![-13260, -877, -15156, 9432, 33564], ![63216, -13716, 111707, -64128, -206304], ![-76890, 48876, -206832, 112463, 334194], ![57366, -25164, 129402, -71808, -220105]]]
  hmulB := by decide  
  f := ![![![25655, -505, -6842, 3343, 11440]], ![![16932, 23567, 32100, -21108, -58524]], ![![12311, 11924, 15357, -10265, -28148]], ![![5206, 4488, 5648, -3803, -10378]], ![![27566, 7866, 5530, -4610, -10953]]]
  g := ![![![-57, 469, -1258, 449, 242], ![-26808, -5905, -15156, 9432, 33564], ![162577, 28035, 111707, -64128, -206304], ![-260290, -33890, -206832, 112463, 334194], ![172240, 25358, 129402, -71808, -220105]]]
  hle1 := by decide   
  hle2 := by decide  


def P433P1 : CertificateIrreducibleZModOfList' 433 2 2 8 [240, 283, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [150, 432], [0, 1]]
 g := ![![[270, 132], [9], [381], [235], [62, 24], [243, 218], [153], [150, 1]], ![[152, 301], [9], [381], [235], [198, 409], [35, 215], [153], [300, 432]]]
 h' := ![![[150, 432], [197, 201], [408, 430], [173, 209], [275, 115], [135, 205], [342, 57], [372, 177], [0, 1]], ![[0, 1], [37, 232], [391, 3], [347, 224], [205, 318], [142, 228], [232, 376], [76, 256], [150, 432]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [126]]
 b := ![[], [38, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI433N1 : CertifiedPrimeIdeal' SI433N1 433 where
  n := 2
  hpos := by decide
  P := [240, 283, 1]
  hirr := P433P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-173734, -170375, -5176, 125495, 87670]
  a := ![385, 23, 476, -339, -984]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-82646, -52317, -5176, 125495, 87670]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI433N1 : Ideal.IsPrime I433N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI433N1 B_one_repr
lemma NI433N1 : Nat.card (O ⧸ I433N1) = 187489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI433N1
def MulI433N0 : IdealMulLeCertificate' Table 
  ![![25655, -505, -6842, 3343, 11440]] ![![1037, 1177, -1258, 449, 242]]
  ![![433, 0, 0, 0, 0]] where
 M := ![![![433, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC433 : ContainsPrimesAboveP 433 ![I433N0, I433N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI433N0
    exact isPrimeI433N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 433 (by decide) (𝕀 ⊙ MulI433N0)
instance hp439 : Fact (Nat.Prime 439) := {out := by norm_num}

def I439N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 90, 104, -70, -190]] i)))

def SI439N0: IdealEqSpanCertificate' Table ![![127, 90, 104, -70, -190]] 
 ![![439, 0, 0, 0, 0], ![0, 439, 0, 0, 0], ![382, 17, 1, 0, 0], ![265, 47, 0, 1, 0], ![90, 10, 0, 0, 1]] where
  M :=![![![127, 90, 104, -70, -190], ![240, 181, 200, -132, -360], ![432, 344, 361, -224, -624], ![168, 218, 120, -37, -140], ![204, 134, 176, -122, -327]]]
  hmulB := by decide  
  f := ![![![97, -66, -72, 46, 134]], ![![-48, 67, 8, -12, -56]], ![![82, -55, -63, 40, 116]], ![![55, -33, -40, 25, 70]], ![![18, -12, -16, 10, 29]]]
  g := ![![![-9, 8, 104, -70, -190], ![-20, 15, 200, -132, -360], ![-50, 25, 361, -224, -624], ![-53, 3, 120, -37, -140], ![-12, 14, 176, -122, -327]]]
  hle1 := by decide   
  hle2 := by decide  


def P439P0 : CertificateIrreducibleZModOfList' 439 2 2 8 [293, 379, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 438], [0, 1]]
 g := ![![[259, 361], [361, 319], [135, 36], [145], [60, 382], [37, 199], [320], [60, 1]], ![[408, 78], [185, 120], [100, 403], [145], [152, 57], [124, 240], [320], [120, 438]]]
 h' := ![![[60, 438], [26, 19], [394, 155], [59, 433], [419, 64], [134, 203], [147, 182], [419, 234], [0, 1]], ![[0, 1], [288, 420], [36, 284], [138, 6], [308, 375], [22, 236], [92, 257], [411, 205], [60, 438]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [102, 260]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI439N0 : CertifiedPrimeIdeal' SI439N0 439 where
  n := 2
  hpos := by decide
  P := [293, 379, 1]
  hirr := P439P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16475, 26894, -50056, 23566, 34270]
  a := ![-162, -18, -200, 126, 414]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![22343, -1304, -50056, 23566, 34270]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI439N0 : Ideal.IsPrime I439N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI439N0 B_one_repr
lemma NI439N0 : Nat.card (O ⧸ I439N0) = 192721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI439N0

def I439N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-377, -259, -306, 209, 564]] i)))

def SI439N1: IdealEqSpanCertificate' Table ![![-377, -259, -306, 209, 564]] 
 ![![439, 0, 0, 0, 0], ![118, 1, 0, 0, 0], ![124, 0, 1, 0, 0], ![88, 0, 0, 1, 0], ![282, 0, 0, 0, 1]] where
  M :=![![![-377, -259, -306, 209, 564], ![-756, -537, -640, 436, 1180], ![-1536, -1088, -1277, 872, 2352], ![-1206, -834, -1028, 697, 1890], ![-522, -374, -422, 290, 779]]]
  hmulB := by decide  
  f := ![![![-13541, -4335, -12014, 10661, 26778]], ![![-3782, -1211, -3356, 2978, 7480]], ![![-4484, -1436, -3981, 3532, 8872]], ![![-4166, -1336, -3700, 3283, 8246]], ![![-8604, -2754, -7634, 6774, 17015]]]
  g := ![![![-249, -259, -306, 209, 564], ![-522, -537, -640, 436, 1180], ![-1036, -1088, -1277, 872, 2352], ![-842, -834, -1028, 697, 1890], ![-340, -374, -422, 290, 779]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI439N1 : Nat.card (O ⧸ I439N1) = 439 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI439N1)

lemma isPrimeI439N1 : Ideal.IsPrime I439N1 := prime_ideal_of_norm_prime hp439.out _ NI439N1

def I439N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1331, 921, 1088, -743, -2006]] i)))

def SI439N2: IdealEqSpanCertificate' Table ![![1331, 921, 1088, -743, -2006]] 
 ![![439, 0, 0, 0, 0], ![311, 1, 0, 0, 0], ![298, 0, 1, 0, 0], ![259, 0, 0, 1, 0], ![117, 0, 0, 0, 1]] where
  M :=![![![1331, 921, 1088, -743, -2006], ![2676, 1899, 2260, -1540, -4164], ![5472, 3852, 4575, -3120, -8432], ![4230, 2978, 3540, -2415, -6526], ![1878, 1316, 1560, -1064, -2875]]]
  hmulB := by decide  
  f := ![![![-865, 77, -1304, 765, 2580]], ![![-605, 52, -908, 533, 1800]], ![![-598, 66, -929, 542, 1816]], ![![-535, 29, -764, 452, 1546]], ![![-225, 33, -368, 213, 705]]]
  g := ![![![-415, 921, 1088, -743, -2006], ![-855, 1899, 2260, -1540, -4164], ![-1734, 3852, 4575, -3120, -8432], ![-1339, 2978, 3540, -2415, -6526], ![-593, 1316, 1560, -1064, -2875]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI439N2 : Nat.card (O ⧸ I439N2) = 439 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI439N2)

lemma isPrimeI439N2 : Ideal.IsPrime I439N2 := prime_ideal_of_norm_prime hp439.out _ NI439N2

def I439N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 4, 1, -1, -2]] i)))

def SI439N3: IdealEqSpanCertificate' Table ![![1, 4, 1, -1, -2]] 
 ![![439, 0, 0, 0, 0], ![432, 1, 0, 0, 0], ![390, 0, 1, 0, 0], ![271, 0, 0, 1, 0], ![45, 0, 0, 0, 1]] where
  M :=![![![1, 4, 1, -1, -2], ![12, 2, 17, -10, -28], ![24, 21, 4, -6, -24], ![-42, 7, -55, 33, 122], ![30, 9, 27, -18, -65]]]
  hmulB := by decide  
  f := ![![![349, 212, 491, -401, -1036]], ![![348, 210, 487, -398, -1028]], ![![330, 195, 454, -372, -960]], ![![259, 145, 342, -282, -726]], ![![33, 21, 48, -39, -101]]]
  g := ![![![-4, 4, 1, -1, -2], ![-8, 2, 17, -10, -28], ![-18, 21, 4, -6, -24], ![9, 7, -55, 33, 122], ![-15, 9, 27, -18, -65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI439N3 : Nat.card (O ⧸ I439N3) = 439 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI439N3)

lemma isPrimeI439N3 : Ideal.IsPrime I439N3 := prime_ideal_of_norm_prime hp439.out _ NI439N3
def MulI439N0 : IdealMulLeCertificate' Table 
  ![![127, 90, 104, -70, -190]] ![![-377, -259, -306, 209, 564]]
  ![![-92063, -64935, -77130, 52581, 142126]] where
 M := ![![![-92063, -64935, -77130, 52581, 142126]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI439N1 : IdealMulLeCertificate' Table 
  ![![-92063, -64935, -77130, 52581, 142126]] ![![1331, 921, 1088, -743, -2006]]
  ![![-229027015, -161582314, -191934094, 130843130, 353672022]] where
 M := ![![![-229027015, -161582314, -191934094, 130843130, 353672022]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI439N2 : IdealMulLeCertificate' Table 
  ![![-229027015, -161582314, -191934094, 130843130, 353672022]] ![![1, 4, 1, -1, -2]]
  ![![439, 0, 0, 0, 0]] where
 M := ![![![-1659683839, -1170938554, -1390890285, 948181613, 2562957508]]]
 hmul := by decide  
 g := ![![![![-3780601, -2667286, -3168315, 2159867, 5838172]]]]
 hle2 := by decide  


def PBC439 : ContainsPrimesAboveP 439 ![I439N0, I439N1, I439N2, I439N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI439N0
    exact isPrimeI439N1
    exact isPrimeI439N2
    exact isPrimeI439N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 439 (by decide) (𝕀 ⊙ MulI439N0 ⊙ MulI439N1 ⊙ MulI439N2)
instance hp443 : Fact (Nat.Prime 443) := {out := by norm_num}

def I443N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![95, 80, -39, -7, -52]] i)))

def SI443N0: IdealEqSpanCertificate' Table ![![95, 80, -39, -7, -52]] 
 ![![443, 0, 0, 0, 0], ![0, 443, 0, 0, 0], ![0, 0, 443, 0, 0], ![157, 113, 21, 1, 0], ![403, 94, 32, 0, 1]] where
  M :=![![![95, 80, -39, -7, -52], ![-372, 18, -437, 218, 1020], ![4392, -225, 6528, -4098, -12584], ![-1554, 3257, -8361, 3771, 12326], ![2850, -1267, 6411, -3524, -10957]]]
  hmulB := by decide  
  f := ![![![-4505, -3384, -4089, 2773, 7522]], ![![-9564, -6618, -7817, 5338, 14412]], ![![-19224, -13645, -16236, 11062, 29912]], ![![-4981, -3558, -4241, 2888, 7812]], ![![-7531, -5479, -6564, 4463, 12085]]]
  g := ![![![50, 13, 4, -7, -52], ![-1006, -272, -85, 218, 1020], ![12910, 3715, 1118, -4098, -12584], ![-12553, -3570, -1088, 3771, 12326], ![11223, 3221, 973, -3524, -10957]]]
  hle1 := by decide   
  hle2 := by decide  


def P443P0 : CertificateIrreducibleZModOfList' 443 3 2 8 [110, 25, 373, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [190, 403, 343], [323, 39, 100], [0, 1]]
 g := ![![[401, 361, 349], [186, 47, 30], [390, 267], [137, 3, 361], [3, 3, 148], [186, 288, 67], [162, 27], [1]], ![[325, 57, 360, 228], [261, 399, 315, 366], [28, 311], [331, 218, 415, 430], [252, 279, 244, 73], [320, 355, 199, 63], [422, 308], [260, 164, 289, 294]], ![[170, 389, 33, 209], [139, 442, 106, 123], [207, 107], [184, 326, 42, 399], [64, 197, 424, 194], [94, 198, 366, 271], [395, 256], [346, 58, 278, 149]]]
 h' := ![![[190, 403, 343], [361, 431, 283], [135, 58, 284], [435, 154, 234], [113, 117, 424], [361, 188, 386], [39, 252, 320], [333, 418, 70], [0, 1]], ![[323, 39, 100], [442, 286, 276], [286, 40, 403], [321, 71, 371], [382, 397, 406], [322, 180, 241], [226, 54, 127], [226, 365, 357], [190, 403, 343]], ![[0, 1], [19, 169, 327], [170, 345, 199], [188, 218, 281], [54, 372, 56], [252, 75, 259], [386, 137, 439], [181, 103, 16], [323, 39, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [312, 442], []]
 b := ![[], [316, 93, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI443N0 : CertifiedPrimeIdeal' SI443N0 443 where
  n := 3
  hpos := by decide
  P := [110, 25, 373, 1]
  hirr := P443P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1437453659, -464359868, -1268973668, 1130222088, 2841461588]
  a := ![-163, 3, -201, 170, 418]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2988693773, -892272788, -261693924, 1130222088, 2841461588]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI443N0 : Ideal.IsPrime I443N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI443N0 B_one_repr
lemma NI443N0 : Nat.card (O ⧸ I443N0) = 86938307 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI443N0

def I443N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4505, 3384, 4089, -2773, -7522]] i)))

def SI443N1: IdealEqSpanCertificate' Table ![![4505, 3384, 4089, -2773, -7522]] 
 ![![443, 0, 0, 0, 0], ![0, 443, 0, 0, 0], ![195, 401, 1, 0, 0], ![108, 102, 0, 1, 0], ![212, 88, 0, 0, 1]] where
  M :=![![![4505, 3384, 4089, -2773, -7522], ![9564, 6618, 7817, -5338, -14412], ![19224, 13645, 16236, -11062, -29912], ![14862, 10527, 12513, -8527, -23054], ![6534, 4713, 5635, -3834, -10377]]]
  hmulB := by decide  
  f := ![![![-95, -80, 39, 7, 52]], ![![372, -18, 437, -218, -1020]], ![![285, -51, 398, -185, -872]], ![![66, -31, 129, -57, -250]], ![![22, -39, 91, -32, -153]]]
  g := ![![![2486, -1561, 4089, -2773, -7522], ![4779, -2969, 7817, -5338, -14412], ![9908, -6177, 16236, -11062, -29912], ![7637, -4760, 12513, -8527, -23054], ![3435, -2146, 5635, -3834, -10377]]]
  hle1 := by decide   
  hle2 := by decide  


def P443P1 : CertificateIrreducibleZModOfList' 443 2 2 8 [82, 214, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [229, 442], [0, 1]]
 g := ![![[424, 17], [112, 374], [409], [307, 81], [103, 386], [270, 79], [137], [229, 1]], ![[330, 426], [259, 69], [409], [250, 362], [340, 57], [198, 364], [137], [15, 442]]]
 h' := ![![[229, 442], [119, 367], [300, 107], [77, 267], [414, 9], [10, 392], [187, 361], [271, 85], [0, 1]], ![[0, 1], [435, 76], [438, 336], [86, 176], [260, 434], [292, 51], [15, 82], [244, 358], [229, 442]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [399]]
 b := ![[], [304, 421]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI443N1 : CertifiedPrimeIdeal' SI443N1 443 where
  n := 2
  hpos := by decide
  P := [82, 214, 1]
  hirr := P443P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3447, 2020, -11611, 6296, 17056]
  a := ![-47, -7, -58, 36, 120]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4594, 5677, -11611, 6296, 17056]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI443N1 : Ideal.IsPrime I443N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI443N1 B_one_repr
lemma NI443N1 : Nat.card (O ⧸ I443N1) = 196249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI443N1
def MulI443N0 : IdealMulLeCertificate' Table 
  ![![95, 80, -39, -7, -52]] ![![4505, 3384, 4089, -2773, -7522]]
  ![![443, 0, 0, 0, 0]] where
 M := ![![![-443, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC443 : ContainsPrimesAboveP 443 ![I443N0, I443N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI443N0
    exact isPrimeI443N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 443 (by decide) (𝕀 ⊙ MulI443N0)
instance hp449 : Fact (Nat.Prime 449) := {out := by norm_num}

def I449N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -18, -15, 11, 28]] i)))

def SI449N0: IdealEqSpanCertificate' Table ![![-23, -18, -15, 11, 28]] 
 ![![449, 0, 0, 0, 0], ![0, 449, 0, 0, 0], ![186, 145, 1, 0, 0], ![434, 357, 0, 1, 0], ![233, 33, 0, 0, 1]] where
  M :=![![![-23, -18, -15, 11, 28], ![-60, -32, -65, 42, 116], ![-120, -93, -66, 54, 152], ![-30, -55, -13, 17, -6], ![-66, -35, -45, 32, 109]]]
  hmulB := by decide  
  f := ![![![-157, 94, 181, -107, -318]], ![![36, -80, -179, 118, 332]], ![![-54, 13, 17, -6, -24]], ![![-124, 27, 32, -9, -42]], ![![-79, 43, 81, -47, -141]]]
  g := ![![![-19, -6, -15, 11, 28], ![-74, -21, -65, 42, 116], ![-104, -33, -66, 54, 152], ![-8, -9, -13, 17, -6], ![-69, -19, -45, 32, 109]]]
  hle1 := by decide   
  hle2 := by decide  


def P449P0 : CertificateIrreducibleZModOfList' 449 2 2 8 [390, 418, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 448], [0, 1]]
 g := ![![[206, 312], [229], [51], [144], [305], [141], [251, 67], [31, 1]], ![[0, 137], [229], [51], [144], [305], [141], [83, 382], [62, 448]]]
 h' := ![![[31, 448], [221, 326], [259, 45], [217, 282], [387, 12], [301, 355], [441, 251], [33, 122], [0, 1]], ![[0, 1], [0, 123], [307, 404], [428, 167], [310, 437], [81, 94], [140, 198], [223, 327], [31, 448]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [356, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI449N0 : CertifiedPrimeIdeal' SI449N0 449 where
  n := 2
  hpos := by decide
  P := [390, 418, 1]
  hirr := P449P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-205341, -61790, -182245, 166202, 411642]
  a := ![-165, -7, -203, 151, 422]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-299225, -103685, -182245, 166202, 411642]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI449N0 : Ideal.IsPrime I449N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI449N0 B_one_repr
lemma NI449N0 : Nat.card (O ⧸ I449N0) = 201601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI449N0

def I449N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![343, 130, 347, -301, -762]] i)))

def SI449N1: IdealEqSpanCertificate' Table ![![343, 130, 347, -301, -762]] 
 ![![449, 0, 0, 0, 0], ![0, 449, 0, 0, 0], ![416, 182, 1, 0, 0], ![309, 35, 0, 1, 0], ![74, 172, 0, 0, 1]] where
  M :=![![![343, 130, 347, -301, -762], ![1692, 530, 1483, -1318, -3308], ![7752, 2503, 6912, -6130, -15400], ![17094, 5497, 15235, -13509, -33926], ![-1122, -349, -983, 874, 2189]]]
  hmulB := by decide  
  f := ![![![3821, 2714, 3199, -2183, -5896]], ![![7836, 5490, 6613, -4498, -12164]], ![![6752, 4765, 5674, -3866, -10448]], ![![3267, 2315, 2739, -1868, -5046]], ![![3644, 2559, 3071, -2090, -5651]]]
  g := ![![![12, 175, 347, -301, -762], ![82, 770, 1483, -1318, -3308], ![370, 3581, 6912, -6130, -15400], ![811, 7886, 15235, -13509, -33926], ![-54, -509, -983, 874, 2189]]]
  hle1 := by decide   
  hle2 := by decide  


def P449P1 : CertificateIrreducibleZModOfList' 449 2 2 8 [414, 150, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [299, 448], [0, 1]]
 g := ![![[124, 372], [357], [175], [191], [205], [439], [248, 41], [299, 1]], ![[0, 77], [357], [175], [191], [205], [439], [384, 408], [149, 448]]]
 h' := ![![[299, 448], [33, 99], [124, 229], [284, 98], [41, 33], [299, 297], [149, 341], [138, 85], [0, 1]], ![[0, 1], [0, 350], [347, 220], [401, 351], [30, 416], [200, 152], [185, 108], [409, 364], [299, 448]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [345]]
 b := ![[], [141, 397]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI449N1 : CertifiedPrimeIdeal' SI449N1 449 where
  n := 2
  hpos := by decide
  P := [414, 150, 1]
  hirr := P449P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-180047, -83048, -124707, 141896, 298568]
  a := ![-241, -13, -298, 214, 616]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-31719, -75070, -124707, 141896, 298568]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI449N1 : Ideal.IsPrime I449N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI449N1 B_one_repr
lemma NI449N1 : Nat.card (O ⧸ I449N1) = 201601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI449N1

def I449N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 60, 74, -50, -136]] i)))

def SI449N2: IdealEqSpanCertificate' Table ![![79, 60, 74, -50, -136]] 
 ![![449, 0, 0, 0, 0], ![122, 1, 0, 0, 0], ![382, 0, 1, 0, 0], ![434, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![79, 60, 74, -50, -136], ![168, 117, 134, -92, -248], ![336, 238, 289, -196, -528], ![276, 186, 238, -161, -444], ![108, 82, 94, -64, -169]]]
  hmulB := by decide  
  f := ![![![-1993, -620, -1706, 1530, 3824]], ![![-562, -175, -482, 432, 1080]], ![![-1790, -558, -1535, 1376, 3440]], ![![-2134, -666, -1834, 1643, 4108]], ![![-71, -22, -60, 54, 135]]]
  g := ![![![-25, 60, 74, -50, -136], ![-46, 117, 134, -92, -248], ![-98, 238, 289, -196, -528], ![-78, 186, 238, -161, -444], ![-33, 82, 94, -64, -169]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI449N2 : Nat.card (O ⧸ I449N2) = 449 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI449N2)

lemma isPrimeI449N2 : Ideal.IsPrime I449N2 := prime_ideal_of_norm_prime hp449.out _ NI449N2
def MulI449N0 : IdealMulLeCertificate' Table 
  ![![-23, -18, -15, 11, 28]] ![![343, 130, 347, -301, -762]]
  ![![1993, 620, 1706, -1530, -3824]] where
 M := ![![![1993, 620, 1706, -1530, -3824]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI449N1 : IdealMulLeCertificate' Table 
  ![![1993, 620, 1706, -1530, -3824]] ![![79, 60, 74, -50, -136]]
  ![![449, 0, 0, 0, 0]] where
 M := ![![![-449, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC449 : ContainsPrimesAboveP 449 ![I449N0, I449N1, I449N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI449N0
    exact isPrimeI449N1
    exact isPrimeI449N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 449 (by decide) (𝕀 ⊙ MulI449N0 ⊙ MulI449N1)
instance hp457 : Fact (Nat.Prime 457) := {out := by norm_num}

def I457N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2735, -1911, -3592, 2177, 6380]] i)))

def SI457N0: IdealEqSpanCertificate' Table ![![2735, -1911, -3592, 2177, 6380]] 
 ![![457, 0, 0, 0, 0], ![0, 457, 0, 0, 0], ![0, 0, 457, 0, 0], ![0, 0, 0, 457, 0], ![432, 30, 98, 6, 1]] where
  M :=![![![2735, -1911, -3592, 2177, 6380], ![-1812, 1169, 2204, -1320, -3876], ![1008, -844, -1447, 928, 2592], ![-246, -436, -1668, 1101, 3154], ![1590, -994, -1480, 898, 2587]]]
  hmulB := by decide  
  f := ![![![-19, -13, -16, 11, 30]], ![![-36, -27, -28, 20, 52]], ![![-96, -52, -95, 64, 176]], ![![-78, -58, -44, 39, 102]], ![![-42, -26, -38, 26, 71]]]
  g := ![![![-6025, -423, -1376, -79, 6380], ![3660, 257, 836, 48, -3876], ![-2448, -172, -559, -32, 2592], ![-2982, -208, -680, -39, 3154], ![-2442, -172, -558, -32, 2587]]]
  hle1 := by decide   
  hle2 := by decide  


def P457P0 : CertificateIrreducibleZModOfList' 457 4 2 8 [154, 394, 28, 299, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 409, 183, 77], [255, 432, 169, 428], [307, 72, 105, 409], [0, 1]]
 g := ![![[151, 118, 99, 438], [352, 421, 12], [9, 169, 191], [104, 350, 161, 331], [149, 430, 286], [68, 107, 63], [300, 258, 158, 1], []], ![[236, 426, 361, 290, 201, 335], [384, 189, 288], [376, 266, 200], [58, 39, 245, 61, 50, 10], [319, 158, 58], [113, 241, 373], [63, 436, 79, 215, 172, 353], [85, 225, 95, 67, 58, 447]], ![[109, 245, 219, 219, 56, 150], [240, 264, 265], [131, 151, 100], [162, 112, 283, 368, 422, 361], [8, 95, 252], [185, 429, 108], [210, 140, 93, 327, 372, 9], [38, 344, 228, 455, 425, 289]], ![[59, 275, 47, 402, 358, 407], [56, 1, 237], [275, 386, 232], [124, 347, 57, 322, 115, 268], [184, 350, 382], [9, 181, 305], [143, 66, 47, 160, 415, 262], [104, 141, 166, 165, 360, 2]]]
 h' := ![![[53, 409, 183, 77], [222, 255, 216, 205], [426, 185, 419, 290], [436, 434, 170, 69], [305, 56, 84, 367], [60, 257, 110, 158], [414, 190, 431, 163], [0, 0, 0, 1], [0, 1]], ![[255, 432, 169, 428], [140, 124, 84, 322], [133, 177, 337, 46], [420, 5, 59, 114], [455, 16, 356, 290], [442, 361, 184, 132], [414, 19, 356, 234], [58, 359, 409, 325], [53, 409, 183, 77]], ![[307, 72, 105, 409], [370, 248, 336, 41], [394, 42, 20, 308], [312, 309, 63, 10], [143, 80, 177, 102], [2, 124, 349, 131], [212, 397, 215, 413], [133, 374, 375, 32], [255, 432, 169, 428]], ![[0, 1], [365, 287, 278, 346], [208, 53, 138, 270], [105, 166, 165, 264], [312, 305, 297, 155], [181, 172, 271, 36], [443, 308, 369, 104], [381, 181, 130, 99], [307, 72, 105, 409]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [131, 391, 32], []]
 b := ![[], [], [170, 34, 20, 269], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI457N0 : CertifiedPrimeIdeal' SI457N0 457 where
  n := 4
  hpos := by decide
  P := [154, 394, 28, 299, 1]
  hirr := P457P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-275997506478, -88564343936, -245931358024, 217963485204, 547758041508]
  a := ![-127, -3, -157, 121, 325]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-518397092862, -36151653368, -118000480144, -6714627492, 547758041508]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI457N0 : Ideal.IsPrime I457N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI457N0 B_one_repr
lemma NI457N0 : Nat.card (O ⧸ I457N0) = 43617904801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI457N0

def I457N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 13, 16, -11, -30]] i)))

def SI457N1: IdealEqSpanCertificate' Table ![![19, 13, 16, -11, -30]] 
 ![![457, 0, 0, 0, 0], ![394, 1, 0, 0, 0], ![144, 0, 1, 0, 0], ![226, 0, 0, 1, 0], ![423, 0, 0, 0, 1]] where
  M :=![![![19, 13, 16, -11, -30], ![36, 27, 28, -20, -52], ![96, 52, 95, -64, -176], ![78, 58, 44, -39, -102], ![30, 12, 40, -24, -67]]]
  hmulB := by decide  
  f := ![![![-2735, 1911, 3592, -2177, -6380]], ![![-2354, 1645, 3092, -1874, -5492]], ![![-864, 604, 1135, -688, -2016]], ![![-1352, 946, 1780, -1079, -3162]], ![![-2535, 1771, 3328, -2017, -5911]]]
  g := ![![![17, 13, 16, -11, -30], ![26, 27, 28, -20, -52], ![120, 52, 95, -64, -176], ![50, 58, 44, -39, -102], ![51, 12, 40, -24, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI457N1 : Nat.card (O ⧸ I457N1) = 457 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI457N1)

lemma isPrimeI457N1 : Ideal.IsPrime I457N1 := prime_ideal_of_norm_prime hp457.out _ NI457N1
def MulI457N0 : IdealMulLeCertificate' Table 
  ![![2735, -1911, -3592, 2177, 6380]] ![![19, 13, 16, -11, -30]]
  ![![457, 0, 0, 0, 0]] where
 M := ![![![-457, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC457 : ContainsPrimesAboveP 457 ![I457N0, I457N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI457N0
    exact isPrimeI457N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 457 (by decide) (𝕀 ⊙ MulI457N0)
instance hp461 : Fact (Nat.Prime 461) := {out := by norm_num}

def I461N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-83, 14, 14, 2, -8]] i)))

def SI461N0: IdealEqSpanCertificate' Table ![![-83, 14, 14, 2, -8]] 
 ![![461, 0, 0, 0, 0], ![0, 461, 0, 0, 0], ![172, 60, 1, 0, 0], ![372, 361, 0, 1, 0], ![1, 424, 0, 0, 1]] where
  M :=![![![-83, 14, 14, 2, -8], ![-168, -81, -204, 172, 440], ![-912, -276, -781, 696, 1744], ![-1980, -630, -1744, 1549, 3892], ![108, 56, 138, -116, -299]]]
  hmulB := by decide  
  f := ![![![-199, -110, -194, 126, 352]], ![![-312, -293, -148, 124, 328]], ![![-116, -80, -93, 64, 176]], ![![-408, -319, -276, 201, 548]], ![![-287, -270, -136, 114, 301]]]
  g := ![![![-7, 4, 14, 2, -8], ![-64, -513, -204, 172, 440], ![-276, -2048, -781, 696, 1744], ![-612, -4567, -1744, 1549, 3892], ![43, 348, 138, -116, -299]]]
  hle1 := by decide   
  hle2 := by decide  


def P461P0 : CertificateIrreducibleZModOfList' 461 2 2 8 [385, 291, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [170, 460], [0, 1]]
 g := ![![[257, 370], [336], [394, 95], [305, 405], [193], [234], [411, 340], [170, 1]], ![[0, 91], [336], [409, 366], [5, 56], [193], [234], [125, 121], [340, 460]]]
 h' := ![![[170, 460], [161, 56], [440, 283], [130, 216], [300, 74], [363, 374], [349, 427], [12, 394], [0, 1]], ![[0, 1], [0, 405], [145, 178], [431, 245], [433, 387], [325, 87], [101, 34], [147, 67], [170, 460]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [209]]
 b := ![[], [107, 335]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI461N0 : CertifiedPrimeIdeal' SI461N0 461 where
  n := 2
  hpos := by decide
  P := [385, 291, 1]
  hirr := P461P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3185, 6465, -15376, 6851, 12156]
  a := ![-85, -9, -108, 65, 218]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![189, -14530, -15376, 6851, 12156]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI461N0 : Ideal.IsPrime I461N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI461N0 B_one_repr
lemma NI461N0 : Nat.card (O ⧸ I461N0) = 212521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI461N0

def I461N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -14, 21, -9, -16]] i)))

def SI461N1: IdealEqSpanCertificate' Table ![![-7, -14, 21, -9, -16]] 
 ![![461, 0, 0, 0, 0], ![77, 1, 0, 0, 0], ![64, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![229, 0, 0, 0, 1]] where
  M :=![![![-7, -14, 21, -9, -16], ![132, 16, 135, -86, -316], ![-696, 123, -1170, 678, 2200], ![930, -519, 2339, -1279, -3854], ![-666, 257, -1425, 796, 2465]]]
  hmulB := by decide  
  f := ![![![56263, 39010, 46093, -31467, -84970]], ![![9643, 6690, 7906, -5397, -14574]], ![![8312, 5769, 6818, -4654, -12568]], ![![4413, 3065, 3622, -2472, -6676]], ![![28121, 19499, 23040, -15729, -42473]]]
  g := ![![![8, -14, 21, -9, -16], ![142, 16, 135, -86, -316], ![-1001, 123, -1170, 678, 2200], ![1770, -519, 2339, -1279, -3854], ![-1128, 257, -1425, 796, 2465]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI461N1 : Nat.card (O ⧸ I461N1) = 461 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI461N1)

lemma isPrimeI461N1 : Ideal.IsPrime I461N1 := prime_ideal_of_norm_prime hp461.out _ NI461N1

def I461N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, -19, 66, -35, -100]] i)))

def SI461N2: IdealEqSpanCertificate' Table ![![19, -19, 66, -35, -100]] 
 ![![461, 0, 0, 0, 0], ![111, 1, 0, 0, 0], ![126, 0, 1, 0, 0], ![97, 0, 0, 1, 0], ![429, 0, 0, 0, 1]] where
  M :=![![![19, -19, 66, -35, -100], ![60, 55, -44, 12, -20], ![-672, -28, -805, 496, 1744], ![1506, -390, 2800, -1595, -5078], ![-882, 142, -1450, 842, 2751]]]
  hmulB := by decide  
  f := ![![![-139, -2061, -3358, 2211, 6190]], ![![-45, -500, -814, 537, 1502]], ![![-66, -578, -945, 626, 1748]], ![![-77, -453, -750, 502, 1396]], ![![-129, -1921, -3128, 2059, 5765]]]
  g := ![![![87, -19, 66, -35, -100], ![15, 55, -44, 12, -20], ![-1502, -28, -805, 496, 1744], ![4393, -390, 2800, -1595, -5078], ![-2377, 142, -1450, 842, 2751]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI461N2 : Nat.card (O ⧸ I461N2) = 461 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI461N2)

lemma isPrimeI461N2 : Ideal.IsPrime I461N2 := prime_ideal_of_norm_prime hp461.out _ NI461N2

def I461N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 33, -36, 13, 8]] i)))

def SI461N3: IdealEqSpanCertificate' Table ![![29, 33, -36, 13, 8]] 
 ![![461, 0, 0, 0, 0], ![213, 1, 0, 0, 0], ![270, 0, 1, 0, 0], ![412, 0, 0, 1, 0], ![362, 0, 0, 0, 1]] where
  M :=![![![29, 33, -36, 13, 8], ![-372, -25, -424, 264, 940], ![1776, -384, 3135, -1800, -5792], ![-2166, 1372, -5816, 3163, 9402], ![1614, -706, 3636, -2018, -6187]]]
  hmulB := by decide  
  f := ![![![-2549, -3205, -3412, 2015, 5766]], ![![-1185, -1490, -1580, 931, 2666]], ![![-1470, -1886, -1977, 1154, 3316]], ![![-2170, -2842, -2952, 1709, 4926]], ![![-2024, -2530, -2700, 1598, 4569]]]
  g := ![![![-12, 33, -36, 13, 8], ![-715, -25, -424, 264, 940], ![4502, -384, 3135, -1800, -5792], ![-7442, 1372, -5816, 3163, 9402], ![4862, -706, 3636, -2018, -6187]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI461N3 : Nat.card (O ⧸ I461N3) = 461 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI461N3)

lemma isPrimeI461N3 : Ideal.IsPrime I461N3 := prime_ideal_of_norm_prime hp461.out _ NI461N3
def MulI461N0 : IdealMulLeCertificate' Table 
  ![![-83, 14, 14, 2, -8]] ![![-7, -14, 21, -9, -16]]
  ![![-127, 14, -155, 109, 276]] where
 M := ![![![-127, 14, -155, 109, 276]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI461N1 : IdealMulLeCertificate' Table 
  ![![-127, 14, -155, 109, 276]] ![![19, -19, 66, -35, -100]]
  ![![23309, 4205, 20777, -13730, -52126]] where
 M := ![![![23309, 4205, 20777, -13730, -52126]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI461N2 : IdealMulLeCertificate' Table 
  ![![23309, 4205, 20777, -13730, -52126]] ![![29, 33, -36, 13, 8]]
  ![![461, 0, 0, 0, 0]] where
 M := ![![![-18380531, 10649100, -47162605, 25776815, 77212890]]]
 hmul := by decide  
 g := ![![![![-39871, 23100, -102305, 55915, 167490]]]]
 hle2 := by decide  


def PBC461 : ContainsPrimesAboveP 461 ![I461N0, I461N1, I461N2, I461N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI461N0
    exact isPrimeI461N1
    exact isPrimeI461N2
    exact isPrimeI461N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 461 (by decide) (𝕀 ⊙ MulI461N0 ⊙ MulI461N1 ⊙ MulI461N2)
instance hp463 : Fact (Nat.Prime 463) := {out := by norm_num}

def I463N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1433, 1012, 1889, -1145, -3356]] i)))

def SI463N0: IdealEqSpanCertificate' Table ![![-1433, 1012, 1889, -1145, -3356]] 
 ![![463, 0, 0, 0, 0], ![0, 463, 0, 0, 0], ![0, 0, 463, 0, 0], ![11, 166, 363, 1, 0], ![221, 126, 327, 0, 1]] where
  M :=![![![-1433, 1012, 1889, -1145, -3356], ![948, -610, -1159, 698, 2052], ![-504, 445, 812, -502, -1448], ![-126, 237, 513, -329, -950], ![-738, 519, 931, -564, -1645]]]
  hmulB := by decide  
  f := ![![![19, 8, 19, -13, -38]], ![![12, 26, -15, 2, 20]], ![![168, 13, 256, -166, -456]], ![![137, 20, 196, -130, -352]], ![![131, 20, 186, -123, -335]]]
  g := ![![![1626, 1326, 3272, -1145, -3356], ![-994, -810, -1999, 698, 2052], ![702, 575, 1418, -502, -1448], ![461, 377, 930, -329, -950], ![797, 651, 1606, -564, -1645]]]
  hle1 := by decide   
  hle2 := by decide  


def P463P0 : CertificateIrreducibleZModOfList' 463 3 2 8 [109, 91, 334, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [336, 364, 189], [256, 98, 274], [0, 1]]
 g := ![![[307, 424, 42], [416, 282, 58], [412, 271, 306], [69, 201, 242], [183, 439], [90, 64], [297, 356, 436], [1]], ![[396, 93, 200, 172], [260, 371, 170, 425], [207, 180, 324, 109], [431, 254, 277, 276], [11, 220], [382, 206], [112, 197, 185, 156], [239, 307, 97, 266]], ![[437, 307, 13, 71], [422, 40, 236, 212], [71, 392, 142, 106], [248, 44, 99, 427], [57, 359], [345, 118], [48, 455, 63, 235], [427, 272, 156, 197]]]
 h' := ![![[336, 364, 189], [30, 402, 299], [3, 372, 65], [350, 97, 354], [299, 271, 381], [356, 262, 327], [37, 221, 455], [354, 372, 129], [0, 1]], ![[256, 98, 274], [447, 424, 179], [163, 18, 283], [262, 253, 243], [183, 227, 124], [302, 54, 76], [70, 376, 241], [269, 233, 73], [336, 364, 189]], ![[0, 1], [92, 100, 448], [447, 73, 115], [81, 113, 329], [193, 428, 421], [127, 147, 60], [90, 329, 230], [168, 321, 261], [256, 98, 274]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [169, 35], []]
 b := ![[], [94, 387, 137], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI463N0 : CertifiedPrimeIdeal' SI463N0 463 where
  n := 3
  hpos := by decide
  P := [109, 91, 334, 1]
  hirr := P463P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![29972835, 7077788, 30921302, -24676650, -65605400]
  a := ![92, 5, 113, -85, -235]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![31965895, 26716376, 65748404, -24676650, -65605400]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI463N0 : Ideal.IsPrime I463N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI463N0 B_one_repr
lemma NI463N0 : Nat.card (O ⧸ I463N0) = 99252847 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI463N0

def I463N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -1, -5, 2, 8]] i)))

def SI463N1: IdealEqSpanCertificate' Table ![![5, -1, -5, 2, 8]] 
 ![![463, 0, 0, 0, 0], ![79, 1, 0, 0, 0], ![241, 0, 1, 0, 0], ![164, 0, 0, 1, 0], ![178, 0, 0, 0, 1]] where
  M :=![![![5, -1, -5, 2, 8], ![24, 4, 37, -26, -72], ![72, 41, 22, -38, -88], ![144, 39, 153, -133, -304], ![0, 9, -31, 18, 37]]]
  hmulB := by decide  
  f := ![![![59027, 41611, 49409, -33686, -91048]], ![![10331, 7283, 8648, -5896, -15936]], ![![31253, 22032, 26161, -17836, -48208]], ![![21316, 15027, 17843, -12165, -32880]], ![![22874, 16125, 19147, -13054, -35283]]]
  g := ![![![-1, -1, -5, 2, 8], ![17, 4, 37, -26, -72], ![29, 41, 22, -38, -88], ![78, 39, 153, -133, -304], ![-6, 9, -31, 18, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI463N1 : Nat.card (O ⧸ I463N1) = 463 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI463N1)

lemma isPrimeI463N1 : Ideal.IsPrime I463N1 := prime_ideal_of_norm_prime hp463.out _ NI463N1

def I463N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2351, -1659, -1970, 1343, 3630]] i)))

def SI463N2: IdealEqSpanCertificate' Table ![![-2351, -1659, -1970, 1343, 3630]] 
 ![![463, 0, 0, 0, 0], ![121, 1, 0, 0, 0], ![175, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![368, 0, 0, 0, 1]] where
  M :=![![![-2351, -1659, -1970, 1343, 3630], ![-4788, -3377, -4014, 2736, 7396], ![-9744, -6878, -8161, 5564, 15040], ![-7518, -5308, -6302, 4295, 11606], ![-3342, -2358, -2798, 1908, 5159]]]
  hmulB := by decide  
  f := ![![![11749, -8071, -15018, 9083, 26652]], ![![3055, -2098, -3904, 2361, 6928]], ![![4453, -3057, -5687, 3439, 10092]], ![![37, -19, -32, 18, 54]], ![![9350, -6424, -11954, 7230, 21215]]]
  g := ![![![-1715, -1659, -1970, 1343, 3630], ![-3495, -3377, -4014, 2736, 7396], ![-7105, -6878, -8161, 5564, 15040], ![-5481, -5308, -6302, 4295, 11606], ![-2438, -2358, -2798, 1908, 5159]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI463N2 : Nat.card (O ⧸ I463N2) = 463 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI463N2)

lemma isPrimeI463N2 : Ideal.IsPrime I463N2 := prime_ideal_of_norm_prime hp463.out _ NI463N2
def MulI463N0 : IdealMulLeCertificate' Table 
  ![![-1433, 1012, 1889, -1145, -3356]] ![![5, -1, -5, 2, 8]]
  ![![-11749, 8071, 15018, -9083, -26652]] where
 M := ![![![-11749, 8071, 15018, -9083, -26652]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI463N1 : IdealMulLeCertificate' Table 
  ![![-11749, 8071, 15018, -9083, -26652]] ![![-2351, -1659, -1970, 1343, 3630]]
  ![![463, 0, 0, 0, 0]] where
 M := ![![![-463, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC463 : ContainsPrimesAboveP 463 ![I463N0, I463N1, I463N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI463N0
    exact isPrimeI463N1
    exact isPrimeI463N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 463 (by decide) (𝕀 ⊙ MulI463N0 ⊙ MulI463N1)


lemma PB696I9_primes (p : ℕ) :
  p ∈ Set.range ![421, 431, 433, 439, 443, 449, 457, 461, 463] ↔ Nat.Prime p ∧ 419 < p ∧ p ≤ 463 := by
  rw [← List.mem_ofFn']
  convert primes_range 419 463 (by omega)

def PB696I9 : PrimesBelowBoundCertificateInterval O 419 463 696 where
  m := 9
  g := ![2, 2, 2, 4, 2, 3, 2, 4, 3]
  P := ![421, 431, 433, 439, 443, 449, 457, 461, 463]
  hP := PB696I9_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I421N0, I421N1]
    · exact ![I431N0, I431N1]
    · exact ![I433N0, I433N1]
    · exact ![I439N0, I439N1, I439N2, I439N3]
    · exact ![I443N0, I443N1]
    · exact ![I449N0, I449N1, I449N2]
    · exact ![I457N0, I457N1]
    · exact ![I461N0, I461N1, I461N2, I461N3]
    · exact ![I463N0, I463N1, I463N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC421
    · exact PBC431
    · exact PBC433
    · exact PBC439
    · exact PBC443
    · exact PBC449
    · exact PBC457
    · exact PBC461
    · exact PBC463
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![74618461, 177241]
    · exact ![34507149121, 431]
    · exact ![81182737, 187489]
    · exact ![192721, 439, 439, 439]
    · exact ![86938307, 196249]
    · exact ![201601, 201601, 449]
    · exact ![43617904801, 457]
    · exact ![212521, 461, 461, 461]
    · exact ![99252847, 463, 463]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI421N0
      exact NI421N1
    · dsimp ; intro j
      fin_cases j
      exact NI431N0
      exact NI431N1
    · dsimp ; intro j
      fin_cases j
      exact NI433N0
      exact NI433N1
    · dsimp ; intro j
      fin_cases j
      exact NI439N0
      exact NI439N1
      exact NI439N2
      exact NI439N3
    · dsimp ; intro j
      fin_cases j
      exact NI443N0
      exact NI443N1
    · dsimp ; intro j
      fin_cases j
      exact NI449N0
      exact NI449N1
      exact NI449N2
    · dsimp ; intro j
      fin_cases j
      exact NI457N0
      exact NI457N1
    · dsimp ; intro j
      fin_cases j
      exact NI461N0
      exact NI461N1
      exact NI461N2
      exact NI461N3
    · dsimp ; intro j
      fin_cases j
      exact NI463N0
      exact NI463N1
      exact NI463N2
  β := ![I431N1, I439N1, I439N2, I439N3, I449N2, I457N1, I461N1, I461N2, I461N3, I463N1, I463N2]
  Il := ![[], [I431N1], [], [I439N1, I439N2, I439N3], [], [I449N2], [I457N1], [I461N1, I461N2, I461N3], [I463N1, I463N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
