
import IdealArithmetic.Examples.NF5_3_364500000_2.RI5_3_364500000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp647 : Fact (Nat.Prime 647) := {out := by norm_num}

def I647N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25057, 1139, -6284, -747, 1700]] i)))

def SI647N0: IdealEqSpanCertificate' Table ![![25057, 1139, -6284, -747, 1700]] 
 ![![647, 0, 0, 0, 0], ![0, 647, 0, 0, 0], ![0, 0, 647, 0, 0], ![480, 343, 30, 1, 0], ![564, 159, 368, 0, 1]] where
  M :=![![![25057, 1139, -6284, -747, 1700], ![-40800, -1421, 10572, 1032, -2988], ![35856, 2352, -8429, -1380, 2064], ![-4368, 1692, 2574, -689, -1266], ![45924, 4575, -9576, -2451, 1837]]]
  hmulB := by decide  
  f := ![![![335, 107, -146, -3, 26]], ![![-624, -103, 324, -84, -12]], ![![144, -168, -43, 276, -168]], ![![-72, 19, 60, -35, 6]], ![![216, -30, -70, 135, -77]]]
  g := ![![![-889, -20, -942, -747, 1700], ![1776, 185, 1668, 1032, -2988], ![-720, 228, -1123, -1380, 2064], ![1608, 679, 756, -689, -1266], ![288, 855, -946, -2451, 1837]]]
  hle1 := by decide   
  hle2 := by decide  


def P647P0 : CertificateIrreducibleZModOfList' 647 3 2 9 [306, 301, 384, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [339, 454, 117], [571, 192, 530], [0, 1]]
 g := ![![[500, 430, 116], [146, 256, 164], [576, 358, 64], [239, 337], [171, 288], [561, 436], [242, 291], [286, 263, 1], []], ![[610, 54, 153, 349], [211, 333, 117, 501], [332, 395, 602, 364], [117, 274], [49, 281], [460, 419], [560, 29], [388, 533, 283, 186], [427, 102]], ![[499, 196, 64, 132], [152, 3, 98, 491], [588, 539, 580, 524], [523, 403], [339, 385], [632, 385], [349, 98], [181, 529, 632, 59], [14, 102]]]
 h' := ![![[339, 454, 117], [614, 227, 595], [375, 58, 322], [451, 140, 639], [66, 97, 118], [192, 229, 215], [479, 282, 377], [476, 362, 278], [0, 0, 1], [0, 1]], ![[571, 192, 530], [4, 336, 400], [623, 587, 28], [443, 227, 610], [51, 421, 361], [325, 506, 138], [248, 283, 564], [574, 223, 621], [434, 557, 192], [339, 454, 117]], ![[0, 1], [240, 84, 299], [199, 2, 297], [520, 280, 45], [530, 129, 168], [125, 559, 294], [639, 82, 353], [187, 62, 395], [198, 90, 454], [571, 192, 530]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [495, 31], []]
 b := ![[], [225, 606, 326], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI647N0 : CertifiedPrimeIdeal' SI647N0 647 where
  n := 3
  hpos := by decide
  P := [306, 301, 384, 1]
  hirr := P647P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4639302, 2750878, 537098, -925608, -668466]
  a := ![0, -7, 2, -4, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1276578, 659228, 423958, -925608, -668466]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI647N0 : Ideal.IsPrime I647N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI647N0 B_one_repr
lemma NI647N0 : Nat.card (O ⧸ I647N0) = 270840023 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI647N0

def I647N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-335, -107, 146, 3, -26]] i)))

def SI647N1: IdealEqSpanCertificate' Table ![![-335, -107, 146, 3, -26]] 
 ![![647, 0, 0, 0, 0], ![0, 647, 0, 0, 0], ![453, 617, 1, 0, 0], ![3, 621, 0, 1, 0], ![616, 405, 0, 0, 1]] where
  M :=![![![-335, -107, 146, 3, -26], ![624, 103, -324, 84, 12], ![-144, 168, 43, -276, 168], ![-2328, -1302, 942, 673, -558], ![2964, 1557, -1362, -825, 751]]]
  hmulB := by decide  
  f := ![![![-25057, -1139, 6284, 747, -1700]], ![![40800, 1421, -10572, -1032, 2988]], ![![21309, 554, -5669, -459, 1656]], ![![39051, 1356, -10122, -986, 2862]], ![![1612, -202, -620, 69, 249]]]
  g := ![![![-78, -126, 146, 3, -26], ![216, 221, -324, 84, 12], ![-189, 119, 43, -276, 168], ![-135, -1197, 942, 673, -558], ![247, 1623, -1362, -825, 751]]]
  hle1 := by decide   
  hle2 := by decide  


def P647P1 : CertificateIrreducibleZModOfList' 647 2 2 9 [444, 358, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [289, 646], [0, 1]]
 g := ![![[505, 126], [156, 355], [370, 364], [192], [243], [100], [252], [167, 58], [1]], ![[40, 521], [525, 292], [105, 283], [192], [243], [100], [252], [107, 589], [1]]]
 h' := ![![[289, 646], [612, 171], [58, 238], [623, 162], [264, 329], [142, 451], [98, 10], [257, 314], [203, 289], [0, 1]], ![[0, 1], [212, 476], [258, 409], [210, 485], [236, 318], [434, 196], [400, 637], [423, 333], [261, 358], [289, 646]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [470]]
 b := ![[], [10, 235]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI647N1 : CertifiedPrimeIdeal' SI647N1 647 where
  n := 2
  hpos := by decide
  P := [444, 358, 1]
  hirr := P647P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![126267, 28478, -179187, -10342, 139779]
  a := ![3, -62, -1, -65, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7380, 93352, -179187, -10342, 139779]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI647N1 : Ideal.IsPrime I647N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI647N1 B_one_repr
lemma NI647N1 : Nat.card (O ⧸ I647N1) = 418609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI647N1
def MulI647N0 : IdealMulLeCertificate' Table 
  ![![25057, 1139, -6284, -747, 1700]] ![![-335, -107, 146, 3, -26]]
  ![![647, 0, 0, 0, 0]] where
 M := ![![![-647, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC647 : ContainsPrimesAboveP 647 ![I647N0, I647N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI647N0
    exact isPrimeI647N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 647 (by decide) (𝕀 ⊙ MulI647N0)
instance hp653 : Fact (Nat.Prime 653) := {out := by norm_num}

def I653N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1759, 1029, 300, -467, -370]] i)))

def SI653N0: IdealEqSpanCertificate' Table ![![1759, 1029, 300, -467, -370]] 
 ![![653, 0, 0, 0, 0], ![0, 653, 0, 0, 0], ![530, 124, 1, 0, 0], ![233, 235, 0, 1, 0], ![25, 80, 0, 0, 1]] where
  M :=![![![1759, 1029, 300, -467, -370], ![8880, 5195, 1512, -2360, -1868], ![22416, 13110, 3819, -5960, -4720], ![52200, 30520, 8874, -13881, -10986], ![72684, 42497, 12368, -19335, -15307]]]
  hmulB := by decide  
  f := ![![![1883, 111, -470, -81, 144]], ![![-3456, -333, 960, 212, -324]], ![![878, 28, -201, -26, 56]], ![![-577, -82, 180, 48, -66]], ![![-341, -34, 96, 22, -33]]]
  g := ![![![-60, 158, 300, -467, -370], ![-300, 799, 1512, -2360, -1868], ![-758, 2018, 3819, -5960, -4720], ![-1749, 4703, 8874, -13881, -10986], ![-2442, 6550, 12368, -19335, -15307]]]
  hle1 := by decide   
  hle2 := by decide  


def P653P0 : CertificateIrreducibleZModOfList' 653 2 2 9 [240, 100, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [553, 652], [0, 1]]
 g := ![![[599, 117], [587], [604, 463], [473, 566], [34], [649], [257], [74, 205], [1]], ![[0, 536], [587], [14, 190], [31, 87], [34], [649], [257], [470, 448], [1]]]
 h' := ![![[553, 652], [204, 211], [6, 175], [102, 486], [160, 462], [631, 120], [18, 355], [524, 347], [413, 553], [0, 1]], ![[0, 1], [0, 442], [137, 478], [477, 167], [323, 191], [385, 533], [433, 298], [433, 306], [618, 100], [553, 652]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [525]]
 b := ![[], [65, 589]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI653N0 : CertifiedPrimeIdeal' SI653N0 653 where
  n := 2
  hpos := by decide
  P := [240, 100, 1]
  hirr := P653P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8107, -5030, -731, 1984, 1462]
  a := ![1, -6, 1, -5, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-183, -762, -731, 1984, 1462]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI653N0 : Ideal.IsPrime I653N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI653N0 B_one_repr
lemma NI653N0 : Nat.card (O ⧸ I653N0) = 426409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI653N0

def I653N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![91, 63, -38, -42, 32]] i)))

def SI653N1: IdealEqSpanCertificate' Table ![![91, 63, -38, -42, 32]] 
 ![![653, 0, 0, 0, 0], ![197, 1, 0, 0, 0], ![512, 0, 1, 0, 0], ![77, 0, 0, 1, 0], ![120, 0, 0, 0, 1]] where
  M :=![![![91, 63, -38, -42, 32], ![-768, -383, 338, 180, -168], ![2016, 889, -899, -334, 360], ![-3936, -1564, 1774, 451, -584], ![4896, 1927, -2210, -538, 715]]]
  hmulB := by decide  
  f := ![![![335351, 14511, -84664, -9634, 23160]], ![![100319, 4342, -25326, -2882, 6928]], ![![263648, 11409, -66561, -7574, 18208]], ![![39383, 1705, -9942, -1131, 2720]], ![![62472, 2703, -15772, -1794, 4315]]]
  g := ![![![10, 63, -38, -42, 32], ![-141, -383, 338, 180, -168], ![413, 889, -899, -334, 360], ![-871, -1564, 1774, 451, -584], ![1091, 1927, -2210, -538, 715]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI653N1 : Nat.card (O ⧸ I653N1) = 653 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI653N1)

lemma isPrimeI653N1 : Ideal.IsPrime I653N1 := prime_ideal_of_norm_prime hp653.out _ NI653N1

def I653N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47, -1, 10, 1, -2]] i)))

def SI653N2: IdealEqSpanCertificate' Table ![![-47, -1, 10, 1, -2]] 
 ![![653, 0, 0, 0, 0], ![425, 1, 0, 0, 0], ![128, 0, 1, 0, 0], ![340, 0, 0, 1, 0], ![621, 0, 0, 0, 1]] where
  M :=![![![-47, -1, 10, 1, -2], ![48, -13, -12, 4, 4], ![-48, 0, -9, 4, 8], ![-120, -62, 18, 21, 6], ![-84, -25, -34, 21, 23]]]
  hmulB := by decide  
  f := ![![![-30043, -23527, -10852, 3687, 4292]], ![![-19711, -15436, -7120, 2419, 2816]], ![![-6160, -4824, -2225, 756, 880]], ![![-16028, -12552, -5790, 1967, 2290]], ![![-28959, -22678, -10460, 3554, 4137]]]
  g := ![![![0, -1, 10, 1, -2], ![5, -13, -12, 4, 4], ![-8, 0, -9, 4, 8], ![20, -62, 18, 21, 6], ![-10, -25, -34, 21, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI653N2 : Nat.card (O ⧸ I653N2) = 653 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI653N2)

lemma isPrimeI653N2 : Ideal.IsPrime I653N2 := prime_ideal_of_norm_prime hp653.out _ NI653N2

def I653N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, 2, -10, 0, 2]] i)))

def SI653N3: IdealEqSpanCertificate' Table ![![35, 2, -10, 0, 2]] 
 ![![653, 0, 0, 0, 0], ![436, 1, 0, 0, 0], ![290, 0, 1, 0, 0], ![556, 0, 0, 1, 0], ![52, 0, 0, 0, 1]] where
  M :=![![![35, 2, -10, 0, 2], ![-48, 3, 12, -4, 0], ![0, -22, 7, 12, -8], ![120, 58, -56, -23, 24], ![-120, -74, 62, 28, -27]]]
  hmulB := by decide  
  f := ![![![-1217, -946, -434, 184, 202]], ![![-820, -637, -292, 124, 136]], ![![-554, -430, -197, 84, 92]], ![![-1060, -822, -376, 161, 176]], ![![-124, -94, -42, 20, 21]]]
  g := ![![![3, 2, -10, 0, 2], ![-4, 3, 12, -4, 0], ![2, -22, 7, 12, -8], ![4, 58, -56, -23, 24], ![0, -74, 62, 28, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI653N3 : Nat.card (O ⧸ I653N3) = 653 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI653N3)

lemma isPrimeI653N3 : Ideal.IsPrime I653N3 := prime_ideal_of_norm_prime hp653.out _ NI653N3
def MulI653N0 : IdealMulLeCertificate' Table 
  ![![1759, 1029, 300, -467, -370]] ![![91, 63, -38, -42, 32]]
  ![![1189, 808, 502, -415, -406]] where
 M := ![![![1189, 808, 502, -415, -406]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI653N1 : IdealMulLeCertificate' Table 
  ![![1189, 808, 502, -415, -406]] ![![-47, -1, 10, 1, -2]]
  ![![42709, 24187, 4010, -10812, -6958]] where
 M := ![![![42709, 24187, 4010, -10812, -6958]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI653N2 : IdealMulLeCertificate' Table 
  ![![42709, 24187, 4010, -10812, -6958]] ![![35, 2, -10, 0, 2]]
  ![![653, 0, 0, 0, 0]] where
 M := ![![![-128641, -42445, 65300, 5224, -18284]]]
 hmul := by decide  
 g := ![![![![-197, -65, 100, 8, -28]]]]
 hle2 := by decide  


def PBC653 : ContainsPrimesAboveP 653 ![I653N0, I653N1, I653N2, I653N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI653N0
    exact isPrimeI653N1
    exact isPrimeI653N2
    exact isPrimeI653N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 653 (by decide) (𝕀 ⊙ MulI653N0 ⊙ MulI653N1 ⊙ MulI653N2)
instance hp659 : Fact (Nat.Prime 659) := {out := by norm_num}

def I659N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1055, 420, 44, -78, -34]] i)))

def SI659N0: IdealEqSpanCertificate' Table ![![1055, 420, 44, -78, -34]] 
 ![![659, 0, 0, 0, 0], ![0, 659, 0, 0, 0], ![0, 0, 659, 0, 0], ![130, 200, 263, 1, 0], ![39, 653, 442, 0, 1]] where
  M :=![![![1055, 420, 44, -78, -34], ![816, 1317, 860, -184, -312], ![3744, 2370, 877, -388, -368], ![4008, 3288, 1592, -503, -620], ![5184, 3380, 1284, -546, -531]]]
  hmulB := by decide  
  f := ![![![-35, -20, 12, 10, -6]], ![![144, 63, -84, -24, 40]], ![![-480, -214, 167, 76, -48]], ![![-154, -70, 43, 25, -8]], ![![-183, -83, 30, 28, 7]]]
  g := ![![![19, 58, 54, -78, -34], ![56, 367, 284, -184, -312], ![104, 486, 403, -388, -368], ![142, 772, 619, -503, -620], ![147, 697, 576, -546, -531]]]
  hle1 := by decide   
  hle2 := by decide  


def P659P0 : CertificateIrreducibleZModOfList' 659 3 2 9 [119, 217, 266, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [614, 462, 382], [438, 196, 277], [0, 1]]
 g := ![![[604, 0, 375], [6, 494, 522], [36, 563], [167, 221], [217, 440, 292], [122, 49], [213, 500], [26, 393, 1], []], ![[221, 39, 566, 429], [278, 123, 40, 20], [212, 613], [94, 19], [104, 186, 538, 203], [466, 637], [287, 554], [566, 367, 218, 300], [378, 285]], ![[356, 658, 341, 542], [172, 226, 628, 218], [371, 127], [613, 582], [192, 281, 354, 103], [189, 182], [49, 58], [407, 320, 388, 485], [483, 285]]]
 h' := ![![[614, 462, 382], [604, 281, 344], [20, 591, 400], [283, 75, 489], [537, 108, 337], [45, 386, 388], [556, 190, 652], [201, 311, 603], [0, 0, 1], [0, 1]], ![[438, 196, 277], [29, 368, 131], [410, 124, 363], [514, 487, 602], [34, 321, 550], [580, 550, 99], [109, 273, 36], [287, 481, 409], [537, 639, 196], [614, 462, 382]], ![[0, 1], [437, 10, 184], [628, 603, 555], [51, 97, 227], [205, 230, 431], [656, 382, 172], [566, 196, 630], [575, 526, 306], [590, 20, 462], [438, 196, 277]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [565, 51], []]
 b := ![[], [15, 216, 112], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI659N0 : CertifiedPrimeIdeal' SI659N0 659 where
  n := 3
  hpos := by decide
  P := [119, 217, 266, 1]
  hirr := P659P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-166703829, -93663896, -24253688, 46712738, 36068122]
  a := ![1, 25, -3, 18, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11602453, -50058718, -42870734, 46712738, 36068122]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI659N0 : Ideal.IsPrime I659N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI659N0 B_one_repr
lemma NI659N0 : Nat.card (O ⧸ I659N0) = 286191179 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI659N0

def I659N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5513, -231, 1398, 156, -384]] i)))

def SI659N1: IdealEqSpanCertificate' Table ![![-5513, -231, 1398, 156, -384]] 
 ![![659, 0, 0, 0, 0], ![212, 1, 0, 0, 0], ![593, 0, 1, 0, 0], ![300, 0, 0, 1, 0], ![436, 0, 0, 0, 1]] where
  M :=![![![-5513, -231, 1398, 156, -384], ![9216, 421, -2310, -276, 624], ![-7488, -255, 1945, 186, -552], ![2016, 240, -390, -125, 60], ![-8712, -159, 2370, 156, -713]]]
  hmulB := by decide  
  f := ![![![-20155, -15405, -6540, 2424, 2640]], ![![-6580, -5033, -2142, 792, 864]], ![![-18313, -13998, -5945, 2202, 2400]], ![![-9420, -7206, -3066, 1135, 1236]], ![![-13580, -10383, -4416, 1632, 1783]]]
  g := ![![![-1009, -231, 1398, 156, -384], ![1670, 421, -2310, -276, 624], ![-1399, -255, 1945, 186, -552], ![294, 240, -390, -125, 60], ![-1694, -159, 2370, 156, -713]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI659N1 : Nat.card (O ⧸ I659N1) = 659 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI659N1)

lemma isPrimeI659N1 : Ideal.IsPrime I659N1 := prime_ideal_of_norm_prime hp659.out _ NI659N1

def I659N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-101, -53, 36, 22, -18]] i)))

def SI659N2: IdealEqSpanCertificate' Table ![![-101, -53, 36, 22, -18]] 
 ![![659, 0, 0, 0, 0], ![580, 1, 0, 0, 0], ![504, 0, 1, 0, 0], ![507, 0, 0, 1, 0], ![255, 0, 0, 0, 1]] where
  M :=![![![-101, -53, 36, 22, -18], ![432, 177, -222, -72, 88], ![-1056, -451, 425, 130, -144], ![1512, 518, -758, -115, 216], ![-2040, -777, 856, 154, -231]]]
  hmulB := by decide  
  f := ![![![-2136007, -91419, 540110, 61290, -147766]], ![![-1874564, -80229, 474002, 53788, -129680]], ![![-1638072, -70107, 414203, 47002, -113320]], ![![-1642311, -70287, 415276, 47123, -113614]], ![![-831867, -35600, 210348, 23868, -57549]]]
  g := ![![![9, -53, 36, 22, -18], ![36, 177, -222, -72, 88], ![26, -451, 425, 130, -144], ![131, 518, -758, -115, 216], ![-3, -777, 856, 154, -231]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI659N2 : Nat.card (O ⧸ I659N2) = 659 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI659N2)

lemma isPrimeI659N2 : Ideal.IsPrime I659N2 := prime_ideal_of_norm_prime hp659.out _ NI659N2
def MulI659N0 : IdealMulLeCertificate' Table 
  ![![1055, 420, 44, -78, -34]] ![![-5513, -231, 1398, 156, -384]]
  ![![-2136007, -91419, 540110, 61290, -147766]] where
 M := ![![![-2136007, -91419, 540110, 61290, -147766]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI659N1 : IdealMulLeCertificate' Table 
  ![![-2136007, -91419, 540110, 61290, -147766]] ![![-101, -53, 36, 22, -18]]
  ![![659, 0, 0, 0, 0]] where
 M := ![![![659, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC659 : ContainsPrimesAboveP 659 ![I659N0, I659N1, I659N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI659N0
    exact isPrimeI659N1
    exact isPrimeI659N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 659 (by decide) (𝕀 ⊙ MulI659N0 ⊙ MulI659N1)
instance hp661 : Fact (Nat.Prime 661) := {out := by norm_num}

def I661N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![65489, 33659, -28690, -16504, 15002]] i)))

def SI661N0: IdealEqSpanCertificate' Table ![![65489, 33659, -28690, -16504, 15002]] 
 ![![661, 0, 0, 0, 0], ![0, 661, 0, 0, 0], ![0, 0, 661, 0, 0], ![383, 625, 624, 1, 0], ![145, 82, 619, 0, 1]] where
  M :=![![![65489, 33659, -28690, -16504, 15002], ![-360048, -161231, 160334, 62636, -66016], ![792192, 325867, -355899, -103730, 125272], ![-1323240, -493964, 599974, 113871, -174452], ![1622832, 599411, -736486, -132100, 209515]]]
  hmulB := by decide  
  f := ![![![133397, 5911, -33572, -3908, 9130]], ![![-219120, -8421, 56158, 5896, -15632]], ![![187584, 10391, -45581, -6370, 11792]], ![![47143, 5278, -9364, -2705, 1634]], ![![178097, 10009, -43163, -6106, 11125]]]
  g := ![![![6371, 13795, 1488, -16504, 15002], ![-22356, -51279, 2934, 62636, -66016], ![33822, 83033, -19927, -103730, 125272], ![-29713, -86775, 56778, 113871, -174452], ![33037, 99821, -72611, -132100, 209515]]]
  hle1 := by decide   
  hle2 := by decide  


def P661P0 : CertificateIrreducibleZModOfList' 661 3 2 9 [322, 627, 106, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 405, 4], [471, 255, 657], [0, 1]]
 g := ![![[632, 214, 122], [26, 80], [30, 175, 427], [338, 45], [647, 15, 437], [644, 14], [497, 274], [33, 555, 1], []], ![[619, 369, 255, 459], [378, 506], [166, 569, 242, 504], [530, 272], [393, 524, 142, 311], [353, 236], [345, 545], [169, 239, 533, 327], [222, 16]], ![[69, 360, 277, 554], [567, 56], [163, 591, 202, 658], [179, 73], [538, 136, 274, 383], [427, 38], [109, 272], [657, 413, 170, 273], [230, 16]]]
 h' := ![![[84, 405, 4], [468, 86, 38], [255, 163, 460], [509, 599, 108], [542, 632, 345], [572, 641, 114], [445, 432, 284], [611, 221, 508], [0, 0, 1], [0, 1]], ![[471, 255, 657], [501, 637, 119], [443, 238, 294], [51, 308, 191], [537, 230, 607], [454, 369, 567], [628, 437, 116], [658, 506, 207], [350, 370, 255], [84, 405, 4]], ![[0, 1], [475, 599, 504], [389, 260, 568], [233, 415, 362], [296, 460, 370], [533, 312, 641], [599, 453, 261], [598, 595, 607], [378, 291, 405], [471, 255, 657]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [617, 405], []]
 b := ![[], [570, 331, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI661N0 : CertifiedPrimeIdeal' SI661N0 661 where
  n := 3
  hpos := by decide
  P := [322, 627, 106, 1]
  hirr := P661P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18408076, 11579225, 2930684, -5921365, -3073990]
  a := ![-1, -7, 5, 5, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4133161, 5997730, 8473014, -5921365, -3073990]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI661N0 : Ideal.IsPrime I661N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI661N0 B_one_repr
lemma NI661N0 : Nat.card (O ⧸ I661N0) = 288804781 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI661N0

def I661N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![133397, 5911, -33572, -3908, 9130]] i)))

def SI661N1: IdealEqSpanCertificate' Table ![![133397, 5911, -33572, -3908, 9130]] 
 ![![661, 0, 0, 0, 0], ![0, 661, 0, 0, 0], ![152, 37, 1, 0, 0], ![325, 360, 0, 1, 0], ![478, 546, 0, 0, 1]] where
  M :=![![![133397, 5911, -33572, -3908, 9130], ![-219120, -8421, 56158, 5896, -15632], ![187584, 10391, -45581, -6370, 11792], ![-31944, 3986, 12266, -1361, -4924], ![232896, 17347, -53120, -9848, 12351]]]
  hmulB := by decide  
  f := ![![![65489, 33659, -28690, -16504, 15002]], ![![-360048, -161231, 160334, 62636, -66016]], ![![-3896, -792, 1839, -446, -56]], ![![-165895, -72009, 74124, 26171, -28842]], ![![-247594, -107933, 110578, 39604, -43365]]]
  g := ![![![3241, -3525, -33572, -3908, 9130], ![-4840, 6545, 56158, 5896, -15632], ![5370, -3704, -45581, -6370, 11792], ![1361, 4128, 12266, -1361, -4924], ![8478, -1839, -53120, -9848, 12351]]]
  hle1 := by decide   
  hle2 := by decide  


def P661P1 : CertificateIrreducibleZModOfList' 661 2 2 9 [548, 575, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 660], [0, 1]]
 g := ![![[147, 481], [632], [132, 399], [605], [432, 636], [620], [442], [441, 125], [1]], ![[531, 180], [632], [74, 262], [605], [265, 25], [620], [442], [615, 536], [1]]]
 h' := ![![[86, 660], [433, 231], [374, 434], [632, 407], [563, 604], [525, 530], [174, 194], [258, 42], [113, 86], [0, 1]], ![[0, 1], [469, 430], [21, 227], [601, 254], [288, 57], [496, 131], [333, 467], [565, 619], [238, 575], [86, 660]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [298, 362]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI661N1 : CertifiedPrimeIdeal' SI661N1 661 where
  n := 2
  hpos := by decide
  P := [548, 575, 1]
  hirr := P661P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![60212, 23452, -27354, -19030, 16146]
  a := ![0, -4, -2, -18, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4062, -1406, -27354, -19030, 16146]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI661N1 : Ideal.IsPrime I661N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI661N1 B_one_repr
lemma NI661N1 : Nat.card (O ⧸ I661N1) = 436921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI661N1
def MulI661N0 : IdealMulLeCertificate' Table 
  ![![65489, 33659, -28690, -16504, 15002]] ![![133397, 5911, -33572, -3908, 9130]]
  ![![661, 0, 0, 0, 0]] where
 M := ![![![661, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC661 : ContainsPrimesAboveP 661 ![I661N0, I661N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI661N0
    exact isPrimeI661N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 661 (by decide) (𝕀 ⊙ MulI661N0)
instance hp673 : Fact (Nat.Prime 673) := {out := by norm_num}

def I673N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-571225, -24453, 144436, 16393, -39514]] i)))

def SI673N0: IdealEqSpanCertificate' Table ![![-571225, -24453, 144436, 16393, -39514]] 
 ![![673, 0, 0, 0, 0], ![0, 673, 0, 0, 0], ![0, 0, 673, 0, 0], ![314, 594, 598, 1, 0], ![334, 631, 176, 0, 1]] where
  M :=![![![-571225, -24453, 144436, 16393, -39514], ![948336, 40651, -239748, -27240, 65572], ![-786864, -33592, 199035, 22540, -54480], ![179592, 7940, -45218, -5265, 12294], ![-941364, -39969, 238288, 26869, -65291]]]
  hmulB := by decide  
  f := ![![![-97, -43, -14, -17, 24]], ![![-576, -409, 44, 164, -68]], ![![816, 272, -709, -228, 328]], ![![166, -142, -596, -65, 242]], ![![-370, -332, -154, 85, 35]]]
  g := ![![![11113, 22543, -4018, 16393, -39514], ![-18424, -37377, 6700, -27240, 65572], ![15352, 31136, -5485, 22540, -54480], ![-3378, -6868, 1396, -5265, 12294], ![18468, 37442, -6446, 26869, -65291]]]
  hle1 := by decide   
  hle2 := by decide  


def P673P0 : CertificateIrreducibleZModOfList' 673 3 2 9 [54, 549, 620, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 460, 93], [633, 212, 580], [0, 1]]
 g := ![![[260, 402, 350], [259, 110], [384, 165], [174, 392], [628, 24], [393, 380, 203], [555, 601], [241, 53, 1], []], ![[658, 389, 613, 404], [120, 249], [35, 209], [412, 81], [150, 49], [117, 325, 310, 67], [127, 187], [172, 129, 220, 462], [173, 573]], ![[398, 638, 656, 315], [90, 669], [624, 84], [581, 495], [247, 159], [65, 303, 601, 403], [104, 556], [335, 618, 201, 393], [359, 573]]]
 h' := ![![[93, 460, 93], [636, 394, 404], [544, 366, 282], [418, 669, 288], [76, 15, 76], [314, 475, 90], [23, 153, 241], [446, 102, 447], [0, 0, 1], [0, 1]], ![[633, 212, 580], [259, 611, 477], [3, 648, 275], [343, 170, 114], [624, 420, 9], [290, 319, 666], [10, 65, 40], [319, 448, 608], [653, 21, 212], [93, 460, 93]], ![[0, 1], [432, 341, 465], [254, 332, 116], [413, 507, 271], [470, 238, 588], [485, 552, 590], [544, 455, 392], [211, 123, 291], [385, 652, 460], [633, 212, 580]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [599, 431], []]
 b := ![[], [166, 62, 596], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI673N0 : CertifiedPrimeIdeal' SI673N0 673 where
  n := 3
  hpos := by decide
  P := [54, 549, 620, 1]
  hirr := P673P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12342336, 5101087, -5876844, -1203832, 2341960]
  a := ![13, -7, 4, 2, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-582272, -1125705, 448484, -1203832, 2341960]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI673N0 : Ideal.IsPrime I673N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI673N0 B_one_repr
lemma NI673N0 : Nat.card (O ⧸ I673N0) = 304821217 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI673N0

def I673N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1109, -418, -592, 887, -430]] i)))

def SI673N1: IdealEqSpanCertificate' Table ![![1109, -418, -592, 887, -430]] 
 ![![673, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![95, 0, 1, 0, 0], ![387, 0, 0, 1, 0], ![106, 0, 0, 0, 1]] where
  M :=![![![1109, -418, -592, 887, -430], ![10320, 7021, -4330, -4624, 3548], ![-42576, -21143, 18741, 9862, -9248], ![105816, 45298, -47336, -15939, 17950], ![-134148, -56794, 60104, 19475, -22337]]]
  hmulB := by decide  
  f := ![![![-1040635, -155744, 176344, 78601, -14552]], ![![-52054, -8681, 8126, 4322, -268]], ![![-152501, -24335, 24663, 12181, -1352]], ![![-607089, -94846, 99764, 47602, -6430]], ![![-178594, -32008, 26144, 15803, 229]]]
  g := ![![![-336, -418, -592, 887, -430], ![2372, 7021, -4330, -4624, 3548], ![-5855, -21143, 18741, 9862, -9248], ![10889, 45298, -47336, -15939, 17950], ![-13495, -56794, 60104, 19475, -22337]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI673N1 : Nat.card (O ⧸ I673N1) = 673 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI673N1)

lemma isPrimeI673N1 : Ideal.IsPrime I673N1 := prime_ideal_of_norm_prime hp673.out _ NI673N1

def I673N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![221, 11, -54, -7, 14]] i)))

def SI673N2: IdealEqSpanCertificate' Table ![![221, 11, -54, -7, 14]] 
 ![![673, 0, 0, 0, 0], ![116, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![499, 0, 0, 1, 0], ![278, 0, 0, 0, 1]] where
  M :=![![![221, 11, -54, -7, 14], ![-336, -1, 92, 4, -28], ![336, 36, -61, -20, 8], ![72, 74, 26, -31, -26], ![492, 99, -50, -51, -13]]]
  hmulB := by decide  
  f := ![![![-23779, -18623, -8588, 2907, 3404]], ![![-4220, -3305, -1524, 516, 604]], ![![-278, -218, -101, 34, 40]], ![![-17929, -14041, -6474, 2192, 2566]], ![![-10118, -7925, -3656, 1237, 1449]]]
  g := ![![![-2, 11, -54, -7, 14], ![8, -1, 92, 4, -28], ![6, 36, -61, -20, 8], ![21, 74, 26, -31, -26], ![27, 99, -50, -51, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI673N2 : Nat.card (O ⧸ I673N2) = 673 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI673N2)

lemma isPrimeI673N2 : Ideal.IsPrime I673N2 := prime_ideal_of_norm_prime hp673.out _ NI673N2
def MulI673N0 : IdealMulLeCertificate' Table 
  ![![-571225, -24453, 144436, 16393, -39514]] ![![1109, -418, -592, 887, -430]]
  ![![15139, 5419, -6738, -1248, 1946]] where
 M := ![![![15139, 5419, -6738, -1248, 1946]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI673N1 : IdealMulLeCertificate' Table 
  ![![15139, 5419, -6738, -1248, 1946]] ![![221, 11, -54, -7, 14]]
  ![![673, 0, 0, 0, 0]] where
 M := ![![![128543, 18844, -37688, -10095, 13460]]]
 hmul := by decide  
 g := ![![![![191, 28, -56, -15, 20]]]]
 hle2 := by decide  


def PBC673 : ContainsPrimesAboveP 673 ![I673N0, I673N1, I673N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI673N0
    exact isPrimeI673N1
    exact isPrimeI673N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 673 (by decide) (𝕀 ⊙ MulI673N0 ⊙ MulI673N1)
instance hp677 : Fact (Nat.Prime 677) := {out := by norm_num}

def I677N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2723, -224, 592, 85, -160]] i)))

def SI677N0: IdealEqSpanCertificate' Table ![![-2723, -224, 592, 85, -160]] 
 ![![677, 0, 0, 0, 0], ![0, 677, 0, 0, 0], ![0, 0, 677, 0, 0], ![0, 0, 0, 677, 0], ![529, 543, 64, 613, 1]] where
  M :=![![![-2723, -224, 592, 85, -160], ![3840, -201, -1258, -96, 340], ![-4080, -675, 575, 102, -192], ![384, -494, -532, -145, 34], ![-4164, -440, 776, -99, -411]]]
  hmulB := by decide  
  f := ![![![17, 6, -8, -1, 2]], ![![-48, -15, 22, 0, -4]], ![![48, 9, -23, 6, 0]], ![![24, 26, -8, -23, 14]], ![![1, 17, 2, -21, 11]]]
  g := ![![![121, 128, 16, 145, -160], ![-260, -273, -34, -308, 340], ![144, 153, 19, 174, -192], ![-26, -28, -4, -31, 34], ![315, 329, 40, 372, -411]]]
  hle1 := by decide   
  hle2 := by decide  


def P677P0 : CertificateIrreducibleZModOfList' 677 4 2 9 [480, 112, 128, 516, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [183, 78, 597, 473], [438, 505, 580, 366], [217, 93, 177, 515], [0, 1]]
 g := ![![[647, 195, 265, 494], [663, 295, 56], [258, 626, 200, 149], [35, 315, 445], [221, 185, 354], [477, 370, 219, 341], [641, 267, 427], [161, 1], []], ![[257, 345, 492, 661, 158, 600], [596, 595, 235], [318, 9, 214, 248, 176, 347], [529, 81, 267], [237, 120, 126], [552, 548, 399, 670, 443, 191], [594, 74, 134], [479, 453, 279, 323, 456, 544], [177, 51, 319]], ![[294, 595, 365, 410, 476, 446], [306, 404, 302], [111, 430, 575, 475, 429, 672], [56, 151, 531], [2, 118, 103], [525, 49, 281, 101, 78, 669], [247, 373, 615], [333, 391, 164, 260, 649, 245], [190, 485, 587]], ![[645, 669, 70, 297, 509, 226], [268, 226, 253], [291, 251, 14, 428, 153, 143], [320, 211, 458], [415, 447, 556], [510, 283, 593, 489, 495, 279], [285, 555, 122], [378, 305, 451, 89, 153, 506], [597, 324, 518]]]
 h' := ![![[183, 78, 597, 473], [520, 452, 332, 265], [51, 541, 498, 291], [258, 421, 255, 560], [563, 556, 3, 72], [543, 423, 553, 543], [604, 582, 422, 232], [575, 444, 267, 67], [0, 0, 1], [0, 1]], ![[438, 505, 580, 366], [558, 20, 608, 131], [262, 135, 311, 554], [115, 388, 667, 504], [175, 266, 453, 262], [297, 76, 56, 98], [426, 458, 529, 455], [654, 303, 578, 218], [658, 492, 447, 647], [183, 78, 597, 473]], ![[217, 93, 177, 515], [119, 222, 82, 169], [639, 433, 490, 71], [583, 346, 188, 637], [315, 132, 510, 142], [329, 599, 581, 322], [391, 48, 648, 23], [511, 666, 232, 479], [448, 94, 567, 167], [438, 505, 580, 366]], ![[0, 1], [306, 660, 332, 112], [494, 245, 55, 438], [69, 199, 244, 330], [555, 400, 388, 201], [426, 256, 164, 391], [32, 266, 432, 644], [453, 618, 277, 590], [187, 91, 339, 540], [217, 93, 177, 515]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [374, 445, 537], []]
 b := ![[], [], [584, 346, 422, 559], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI677N0 : CertifiedPrimeIdeal' SI677N0 677 where
  n := 4
  hpos := by decide
  P := [480, 112, 128, 516, 1]
  hirr := P677P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![211563233, 50087914, -110155481, 14414818, 17126215]
  a := ![-1, -1, -1, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13069726, -13662403, -1781733, -15485901, 17126215]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI677N0 : Ideal.IsPrime I677N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI677N0 B_one_repr
lemma NI677N0 : Nat.card (O ⧸ I677N0) = 210065472241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI677N0

def I677N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 6, -8, -1, 2]] i)))

def SI677N1: IdealEqSpanCertificate' Table ![![17, 6, -8, -1, 2]] 
 ![![677, 0, 0, 0, 0], ![256, 1, 0, 0, 0], ![405, 0, 1, 0, 0], ![161, 0, 0, 1, 0], ![264, 0, 0, 0, 1]] where
  M :=![![![17, 6, -8, -1, 2], ![-48, -15, 22, 0, -4], ![48, 9, -23, 6, 0], ![24, 26, -8, -23, 14], ![-36, -34, 16, 27, -21]]]
  hmulB := by decide  
  f := ![![![-2723, -224, 592, 85, -160]], ![![-1024, -85, 222, 32, -60]], ![![-1635, -135, 355, 51, -96]], ![![-647, -54, 140, 20, -38]], ![![-1068, -88, 232, 33, -63]]]
  g := ![![![2, 6, -8, -1, 2], ![-6, -15, 22, 0, -4], ![9, 9, -23, 6, 0], ![-5, 26, -8, -23, 14], ![5, -34, 16, 27, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI677N1 : Nat.card (O ⧸ I677N1) = 677 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI677N1)

lemma isPrimeI677N1 : Ideal.IsPrime I677N1 := prime_ideal_of_norm_prime hp677.out _ NI677N1
def MulI677N0 : IdealMulLeCertificate' Table 
  ![![-2723, -224, 592, 85, -160]] ![![17, 6, -8, -1, 2]]
  ![![677, 0, 0, 0, 0]] where
 M := ![![![677, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC677 : ContainsPrimesAboveP 677 ![I677N0, I677N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI677N0
    exact isPrimeI677N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 677 (by decide) (𝕀 ⊙ MulI677N0)
instance hp683 : Fact (Nat.Prime 683) := {out := by norm_num}

def I683N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-134527, -5802, 33980, 3868, -9292]] i)))

def SI683N0: IdealEqSpanCertificate' Table ![![-134527, -5802, 33980, 3868, -9292]] 
 ![![683, 0, 0, 0, 0], ![0, 683, 0, 0, 0], ![261, 222, 1, 0, 0], ![113, 23, 0, 1, 0], ![544, 148, 0, 0, 1]] where
  M :=![![![-134527, -5802, 33980, 3868, -9292], ![223008, 9401, -56508, -6376, 15472], ![-185664, -8222, 46721, 5380, -12752], ![41520, 1344, -10852, -1099, 3024], ![-222480, -10010, 55860, 6500, -15211]]]
  hmulB := by decide  
  f := ![![![21355, 8926, -9580, -2964, 3476]], ![![-83424, -32389, 37684, 8648, -11856]], ![![-18747, -7042, 8493, 1664, -2500]], ![![481, 313, -204, -199, 156]], ![![-784, 174, 404, -484, 221]]]
  g := ![![![-6421, -9170, 33980, 3868, -9292], ![10652, 15243, -56508, -6376, 15472], ![-8859, -12616, 46721, 5380, -12752], ![1981, 2911, -10852, -1099, 3024], ![-10632, -15094, 55860, 6500, -15211]]]
  hle1 := by decide   
  hle2 := by decide  


def P683P0 : CertificateIrreducibleZModOfList' 683 2 2 9 [375, 162, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [521, 682], [0, 1]]
 g := ![![[66, 16], [301, 147], [443], [266, 137], [672], [654, 507], [509], [73, 290], [1]], ![[206, 667], [392, 536], [443], [611, 546], [672], [480, 176], [509], [220, 393], [1]]]
 h' := ![![[521, 682], [503, 4], [185, 259], [651, 358], [104, 305], [630, 291], [658, 202], [628, 242], [308, 521], [0, 1]], ![[0, 1], [538, 679], [573, 424], [27, 325], [553, 378], [615, 392], [35, 481], [355, 441], [598, 162], [521, 682]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [393, 359]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI683N0 : CertifiedPrimeIdeal' SI683N0 683 where
  n := 2
  hpos := by decide
  P := [375, 162, 1]
  hirr := P683P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![618, -508, -3506, 878, 3467]
  a := ![3, 3, 0, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1566, 358, -3506, 878, 3467]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI683N0 : Ideal.IsPrime I683N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI683N0 B_one_repr
lemma NI683N0 : Nat.card (O ⧸ I683N0) = 466489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI683N0

def I683N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2545, 121, -634, -78, 170]] i)))

def SI683N1: IdealEqSpanCertificate' Table ![![2545, 121, -634, -78, 170]] 
 ![![683, 0, 0, 0, 0], ![0, 683, 0, 0, 0], ![265, 138, 1, 0, 0], ![312, 213, 0, 1, 0], ![596, 135, 0, 0, 1]] where
  M :=![![![2545, 121, -634, -78, 170], ![-4080, -115, 1078, 92, -312], ![3744, 307, -831, -170, 184], ![-168, 332, 306, -141, -184], ![5016, 681, -902, -346, 107]]]
  hmulB := by decide  
  f := ![![![203, 159, -52, -98, 62]], ![![-1488, -727, 762, 392, -392]], ![![-215, -82, 131, 40, -54]], ![![-384, -159, 220, 79, -96]], ![![-100, 2, 98, -10, -21]]]
  g := ![![![137, 119, -634, -78, 170], ![-194, -185, 1078, 92, -312], ![245, 185, -831, -170, 184], ![106, 19, 306, -141, -184], ![422, 270, -902, -346, 107]]]
  hle1 := by decide   
  hle2 := by decide  


def P683P1 : CertificateIrreducibleZModOfList' 683 2 2 9 [614, 284, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [399, 682], [0, 1]]
 g := ![![[570, 584], [297, 391], [553], [351, 407], [16], [163, 158], [407], [572, 62], [1]], ![[0, 99], [582, 292], [553], [190, 276], [16], [369, 525], [407], [39, 621], [1]]]
 h' := ![![[399, 682], [3, 190], [153, 67], [314, 223], [415, 417], [319, 679], [223, 29], [537, 266], [69, 399], [0, 1]], ![[0, 1], [0, 493], [249, 616], [501, 460], [146, 266], [89, 4], [183, 654], [123, 417], [131, 284], [399, 682]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [489]]
 b := ![[], [569, 586]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI683N1 : CertifiedPrimeIdeal' SI683N1 683 where
  n := 2
  hpos := by decide
  P := [614, 284, 1]
  hirr := P683P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1247, -484, -8391, 1534, 7727]
  a := ![1, 5, -3, -2, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4186, -311, -8391, 1534, 7727]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI683N1 : Ideal.IsPrime I683N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI683N1 B_one_repr
lemma NI683N1 : Nat.card (O ⧸ I683N1) = 466489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI683N1

def I683N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12667, -2022, 2048, 1012, -112]] i)))

def SI683N2: IdealEqSpanCertificate' Table ![![-12667, -2022, 2048, 1012, -112]] 
 ![![683, 0, 0, 0, 0], ![646, 1, 0, 0, 0], ![340, 0, 1, 0, 0], ![503, 0, 0, 1, 0], ![231, 0, 0, 0, 1]] where
  M :=![![![-12667, -2022, 2048, 1012, -112], ![2688, -7363, -6516, 3200, 4048], ![-48576, -20978, -2467, 9676, 6400], ![-78144, -47364, -14596, 21533, 17328], ![-129600, -66878, -15096, 30596, 22709]]]
  hmulB := by decide  
  f := ![![![-73361, -31838, 33752, 12132, -13456]], ![![-68914, -29919, 31716, 11416, -12656]], ![![-37372, -16166, 17197, 6116, -6816]], ![![-52853, -23050, 24332, 8889, -9792]], ![![-26181, -11208, 12056, 4144, -4691]]]
  g := ![![![167, -2022, 2048, 1012, -112], ![6486, -7363, -6516, 3200, 4048], ![11708, -20978, -2467, 9676, 6400], ![30231, -47364, -14596, 21533, 17328], ![40367, -66878, -15096, 30596, 22709]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI683N2 : Nat.card (O ⧸ I683N2) = 683 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI683N2)

lemma isPrimeI683N2 : Ideal.IsPrime I683N2 := prime_ideal_of_norm_prime hp683.out _ NI683N2
def MulI683N0 : IdealMulLeCertificate' Table 
  ![![-134527, -5802, 33980, 3868, -9292]] ![![2545, 121, -634, -78, 170]]
  ![![-238736431, -10222353, 60363174, 6852366, -16513002]] where
 M := ![![![-238736431, -10222353, 60363174, 6852366, -16513002]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI683N1 : IdealMulLeCertificate' Table 
  ![![-238736431, -10222353, 60363174, 6852366, -16513002]] ![![-12667, -2022, 2048, 1012, -112]]
  ![![683, 0, 0, 0, 0]] where
 M := ![![![1669008916885, 71494668981, -421976164742, -47918538262, 115426744558]]]
 hmul := by decide  
 g := ![![![![2443644095, 104677407, -617827474, -70158914, 168999626]]]]
 hle2 := by decide  


def PBC683 : ContainsPrimesAboveP 683 ![I683N0, I683N1, I683N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI683N0
    exact isPrimeI683N1
    exact isPrimeI683N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 683 (by decide) (𝕀 ⊙ MulI683N0 ⊙ MulI683N1)
instance hp691 : Fact (Nat.Prime 691) := {out := by norm_num}

def I691N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3037, -1605, -382, 742, 558]] i)))

def SI691N0: IdealEqSpanCertificate' Table ![![-3037, -1605, -382, 742, 558]] 
 ![![691, 0, 0, 0, 0], ![0, 691, 0, 0, 0], ![0, 0, 691, 0, 0], ![140, 72, 326, 1, 0], ![674, 128, 450, 0, 1]] where
  M :=![![![-3037, -1605, -382, 742, 558], ![-13392, -8073, -2462, 3700, 2968], ![-35616, -20551, -5837, 9410, 7400], ![-82104, -47980, -13930, 21913, 17336], ![-115128, -66965, -19298, 30562, 24129]]]
  hmulB := by decide  
  f := ![![![-127, -99, 52, 74, -54]], ![![1296, 667, -562, -328, 296]], ![![-3552, -1589, 1587, 622, -656]], ![![-1556, -696, 696, 273, -288]], ![![-2210, -1013, 986, 418, -427]]]
  g := ![![![-699, -183, -714, 742, 558], ![-3664, -947, -3682, 3700, 2968], ![-9176, -2381, -9267, 9410, 7400], ![-21468, -5564, -21648, 21913, 17336], ![-29894, -7751, -30160, 30562, 24129]]]
  hle1 := by decide   
  hle2 := by decide  


def P691P0 : CertificateIrreducibleZModOfList' 691 3 2 9 [399, 394, 245, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 467, 107], [333, 223, 584], [0, 1]]
 g := ![![[211, 207, 361], [533, 505, 485], [393, 534], [315, 140], [536, 658, 37], [458, 662, 491], [633, 170], [205, 446, 1], []], ![[368, 499, 468, 267], [281, 289, 130, 548], [297, 49], [621, 359], [644, 541, 605, 277], [559, 7, 514, 15], [70, 389], [497, 553, 201, 303], [198, 393]], ![[284, 520, 116, 156], [575, 365, 107, 46], [232, 93], [20, 103], [411, 676, 601, 483], [667, 593, 35, 134], [225, 673], [607, 436, 528, 238], [412, 393]]]
 h' := ![![[113, 467, 107], [161, 31, 672], [360, 380, 57], [250, 228, 656], [346, 538, 404], [373, 354, 450], [52, 432, 128], [434, 401, 300], [0, 0, 1], [0, 1]], ![[333, 223, 584], [325, 415, 462], [110, 599, 164], [297, 89, 7], [484, 358, 475], [350, 118, 28], [553, 584, 140], [637, 663, 629], [103, 631, 223], [113, 467, 107]], ![[0, 1], [139, 245, 248], [387, 403, 470], [19, 374, 28], [33, 486, 503], [675, 219, 213], [118, 366, 423], [70, 318, 453], [399, 60, 467], [333, 223, 584]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [445, 670], []]
 b := ![[], [410, 140, 491], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI691N0 : CertifiedPrimeIdeal' SI691N0 691 where
  n := 3
  hpos := by decide
  P := [399, 394, 245, 1]
  hirr := P691P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![82963, 32532, -36088, -9377, 12158]
  a := ![4, 0, 0, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9839, -1228, -3546, -9377, 12158]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI691N0 : Ideal.IsPrime I691N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI691N0 B_one_repr
lemma NI691N0 : Nat.card (O ⧸ I691N0) = 329939371 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI691N0

def I691N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, 4, 6, -5, 2]] i)))

def SI691N1: IdealEqSpanCertificate' Table ![![-31, 4, 6, -5, 2]] 
 ![![691, 0, 0, 0, 0], ![263, 1, 0, 0, 0], ![311, 0, 1, 0, 0], ![432, 0, 0, 1, 0], ![642, 0, 0, 0, 1]] where
  M :=![![![-31, 4, 6, -5, 2], ![-48, -57, 26, 28, -20], ![240, 127, -125, -54, 56], ![-648, -276, 280, 85, -98], ![732, 312, -354, -97, 123]]]
  hmulB := by decide  
  f := ![![![-159541, -93238, -27098, 42439, 33584]], ![![-61889, -36169, -10512, 16463, 13028]], ![![-74753, -43687, -12697, 19885, 15736]], ![![-106608, -62304, -18108, 28359, 22442]], ![![-157794, -92218, -26802, 41975, 33217]]]
  g := ![![![-3, 4, 6, -5, 2], ![11, -57, 26, 28, -20], ![-10, 127, -125, -54, 56], ![16, -276, 280, 85, -98], ![-12, 312, -354, -97, 123]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI691N1 : Nat.card (O ⧸ I691N1) = 691 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI691N1)

lemma isPrimeI691N1 : Ideal.IsPrime I691N1 := prime_ideal_of_norm_prime hp691.out _ NI691N1

def I691N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, 4, -1, -2]] i)))

def SI691N2: IdealEqSpanCertificate' Table ![![-1, 1, 4, -1, -2]] 
 ![![691, 0, 0, 0, 0], ![467, 1, 0, 0, 0], ![479, 0, 1, 0, 0], ![553, 0, 0, 1, 0], ![570, 0, 0, 0, 1]] where
  M :=![![![-1, 1, 4, -1, -2], ![48, 23, -4, -8, -4], ![48, 36, 23, -20, -16], ![168, 92, 26, -37, -38], ![228, 141, 40, -69, -43]]]
  hmulB := by decide  
  f := ![![![-7147, -127, 1974, 183, -552]], ![![-4811, -84, 1330, 123, -372]], ![![-4967, -87, 1373, 127, -384]], ![![-5713, -99, 1580, 146, -442]], ![![-5910, -103, 1634, 151, -457]]]
  g := ![![![-1, 1, 4, -1, -2], ![-3, 23, -4, -8, -4], ![-11, 36, 23, -20, -16], ![-19, 92, 26, -37, -38], ![-32, 141, 40, -69, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI691N2 : Nat.card (O ⧸ I691N2) = 691 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI691N2)

lemma isPrimeI691N2 : Ideal.IsPrime I691N2 := prime_ideal_of_norm_prime hp691.out _ NI691N2
def MulI691N0 : IdealMulLeCertificate' Table 
  ![![-3037, -1605, -382, 742, 558]] ![![-31, 4, 6, -5, 2]]
  ![![7147, 127, -1974, -183, 552]] where
 M := ![![![7147, 127, -1974, -183, 552]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI691N1 : IdealMulLeCertificate' Table 
  ![![7147, 127, -1974, -183, 552]] ![![-1, 1, 4, -1, -2]]
  ![![691, 0, 0, 0, 0]] where
 M := ![![![-691, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC691 : ContainsPrimesAboveP 691 ![I691N0, I691N1, I691N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI691N0
    exact isPrimeI691N1
    exact isPrimeI691N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 691 (by decide) (𝕀 ⊙ MulI691N0 ⊙ MulI691N1)
instance hp701 : Fact (Nat.Prime 701) := {out := by norm_num}

def I701N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31135, 1324, -7880, -890, 2158]] i)))

def SI701N0: IdealEqSpanCertificate' Table ![![31135, 1324, -7880, -890, 2158]] 
 ![![701, 0, 0, 0, 0], ![0, 701, 0, 0, 0], ![0, 0, 701, 0, 0], ![36, 180, 577, 1, 0], ![129, 273, 463, 0, 1]] where
  M :=![![![31135, 1324, -7880, -890, 2158], ![-51792, -2263, 13060, 1504, -3560], ![42720, 1718, -10887, -1180, 3008], ![-10200, -676, 2384, 393, -580], ![50736, 1828, -13088, -1310, 3677]]]
  hmulB := by decide  
  f := ![![![83, 28, -56, -14, 22]], ![![-528, -243, 172, 64, -56]], ![![672, 194, -419, -52, 128]], ![![420, 98, -303, -27, 92]], ![![255, 39, -221, -12, 67]]]
  g := ![![![-307, -610, -704, -890, 2158], ![504, 997, 1132, 1504, -3560], ![-432, -866, -1031, -1180, 3008], ![72, 124, 63, 393, -580], ![-537, -1093, -1369, -1310, 3677]]]
  hle1 := by decide   
  hle2 := by decide  


def P701P0 : CertificateIrreducibleZModOfList' 701 3 2 9 [352, 558, 435, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [327, 667, 148], [640, 33, 553], [0, 1]]
 g := ![![[483, 205, 377], [65, 68], [47, 303, 595], [150, 581, 610], [9, 444, 422], [411, 207, 142], [162, 668], [98, 266, 1], []], ![[146, 610, 3, 481], [204, 69], [454, 5, 112, 342], [113, 63, 691, 284], [193, 160, 428, 108], [652, 221, 36, 463], [142, 133], [59, 597, 309, 643], [203, 173]], ![[262, 348, 539, 344], [642, 320], [114, 128, 507, 462], [427, 478, 550, 452], [34, 686, 378, 401], [568, 175, 268, 249], [451, 358], [448, 447, 462, 657], [499, 173]]]
 h' := ![![[327, 667, 148], [141, 272, 374], [280, 461, 150], [476, 607, 665], [337, 576, 285], [435, 665, 73], [336, 333, 172], [554, 296, 664], [0, 0, 1], [0, 1]], ![[640, 33, 553], [535, 409, 23], [672, 476, 274], [75, 21, 322], [103, 586, 18], [615, 438, 586], [424, 654, 282], [379, 206, 527], [423, 575, 33], [327, 667, 148]], ![[0, 1], [302, 20, 304], [238, 465, 277], [144, 73, 415], [255, 240, 398], [561, 299, 42], [593, 415, 247], [448, 199, 211], [519, 126, 667], [640, 33, 553]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 358], []]
 b := ![[], [690, 5, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI701N0 : CertifiedPrimeIdeal' SI701N0 701 where
  n := 3
  hpos := by decide
  P := [352, 558, 435, 1]
  hirr := P701P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![323149676, 189085746, 55923108, -86290074, -68702334]
  a := ![7, -21, -1, -23, -21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![17535226, 49182648, 116482848, -86290074, -68702334]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI701N0 : Ideal.IsPrime I701N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI701N0 B_one_repr
lemma NI701N0 : Nat.card (O ⧸ I701N0) = 344472101 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI701N0

def I701N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 28, -56, -14, 22]] i)))

def SI701N1: IdealEqSpanCertificate' Table ![![83, 28, -56, -14, 22]] 
 ![![701, 0, 0, 0, 0], ![0, 701, 0, 0, 0], ![235, 124, 1, 0, 0], ![302, 164, 0, 1, 0], ![125, 485, 0, 0, 1]] where
  M :=![![![83, 28, -56, -14, 22], ![-528, -243, 172, 64, -56], ![672, 194, -419, -52, 128], ![-1272, -508, 416, 61, -76], ![1056, 244, -656, -2, 153]]]
  hmulB := by decide  
  f := ![![![31135, 1324, -7880, -890, 2158]], ![![-51792, -2263, 13060, 1504, -3560]], ![![1337, 46, -347, -34, 98]], ![![1282, 40, -336, -31, 96]], ![![-30209, -1327, 7612, 880, -2073]]]
  g := ![![![21, -2, -56, -14, 22], ![-76, -7, 172, 64, -56], ![141, -2, -419, -52, 128], ![-154, -36, 416, 61, -76], ![195, 11, -656, -2, 153]]]
  hle1 := by decide   
  hle2 := by decide  


def P701P1 : CertificateIrreducibleZModOfList' 701 2 2 9 [450, 516, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [185, 700], [0, 1]]
 g := ![![[132, 498], [95], [148, 45], [185, 325], [477, 173], [489, 397], [69], [531, 577], [1]], ![[431, 203], [95], [61, 656], [24, 376], [236, 528], [329, 304], [69], [23, 124], [1]]]
 h' := ![![[185, 700], [36, 650], [696, 641], [169, 542], [557, 471], [64, 148], [364, 50], [91, 427], [251, 185], [0, 1]], ![[0, 1], [415, 51], [111, 60], [196, 159], [67, 230], [105, 553], [501, 651], [574, 274], [127, 516], [185, 700]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [513]]
 b := ![[], [283, 607]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI701N1 : CertifiedPrimeIdeal' SI701N1 701 where
  n := 2
  hpos := by decide
  P := [450, 516, 1]
  hirr := P701P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23033, -16598, -4071, 5076, 1094]
  a := ![1, -6, 1, -5, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1050, -1248, -4071, 5076, 1094]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI701N1 : Ideal.IsPrime I701N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI701N1 B_one_repr
lemma NI701N1 : Nat.card (O ⧸ I701N1) = 491401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI701N1
def MulI701N0 : IdealMulLeCertificate' Table 
  ![![31135, 1324, -7880, -890, 2158]] ![![83, 28, -56, -14, 22]]
  ![![701, 0, 0, 0, 0]] where
 M := ![![![701, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC701 : ContainsPrimesAboveP 701 ![I701N0, I701N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI701N0
    exact isPrimeI701N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 701 (by decide) (𝕀 ⊙ MulI701N0)


lemma PB934I13_primes (p : ℕ) :
  p ∈ Set.range ![647, 653, 659, 661, 673, 677, 683, 691, 701] ↔ Nat.Prime p ∧ 643 < p ∧ p ≤ 701 := by
  rw [← List.mem_ofFn']
  convert primes_range 643 701 (by omega)

def PB934I13 : PrimesBelowBoundCertificateInterval O 643 701 934 where
  m := 9
  g := ![2, 4, 3, 2, 3, 2, 3, 3, 2]
  P := ![647, 653, 659, 661, 673, 677, 683, 691, 701]
  hP := PB934I13_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I647N0, I647N1]
    · exact ![I653N0, I653N1, I653N2, I653N3]
    · exact ![I659N0, I659N1, I659N2]
    · exact ![I661N0, I661N1]
    · exact ![I673N0, I673N1, I673N2]
    · exact ![I677N0, I677N1]
    · exact ![I683N0, I683N1, I683N2]
    · exact ![I691N0, I691N1, I691N2]
    · exact ![I701N0, I701N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC647
    · exact PBC653
    · exact PBC659
    · exact PBC661
    · exact PBC673
    · exact PBC677
    · exact PBC683
    · exact PBC691
    · exact PBC701
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![270840023, 418609]
    · exact ![426409, 653, 653, 653]
    · exact ![286191179, 659, 659]
    · exact ![288804781, 436921]
    · exact ![304821217, 673, 673]
    · exact ![210065472241, 677]
    · exact ![466489, 466489, 683]
    · exact ![329939371, 691, 691]
    · exact ![344472101, 491401]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI647N0
      exact NI647N1
    · dsimp ; intro j
      fin_cases j
      exact NI653N0
      exact NI653N1
      exact NI653N2
      exact NI653N3
    · dsimp ; intro j
      fin_cases j
      exact NI659N0
      exact NI659N1
      exact NI659N2
    · dsimp ; intro j
      fin_cases j
      exact NI661N0
      exact NI661N1
    · dsimp ; intro j
      fin_cases j
      exact NI673N0
      exact NI673N1
      exact NI673N2
    · dsimp ; intro j
      fin_cases j
      exact NI677N0
      exact NI677N1
    · dsimp ; intro j
      fin_cases j
      exact NI683N0
      exact NI683N1
      exact NI683N2
    · dsimp ; intro j
      fin_cases j
      exact NI691N0
      exact NI691N1
      exact NI691N2
    · dsimp ; intro j
      fin_cases j
      exact NI701N0
      exact NI701N1
  β := ![I653N1, I653N2, I653N3, I659N1, I659N2, I673N1, I673N2, I677N1, I683N2, I691N1, I691N2]
  Il := ![[], [I653N1, I653N2, I653N3], [I659N1, I659N2], [], [I673N1, I673N2], [I677N1], [I683N2], [I691N1, I691N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
