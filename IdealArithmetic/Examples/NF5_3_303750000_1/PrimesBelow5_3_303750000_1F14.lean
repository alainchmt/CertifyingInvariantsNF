
import IdealArithmetic.Examples.NF5_3_303750000_1.RI5_3_303750000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp709 : Fact (Nat.Prime 709) := {out := by norm_num}

def I709N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-123, 167, -457, 311, -368]] i)))

def SI709N0: IdealEqSpanCertificate' Table ![![-123, 167, -457, 311, -368]] 
 ![![709, 0, 0, 0, 0], ![0, 709, 0, 0, 0], ![0, 0, 709, 0, 0], ![62, 24, 218, 1, 0], ![282, 488, 303, 0, 1]] where
  M :=![![![-123, 167, -457, 311, -368], ![220, -774, 2001, -1447, 1752], ![-228, 1014, -2555, 1868, -2272], ![1212, -4447, 11257, -8142, 9880], ![-312, 1175, -3011, 2173, -2631]]]
  hmulB := by decide  
  f := ![![![-11, 7, -7, 1, 16]], ![![48, 102, 55, 7, 40]], ![![68, 60, 95, 18, 16]], ![![22, 23, 31, 6, 8]], ![![58, 99, 76, 13, 41]]]
  g := ![![![119, 243, 61, 311, -368], ![-570, -1158, -301, -1447, 1752], ![740, 1502, 393, 1868, -2272], ![-3216, -6531, -1703, -8142, 9880], ![856, 1739, 452, 2173, -2631]]]
  hle1 := by decide   
  hle2 := by decide  


def P709P0 : CertificateIrreducibleZModOfList' 709 3 2 9 [191, 202, 566, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 427, 275], [91, 281, 434], [0, 1]]
 g := ![![[22, 362, 675], [357, 136], [242, 224, 390], [501, 473], [473, 414], [566, 127], [521, 640, 202], [395, 143, 1], []], ![[660, 697, 671, 629], [233, 105], [440, 260, 419, 521], [495, 130], [114, 248], [105, 46], [577, 115, 330, 104], [340, 134, 374, 441], [169, 471]], ![[85, 414, 665, 240], [550, 221], [213, 322, 410, 489], [532, 673], [232, 614], [159, 238], [693, 508, 55, 135], [24, 233, 516, 5], [10, 471]]]
 h' := ![![[52, 427, 275], [212, 239, 625], [572, 420, 179], [258, 458, 105], [114, 385, 329], [271, 196, 438], [458, 417, 313], [418, 665, 466], [0, 0, 1], [0, 1]], ![[91, 281, 434], [551, 332, 290], [611, 354, 602], [13, 654, 184], [423, 388, 513], [117, 151, 437], [601, 146, 563], [558, 351, 443], [203, 426, 281], [52, 427, 275]], ![[0, 1], [113, 138, 503], [134, 644, 637], [473, 306, 420], [663, 645, 576], [256, 362, 543], [534, 146, 542], [262, 402, 509], [699, 283, 427], [91, 281, 434]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [565, 517], []]
 b := ![[], [79, 372, 225], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI709N0 : CertifiedPrimeIdeal' SI709N0 709 where
  n := 3
  hpos := by decide
  P := [191, 202, 566, 1]
  hirr := P709P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-130058935, -151233621, -206081685, -3166466, -138048562]
  a := ![-20, -41, -39, 24, -100]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![55001349, 94911791, 59679721, -3166466, -138048562]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI709N0 : Ideal.IsPrime I709N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI709N0 B_one_repr
lemma NI709N0 : Nat.card (O ⧸ I709N0) = 356400829 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI709N0

def I709N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 22, -58, 40, -48]] i)))

def SI709N1: IdealEqSpanCertificate' Table ![![-7, 22, -58, 40, -48]] 
 ![![709, 0, 0, 0, 0], ![171, 1, 0, 0, 0], ![92, 0, 1, 0, 0], ![129, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-7, 22, -58, 40, -48], ![28, -95, 258, -186, 224], ![-32, 128, -325, 240, -292], ![148, -578, 1438, -1043, 1268], ![-44, 148, -392, 278, -335]]]
  hmulB := by decide  
  f := ![![![-18491, -1046, -4494, -804, 2824]], ![![-4457, -253, -1084, -194, 680]], ![![-2388, -136, -581, -104, 364]], ![![-3355, -196, -820, -147, 508]], ![![-27, -6, -10, -2, 1]]]
  g := ![![![-5, 22, -58, 40, -48], ![23, -95, 258, -186, 224], ![-32, 128, -325, 240, -292], ![141, -578, 1438, -1043, 1268], ![-35, 148, -392, 278, -335]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI709N1 : Nat.card (O ⧸ I709N1) = 709 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI709N1)

lemma isPrimeI709N1 : Ideal.IsPrime I709N1 := prime_ideal_of_norm_prime hp709.out _ NI709N1

def I709N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1017, 696, 1978, 157, -793]] i)))

def SI709N2: IdealEqSpanCertificate' Table ![![1017, 696, 1978, 157, -793]] 
 ![![709, 0, 0, 0, 0], ![320, 1, 0, 0, 0], ![199, 0, 1, 0, 0], ![649, 0, 0, 1, 0], ![216, 0, 0, 0, 1]] where
  M :=![![![1017, 696, 1978, 157, -793], ![120, -4552, 641, 871, -330], ![-2544, -320, -5073, -654, 2056], ![-260, 7711, -1199, -1492, 606], ![2614, 4597, 4837, -113, -1895]]]
  hmulB := by decide  
  f := ![![![-98517, 2278, -17850, -2771, 20577]], ![![-44408, 1080, -8005, -1239, 9314]], ![![-27551, 688, -4953, -765, 5791]], ![![-89869, 2409, -16027, -2465, 19011]], ![![-29830, 929, -5221, -793, 6403]]]
  g := ![![![-770, 696, 1978, 157, -793], ![1178, -4552, 641, 871, -330], ![1537, -320, -5073, -654, 2056], ![-1963, 7711, -1199, -1492, 606], ![-2748, 4597, 4837, -113, -1895]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI709N2 : Nat.card (O ⧸ I709N2) = 709 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI709N2)

lemma isPrimeI709N2 : Ideal.IsPrime I709N2 := prime_ideal_of_norm_prime hp709.out _ NI709N2
def MulI709N0 : IdealMulLeCertificate' Table 
  ![![-123, 167, -457, 311, -368]] ![![-7, 22, -58, 40, -48]]
  ![![82381, -311289, 790219, -572339, 694384]] where
 M := ![![![82381, -311289, 790219, -572339, 694384]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI709N1 : IdealMulLeCertificate' Table 
  ![![82381, -311289, 790219, -572339, 694384]] ![![1017, 696, 1978, 157, -793]]
  ![![709, 0, 0, 0, 0]] where
 M := ![![![37577, 231843, -397749, 462268, -607613]]]
 hmul := by decide  
 g := ![![![![53, 327, -561, 652, -857]]]]
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

def I719N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8923, -10428, -17080, -596, 6776]] i)))

def SI719N0: IdealEqSpanCertificate' Table ![![-8923, -10428, -17080, -596, 6776]] 
 ![![719, 0, 0, 0, 0], ![0, 719, 0, 0, 0], ![0, 0, 719, 0, 0], ![0, 0, 0, 719, 0], ![388, 442, 663, 255, 1]] where
  M :=![![![-8923, -10428, -17080, -596, 6776], ![-8496, 36597, -20240, -9112, 8784], ![24720, 14492, 48341, 4268, -19416], ![14912, -61732, 35384, 15545, -15320], ![-18592, -49732, -32896, 3940, 12605]]]
  hmulB := by decide  
  f := ![![![35, 20, 40, -4, 24]], ![![80, 147, 48, 72, 16]], ![![80, 76, 179, -36, 136]], ![![512, 908, 344, 423, 136]], ![![324, 494, 339, 159, 197]]]
  g := ![![![-3669, -4180, -6272, -2404, 6776], ![-4752, -5349, -8128, -3128, 8784], ![10512, 11956, 17971, 6892, -19416], ![8288, 9332, 14176, 5455, -15320], ![-6828, -7818, -11669, -4465, 12605]]]
  hle1 := by decide   
  hle2 := by decide  


def P719P0 : CertificateIrreducibleZModOfList' 719 4 2 9 [32, 344, 27, 429, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [298, 47, 96, 392], [203, 214, 697, 354], [508, 457, 645, 692], [0, 1]]
 g := ![![[485, 118, 455, 183], [541, 228, 242, 334], [651, 99, 329, 112], [665, 382, 241, 128], [407, 691, 323], [274, 70, 461], [14, 396, 145, 343], [290, 1], []], ![[262, 112, 624, 478, 159, 653], [538, 701, 307, 226, 483, 147], [716, 360, 716, 61, 593, 168], [215, 292, 522, 512, 57, 111], [33, 182, 105], [191, 317, 580], [709, 277, 464, 344, 631, 697], [421, 138, 510, 132, 425, 259], [678, 147, 517]], ![[282, 360, 359, 709, 538, 529], [125, 27, 148, 433, 152, 249], [39, 120, 174, 249, 135, 351], [222, 696, 662, 530, 342, 210], [711, 359, 125], [487, 149, 186], [16, 354, 685, 12, 414, 434], [501, 124, 286, 501, 420, 325], [290, 27, 210]], ![[34, 376, 139, 124, 583, 663], [33, 254, 39, 509, 395, 684], [405, 280, 280, 334, 196, 127], [712, 2, 657, 541, 300, 254], [579, 278, 177], [365, 76, 240], [642, 153, 235, 280, 44, 176], [44, 318, 266, 87, 675, 272], [242, 425, 10]]]
 h' := ![![[298, 47, 96, 392], [663, 372, 342, 168], [19, 69, 409, 571], [290, 393, 18, 485], [568, 425, 570, 435], [682, 592, 266, 205], [271, 662, 235, 450], [67, 149, 454, 669], [0, 0, 1], [0, 1]], ![[203, 214, 697, 354], [492, 328, 51, 130], [480, 104, 523, 350], [438, 101, 260, 603], [26, 284, 23, 578], [130, 399, 422, 172], [530, 348, 27, 526], [559, 454, 107, 708], [241, 24, 610, 57], [298, 47, 96, 392]], ![[508, 457, 645, 692], [405, 163, 38, 646], [574, 69, 25, 616], [437, 425, 12, 601], [589, 8, 302, 502], [236, 311, 73, 419], [324, 212, 117, 357], [11, 8, 269, 51], [293, 640, 84, 201], [203, 214, 697, 354]], ![[0, 1], [488, 575, 288, 494], [179, 477, 481, 620], [55, 519, 429, 468], [369, 2, 543, 642], [157, 136, 677, 642], [483, 216, 340, 105], [63, 108, 608, 10], [108, 55, 24, 461], [508, 457, 645, 692]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [100, 162, 204], []]
 b := ![[], [], [133, 473, 498, 560], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI719N0 : CertifiedPrimeIdeal' SI719N0 719 where
  n := 4
  hpos := by decide
  P := [32, 344, 27, 429, 1]
  hirr := P719P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![973856189015, 1184527222962, 1479694364409, 69045794456, 1013138617363]
  a := ![-37, -75, -76, 33, -127]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-545374029691, -621172102436, -932171361540, -359222950811, 1013138617363]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI719N0 : Ideal.IsPrime I719N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI719N0 B_one_repr
lemma NI719N0 : Nat.card (O ⧸ I719N0) = 267248675521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI719N0

def I719N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, -20, -40, 4, -24]] i)))

def SI719N1: IdealEqSpanCertificate' Table ![![-35, -20, -40, 4, -24]] 
 ![![719, 0, 0, 0, 0], ![115, 1, 0, 0, 0], ![620, 0, 1, 0, 0], ![616, 0, 0, 1, 0], ![383, 0, 0, 0, 1]] where
  M :=![![![-35, -20, -40, 4, -24], ![-80, -147, -48, -72, -16], ![-80, -76, -179, 36, -136], ![-512, -908, -344, -423, -136], ![-416, -524, -608, -52, -411]]]
  hmulB := by decide  
  f := ![![![8923, 10428, 17080, 596, -6776]], ![![1439, 1617, 2760, 108, -1096]], ![![7660, 8972, 14661, 508, -5816]], ![![7624, 9020, 14584, 489, -5784]], ![![4779, 5624, 9144, 312, -3627]]]
  g := ![![![47, -20, -40, 4, -24], ![135, -147, -48, -72, -16], ![208, -76, -179, 36, -136], ![876, -908, -344, -423, -136], ![871, -524, -608, -52, -411]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI719N1 : Nat.card (O ⧸ I719N1) = 719 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI719N1)

lemma isPrimeI719N1 : Ideal.IsPrime I719N1 := prime_ideal_of_norm_prime hp719.out _ NI719N1
def MulI719N0 : IdealMulLeCertificate' Table 
  ![![-8923, -10428, -17080, -596, 6776]] ![![-35, -20, -40, 4, -24]]
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

def I727N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 22, 60, 8, -28]] i)))

def SI727N0: IdealEqSpanCertificate' Table ![![37, 22, 60, 8, -28]] 
 ![![727, 0, 0, 0, 0], ![0, 727, 0, 0, 0], ![0, 0, 727, 0, 0], ![671, 248, 139, 1, 0], ![476, 122, 453, 0, 1]] where
  M :=![![![37, 22, 60, 8, -28], ![4, -145, 32, 16, 8], ![-80, 6, -173, -6, 48], ![20, 230, 80, -103, 104], ![92, 164, 146, 18, -71]]]
  hmulB := by decide  
  f := ![![![179, 10, 44, 8, -28]], ![![-20, 1, 0, 0, 8]], ![![-80, 2, -19, -2, 16]], ![![143, 10, 37, 7, -20]], ![![64, 8, 17, 4, -7]]]
  g := ![![![11, 2, 16, 8, -28], ![-20, -7, -8, 16, 8], ![-26, -6, -29, -6, 48], ![27, 18, -45, -103, 104], ![30, 6, 41, 18, -71]]]
  hle1 := by decide   
  hle2 := by decide  


def P727P0 : CertificateIrreducibleZModOfList' 727 3 2 9 [650, 645, 381, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [610, 37, 16], [463, 689, 711], [0, 1]]
 g := ![![[480, 451, 17], [91, 685, 579], [41, 702, 190], [358, 15], [516, 212, 202], [446, 425], [698, 339, 707], [570, 346, 1], []], ![[502, 219, 64, 587], [54, 319, 437, 63], [371, 310, 448, 34], [668, 456], [553, 384, 459, 195], [208, 700], [327, 88, 408, 488], [358, 7, 312, 567], [339, 256]], ![[318, 28, 483, 496], [21, 525, 377, 315], [713, 477, 626, 389], [352, 535], [223, 333, 512, 522], [600, 451], [45, 306, 54, 138], [685, 275, 356, 633], [371, 256]]]
 h' := ![![[610, 37, 16], [464, 72, 452], [249, 712, 427], [700, 582, 490], [474, 710, 527], [696, 553, 359], [675, 661, 648], [270, 682, 299], [0, 0, 1], [0, 1]], ![[463, 689, 711], [41, 175, 697], [290, 563, 255], [157, 709, 143], [351, 601, 58], [476, 478, 295], [380, 552, 492], [172, 531, 277], [534, 321, 689], [610, 37, 16]], ![[0, 1], [623, 480, 305], [70, 179, 45], [109, 163, 94], [264, 143, 142], [300, 423, 73], [53, 241, 314], [177, 241, 151], [118, 406, 37], [463, 689, 711]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [384, 612], []]
 b := ![[], [350, 256, 507], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI727N0 : CertifiedPrimeIdeal' SI727N0 727 where
  n := 3
  hpos := by decide
  P := [650, 645, 381, 1]
  hirr := P727P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-708787, -882719, -861306, -312403, -283362]
  a := ![-5, -11, -10, 6, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![472894, 152907, 235111, -312403, -283362]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI727N0 : Ideal.IsPrime I727N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI727N0 B_one_repr
lemma NI727N0 : Nat.card (O ⧸ I727N0) = 384240583 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI727N0

def I727N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 10, 44, 8, -28]] i)))

def SI727N1: IdealEqSpanCertificate' Table ![![179, 10, 44, 8, -28]] 
 ![![727, 0, 0, 0, 0], ![0, 727, 0, 0, 0], ![615, 329, 1, 0, 0], ![357, 146, 0, 1, 0], ![361, 91, 0, 0, 1]] where
  M :=![![![179, 10, 44, 8, -28], ![-20, 1, 0, 0, 8], ![-80, 2, -19, -2, 16], ![-68, 34, 16, -1, 40], ![4, 28, 22, 6, 15]]]
  hmulB := by decide  
  f := ![![![37, 22, 60, 8, -28]], ![![4, -145, 32, 16, 8]], ![![33, -47, 65, 14, -20]], ![![19, -18, 36, 7, -12]], ![![19, -7, 34, 6, -13]]]
  g := ![![![-27, -18, 44, 8, -28], ![-4, -1, 0, 0, 8], ![9, 7, -19, -2, 16], ![-33, -12, 16, -1, 40], ![-29, -13, 22, 6, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P727P1 : CertificateIrreducibleZModOfList' 727 2 2 9 [416, 262, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [465, 726], [0, 1]]
 g := ![![[95, 547], [571, 66], [266, 211], [648], [405, 23], [207], [481, 577], [409, 306], [1]], ![[0, 180], [0, 661], [236, 516], [648], [195, 704], [207], [523, 150], [207, 421], [1]]]
 h' := ![![[465, 726], [193, 170], [575, 288], [563, 336], [184, 241], [562, 626], [556, 303], [701, 397], [311, 465], [0, 1]], ![[0, 1], [0, 557], [0, 439], [498, 391], [291, 486], [125, 101], [413, 424], [648, 330], [617, 262], [465, 726]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [212]]
 b := ![[], [73, 106]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI727N1 : CertifiedPrimeIdeal' SI727N1 727 where
  n := 2
  hpos := by decide
  P := [416, 262, 1]
  hirr := P727P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![436530, 495745, 785530, -102411, 659734]
  a := ![46, 95, 92, -54, 215]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-941221, -416819, 785530, -102411, 659734]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI727N1 : Ideal.IsPrime I727N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI727N1 B_one_repr
lemma NI727N1 : Nat.card (O ⧸ I727N1) = 528529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI727N1
def MulI727N0 : IdealMulLeCertificate' Table 
  ![![37, 22, 60, 8, -28]] ![![179, 10, 44, 8, -28]]
  ![![727, 0, 0, 0, 0]] where
 M := ![![![727, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC727 : ContainsPrimesAboveP 727 ![I727N0, I727N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI727N0
    exact isPrimeI727N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 727 (by decide) (𝕀 ⊙ MulI727N0)
instance hp733 : Fact (Nat.Prime 733) := {out := by norm_num}

def I733N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![683, 1167, 1047, 248, 709]] i)))

def SI733N0: IdealEqSpanCertificate' Table ![![683, 1167, 1047, 248, 709]] 
 ![![733, 0, 0, 0, 0], ![0, 733, 0, 0, 0], ![0, 0, 733, 0, 0], ![231, 294, 365, 1, 0], ![129, 149, 399, 0, 1]] where
  M :=![![![683, 1167, 1047, 248, 709], ![4248, 5801, 5322, 1260, 3402], ![3828, 5196, 4727, 1112, 3016], ![26724, 36726, 33570, 7891, 21346], ![19494, 26820, 24552, 5774, 15603]]]
  hmulB := by decide  
  f := ![![![53, -207, 537, -386, 467]], ![![-252, 953, -2442, 1776, -2154]], ![![324, -1248, 3143, -2288, 2780]], ![![75, -297, 736, -535, 651]], ![![135, -524, 1314, -956, 1162]]]
  g := ![![![-202, -242, -508, 248, 709], ![-990, -1189, -2472, 1260, 3402], ![-876, -1052, -2189, 1112, 3016], ![-6207, -7454, -15503, 7891, 21346], ![-4539, -5451, -11335, 5774, 15603]]]
  hle1 := by decide   
  hle2 := by decide  


def P733P0 : CertificateIrreducibleZModOfList' 733 3 2 9 [49, 341, 723, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 439, 658], [627, 293, 75], [0, 1]]
 g := ![![[596, 250, 697], [179, 589], [489, 210, 441], [194, 617, 41], [176, 54, 552], [712, 574], [513, 635, 25], [492, 10, 1], []], ![[208, 63, 26, 190], [412, 218], [17, 214, 363, 206], [616, 95, 714, 441], [82, 455, 305, 536], [283, 489], [700, 194, 275, 100], [592, 155, 199, 730], [662, 494]], ![[309, 697, 639, 312], [397, 238], [631, 562, 314, 258], [616, 180, 439, 300], [434, 194, 23, 680], [70, 585], [107, 323, 726, 682], [709, 557, 663, 48], [512, 494]]]
 h' := ![![[116, 439, 658], [699, 230, 81], [228, 143, 162], [23, 633, 21], [172, 60, 130], [342, 377, 368], [518, 622, 300], [81, 328, 728], [0, 0, 1], [0, 1]], ![[627, 293, 75], [550, 727, 619], [541, 95, 91], [281, 99, 459], [153, 663, 605], [208, 527, 385], [180, 444, 202], [366, 494, 323], [76, 699, 293], [116, 439, 658]], ![[0, 1], [719, 509, 33], [152, 495, 480], [470, 1, 253], [630, 10, 731], [441, 562, 713], [333, 400, 231], [122, 644, 415], [75, 34, 439], [627, 293, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [226, 36], []]
 b := ![[], [290, 614, 323], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI733N0 : CertifiedPrimeIdeal' SI733N0 733 where
  n := 3
  hpos := by decide
  P := [49, 341, 723, 1]
  hirr := P733P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-390084464, -433650757, -650730518, 19271414, -445837836]
  a := ![-27, -60, -55, 38, -147]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![71857162, 82306127, 232202592, 19271414, -445837836]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI733N0 : Ideal.IsPrime I733N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI733N0 B_one_repr
lemma NI733N0 : Nat.card (O ⧸ I733N0) = 393832837 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI733N0

def I733N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-53, 207, -537, 386, -467]] i)))

def SI733N1: IdealEqSpanCertificate' Table ![![-53, 207, -537, 386, -467]] 
 ![![733, 0, 0, 0, 0], ![0, 733, 0, 0, 0], ![115, 642, 1, 0, 0], ![12, 526, 0, 1, 0], ![435, 630, 0, 0, 1]] where
  M :=![![![-53, 207, -537, 386, -467], ![252, -953, 2442, -1776, 2154], ![-324, 1248, -3143, 2288, -2780], ![1440, -5454, 13806, -9987, 12118], ![-390, 1434, -3690, 2666, -3229]]]
  hmulB := by decide  
  f := ![![![-683, -1167, -1047, -248, -709]], ![![-4248, -5801, -5322, -1260, -3402]], ![![-3833, -5271, -4832, -1144, -3095]], ![![-3096, -4232, -3882, -919, -2482]], ![![-4083, -5715, -5229, -1238, -3366]]]
  g := ![![![355, 595, -537, 386, -467], ![-1632, -2717, 2442, -1776, 2154], ![2105, 3502, -3143, 2288, -2780], ![-9192, -15348, 13806, -9987, 12118], ![2451, 4096, -3690, 2666, -3229]]]
  hle1 := by decide   
  hle2 := by decide  


def P733P1 : CertificateIrreducibleZModOfList' 733 2 2 9 [201, 395, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [338, 732], [0, 1]]
 g := ![![[301, 640], [359], [314, 173], [349, 270], [168, 203], [514], [14, 374], [494, 629], [1]], ![[386, 93], [359], [148, 560], [717, 463], [613, 530], [514], [350, 359], [526, 104], [1]]]
 h' := ![![[338, 732], [320, 376], [657, 574], [219, 222], [683, 418], [36, 495], [118, 499], [394, 314], [532, 338], [0, 1]], ![[0, 1], [599, 357], [424, 159], [489, 511], [498, 315], [222, 238], [190, 234], [241, 419], [428, 395], [338, 732]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [155]]
 b := ![[], [463, 444]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI733N1 : CertifiedPrimeIdeal' SI733N1 733 where
  n := 2
  hpos := by decide
  P := [201, 395, 1]
  hirr := P733P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5243, 5612, 23938, -17486, 27488]
  a := ![2, 16, 14, -18, 32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19775, -32036, 23938, -17486, 27488]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI733N1 : Ideal.IsPrime I733N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI733N1 B_one_repr
lemma NI733N1 : Nat.card (O ⧸ I733N1) = 537289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI733N1
def MulI733N0 : IdealMulLeCertificate' Table 
  ![![683, 1167, 1047, 248, 709]] ![![-53, 207, -537, 386, -467]]
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

def I739N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![907, 150, -44, 231, -379]] i)))

def SI739N0: IdealEqSpanCertificate' Table ![![907, 150, -44, 231, -379]] 
 ![![739, 0, 0, 0, 0], ![0, 739, 0, 0, 0], ![0, 0, 739, 0, 0], ![264, 106, 389, 1, 0], ![373, 228, 401, 0, 1]] where
  M :=![![![907, 150, -44, 231, -379], ![4, -480, 1189, -885, 1090], ![-592, 600, -1665, 1118, -1308], ![232, -2701, 6753, -4976, 6110], ![-266, 731, -1833, 1323, -1581]]]
  hmulB := by decide  
  f := ![![![-73, -8, -148, -19, 61]], ![![68, 376, 101, -49, -30]], ![![168, -86, 343, 64, -136]], ![![72, 5, 142, 20, -54]], ![![75, 65, 142, 10, -52]]]
  g := ![![![110, 84, 84, 231, -379], ![-234, -210, -124, -885, 1090], ![260, 244, 119, 1118, -1308], ![-1306, -1175, -687, -4976, 6110], ![325, 299, 159, 1323, -1581]]]
  hle1 := by decide   
  hle2 := by decide  


def P739P0 : CertificateIrreducibleZModOfList' 739 3 2 9 [59, 400, 598, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [196, 366, 108], [684, 372, 631], [0, 1]]
 g := ![![[648, 638, 478], [18, 605, 180], [121, 164], [478, 38], [736, 254], [456, 381, 161], [697, 217, 502], [267, 141, 1], []], ![[416, 484, 107, 207], [680, 135, 120, 229], [44, 184], [38, 668], [430, 203], [139, 656, 554, 77], [596, 626, 151, 422], [385, 565, 420, 675], [332, 579]], ![[696, 171, 659, 335], [208, 92, 277, 628], [675, 623], [63, 24], [701, 678], [250, 315, 695, 181], [358, 455, 670, 223], [327, 379, 61, 155], [548, 579]]]
 h' := ![![[196, 366, 108], [416, 151, 469], [690, 241, 683], [241, 6, 608], [19, 190, 415], [439, 696, 511], [261, 372, 709], [505, 165, 402], [0, 0, 1], [0, 1]], ![[684, 372, 631], [473, 512, 114], [76, 229, 23], [253, 581, 690], [482, 288, 496], [207, 479, 698], [507, 579, 195], [347, 156, 350], [353, 159, 372], [196, 366, 108]], ![[0, 1], [657, 76, 156], [610, 269, 33], [23, 152, 180], [711, 261, 567], [545, 303, 269], [293, 527, 574], [22, 418, 726], [253, 580, 366], [684, 372, 631]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [374, 288], []]
 b := ![[], [502, 304, 490], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI739N0 : CertifiedPrimeIdeal' SI739N0 739 where
  n := 3
  hpos := by decide
  P := [59, 400, 598, 1]
  hirr := P739P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3777618469, 4547107497, 5858548495, 142711778, 4126797828]
  a := ![60, 102, 106, -52, 251]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2128814453, -1287537545, -2306498325, 142711778, 4126797828]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI739N0 : Ideal.IsPrime I739N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI739N0 B_one_repr
lemma NI739N0 : Nat.card (O ⧸ I739N0) = 403583419 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI739N0

def I739N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3187, 154, 752, 134, -502]] i)))

def SI739N1: IdealEqSpanCertificate' Table ![![3187, 154, 752, 134, -502]] 
 ![![739, 0, 0, 0, 0], ![441, 1, 0, 0, 0], ![44, 0, 1, 0, 0], ![295, 0, 0, 1, 0], ![437, 0, 0, 0, 1]] where
  M :=![![![3187, 154, 752, 134, -502], ![-428, -21, -102, -18, 68], ![-1472, -70, -347, -62, 232], ![-1700, -80, -398, -71, 268], ![-296, -14, -68, -12, 47]]]
  hmulB := by decide  
  f := ![![![65, 54, 320, -210, 234]], ![![39, 33, 190, -124, 138]], ![![4, 2, 21, -14, 16]], ![![25, 26, 118, -77, 86]], ![![39, 32, 192, -126, 141]]]
  g := ![![![111, 154, 752, 134, -502], ![-15, -21, -102, -18, 68], ![-52, -70, -347, -62, 232], ![-61, -80, -398, -71, 268], ![-11, -14, -68, -12, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI739N1 : Nat.card (O ⧸ I739N1) = 739 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI739N1)

lemma isPrimeI739N1 : Ideal.IsPrime I739N1 := prime_ideal_of_norm_prime hp739.out _ NI739N1

def I739N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, -88, -42, 9, 15]] i)))

def SI739N2: IdealEqSpanCertificate' Table ![![-25, -88, -42, 9, 15]] 
 ![![739, 0, 0, 0, 0], ![648, 1, 0, 0, 0], ![170, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-25, -88, -42, 9, 15], ![-128, 46, -259, -45, 102], ![96, 196, 177, -10, -72], ![196, -105, 413, 70, -194], ![-2, -279, 29, 47, -33]]]
  hmulB := by decide  
  f := ![![![-2610661, -126434, -615866, -109713, 411227]], ![![-2288712, -110842, -539917, -96183, 360514]], ![![-598926, -29006, -141289, -25170, 94342]], ![![-104094, -5041, -24557, -4374, 16396]], ![![-73857, -3577, -17423, -3104, 11634]]]
  g := ![![![86, -88, -42, 9, 15], ![18, 46, -259, -45, 102], ![-210, 196, 177, -10, -72], ![0, -105, 413, 70, -194], ![237, -279, 29, 47, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI739N2 : Nat.card (O ⧸ I739N2) = 739 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI739N2)

lemma isPrimeI739N2 : Ideal.IsPrime I739N2 := prime_ideal_of_norm_prime hp739.out _ NI739N2
def MulI739N0 : IdealMulLeCertificate' Table 
  ![![907, 150, -44, 231, -379]] ![![3187, 154, 752, 134, -502]]
  ![![2610661, 126434, 615866, 109713, -411227]] where
 M := ![![![2610661, 126434, 615866, 109713, -411227]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI739N1 : IdealMulLeCertificate' Table 
  ![![2610661, 126434, 615866, 109713, -411227]] ![![-25, -88, -42, 9, 15]]
  ![![739, 0, 0, 0, 0]] where
 M := ![![![-739, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I743N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, 52, -38, -19, -1]] i)))

def SI743N0: IdealEqSpanCertificate' Table ![![-21, 52, -38, -19, -1]] 
 ![![743, 0, 0, 0, 0], ![0, 743, 0, 0, 0], ![294, 313, 1, 0, 0], ![617, 604, 0, 1, 0], ![159, 354, 0, 0, 1]] where
  M :=![![![-21, 52, -38, -19, -1], ![64, 6, 169, -1, -154], ![-80, -284, -99, 14, -40], ![-636, -741, -951, -154, -162], ![-402, -291, -591, -141, -157]]]
  hmulB := by decide  
  f := ![![![-4789, -110, -1430, 23, 479]], ![![784, -526, 1561, -997, 1142]], ![![-1562, -264, 90, -409, 668]], ![![-3335, -523, 93, -799, 1335]], ![![-651, -273, 435, -468, 644]]]
  g := ![![![31, 32, -38, -19, -1], ![-33, 3, 169, -1, -154], ![36, 49, -99, 14, -40], ![538, 602, -951, -154, -162], ![384, 438, -591, -141, -157]]]
  hle1 := by decide   
  hle2 := by decide  


def P743P0 : CertificateIrreducibleZModOfList' 743 2 2 9 [430, 280, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [463, 742], [0, 1]]
 g := ![![[208, 243], [716, 69], [231, 625], [344], [659], [411, 529], [381, 510], [3, 385], [1]], ![[524, 500], [714, 674], [579, 118], [344], [659], [148, 214], [237, 233], [681, 358], [1]]]
 h' := ![![[463, 742], [465, 508], [232, 562], [463, 718], [127, 540], [104, 161], [373, 720], [196, 678], [313, 463], [0, 1]], ![[0, 1], [138, 235], [388, 181], [33, 25], [499, 203], [347, 582], [126, 23], [564, 65], [698, 280], [463, 742]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [246]]
 b := ![[], [131, 123]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI743N0 : CertifiedPrimeIdeal' SI743N0 743 where
  n := 2
  hpos := by decide
  P := [430, 280, 1]
  hirr := P743P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![744, 971, 1634, -1663, 3488]
  a := ![0, 3, 2, -4, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11, -997, 1634, -1663, 3488]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI743N0 : Ideal.IsPrime I743N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI743N0 B_one_repr
lemma NI743N0 : Nat.card (O ⧸ I743N0) = 552049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI743N0

def I743N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![135, -517, 1317, -959, 1164]] i)))

def SI743N1: IdealEqSpanCertificate' Table ![![135, -517, 1317, -959, 1164]] 
 ![![743, 0, 0, 0, 0], ![0, 743, 0, 0, 0], ![403, 659, 1, 0, 0], ![417, 244, 0, 1, 0], ![579, 32, 0, 0, 1]] where
  M :=![![![135, -517, 1317, -959, 1164], ![-624, 2408, -6057, 4399, -5344], ![820, -3100, 7841, -5670, 6880], ![-3584, 13457, -34257, 24790, -30064], ![940, -3595, 9105, -6615, 8031]]]
  hmulB := by decide  
  f := ![![![-1659, 361, -51, 17, 588]], ![![1932, 2332, 2151, 503, 1312]], ![![817, 2267, 1883, 456, 1484]], ![![-281, 988, 696, 179, 772]], ![![-1199, 396, 66, 38, 523]]]
  g := ![![![-1083, -904, 1317, -959, 1164], ![4980, 4161, -6057, 4399, -5344], ![-6431, -5393, 7841, -5670, 6880], ![28091, 23556, -34257, 24790, -30064], ![-7483, -6254, 9105, -6615, 8031]]]
  hle1 := by decide   
  hle2 := by decide  


def P743P1 : CertificateIrreducibleZModOfList' 743 2 2 9 [495, 472, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [271, 742], [0, 1]]
 g := ![![[70, 92], [254, 493], [128, 76], [138], [23], [69, 225], [2, 222], [446, 627], [1]], ![[483, 651], [117, 250], [663, 667], [138], [23], [118, 518], [724, 521], [216, 116], [1]]]
 h' := ![![[271, 742], [580, 564], [538, 646], [351, 318], [289, 630], [23, 282], [496, 15], [644, 544], [248, 271], [0, 1]], ![[0, 1], [366, 179], [256, 97], [341, 425], [129, 113], [659, 461], [103, 728], [211, 199], [132, 472], [271, 742]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [648]]
 b := ![[], [678, 324]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI743N1 : CertifiedPrimeIdeal' SI743N1 743 where
  n := 2
  hpos := by decide
  P := [495, 472, 1]
  hirr := P743P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![437810, 495376, 806232, -127806, 712600]
  a := ![45, 91, 91, -56, 217]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-920288, -703136, 806232, -127806, 712600]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI743N1 : Ideal.IsPrime I743N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI743N1 B_one_repr
lemma NI743N1 : Nat.card (O ⧸ I743N1) = 552049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI743N1

def I743N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 4, -10, 7, -7]] i)))

def SI743N2: IdealEqSpanCertificate' Table ![![-1, 4, -10, 7, -7]] 
 ![![743, 0, 0, 0, 0], ![572, 1, 0, 0, 0], ![163, 0, 1, 0, 0], ![374, 0, 0, 1, 0], ![362, 0, 0, 0, 1]] where
  M :=![![![-1, 4, -10, 7, -7], ![8, -8, 47, -31, 42], ![0, 28, -47, 42, -48], ![52, -67, 279, -168, 234], ![10, 47, -45, 53, -41]]]
  hmulB := by decide  
  f := ![![![-310465, -15030, -73282, -13051, 48917]], ![![-238956, -11568, -56403, -10045, 37650]], ![![-67917, -3288, -16031, -2855, 10701]], ![![-156054, -7555, -36835, -6560, 24588]], ![![-151224, -7321, -35695, -6357, 23827]]]
  g := ![![![-1, 4, -10, 7, -7], ![-9, -8, 47, -31, 42], ![-9, 28, -47, 42, -48], ![-39, -67, 279, -168, 234], ![-33, 47, -45, 53, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI743N2 : Nat.card (O ⧸ I743N2) = 743 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI743N2)

lemma isPrimeI743N2 : Ideal.IsPrime I743N2 := prime_ideal_of_norm_prime hp743.out _ NI743N2
def MulI743N0 : IdealMulLeCertificate' Table 
  ![![-21, 52, -38, -19, -1]] ![![135, -517, 1317, -959, 1164]]
  ![![713, 1785, 1199, -48, -587]] where
 M := ![![![713, 1785, 1199, -48, -587]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI743N1 : IdealMulLeCertificate' Table 
  ![![713, 1785, 1199, -48, -587]] ![![-1, 4, -10, 7, -7]]
  ![![743, 0, 0, 0, 0]] where
 M := ![![![5201, -2229, 33435, -23033, 25262]]]
 hmul := by decide  
 g := ![![![![7, -3, 45, -31, 34]]]]
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

def I751N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, -30, 94, -66, 78]] i)))

def SI751N0: IdealEqSpanCertificate' Table ![![15, -30, 94, -66, 78]] 
 ![![751, 0, 0, 0, 0], ![0, 751, 0, 0, 0], ![218, 495, 1, 0, 0], ![642, 411, 0, 1, 0], ![40, 213, 0, 0, 1]] where
  M :=![![![15, -30, 94, -66, 78], ![-36, 161, -400, 304, -372], ![48, -224, 525, -388, 476], ![-260, 928, -2372, 1693, -2048], ![64, -230, 622, -456, 551]]]
  hmulB := by decide  
  f := ![![![369, 178, 222, 50, 62]], ![![580, 847, 752, 184, 524]], ![![490, 611, 561, 136, 364]], ![![638, 623, 608, 145, 344]], ![![188, 255, 230, 56, 155]]]
  g := ![![![25, -48, 94, -66, 78], ![-124, 203, -400, 304, -372], ![154, -269, 525, -388, 476], ![-650, 1219, -2372, 1693, -2048], ![180, -317, 622, -456, 551]]]
  hle1 := by decide   
  hle2 := by decide  


def P751P0 : CertificateIrreducibleZModOfList' 751 2 2 9 [26, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [670, 750], [0, 1]]
 g := ![![[32, 260], [272, 499], [3, 358], [691, 218], [691], [318, 118], [459, 167], [724, 553], [1]], ![[0, 491], [407, 252], [294, 393], [306, 533], [691], [523, 633], [450, 584], [240, 198], [1]]]
 h' := ![![[670, 750], [438, 367], [673, 572], [58, 127], [107, 370], [744, 428], [82, 683], [702, 501], [725, 670], [0, 1]], ![[0, 1], [0, 384], [152, 179], [285, 624], [177, 381], [622, 323], [333, 68], [675, 250], [527, 81], [670, 750]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [378]]
 b := ![[], [520, 189]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI751N0 : CertifiedPrimeIdeal' SI751N0 751 where
  n := 2
  hpos := by decide
  P := [26, 81, 1]
  hirr := P751P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![79874, 89942, 144730, -19611, 122091]
  a := ![18, 39, 36, -24, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-31644, -119170, 144730, -19611, 122091]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI751N0 : Ideal.IsPrime I751N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI751N0 B_one_repr
lemma NI751N0 : Nat.card (O ⧸ I751N0) = 564001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI751N0

def I751N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1657, -2041, -1901, -445, -1156]] i)))

def SI751N1: IdealEqSpanCertificate' Table ![![-1657, -2041, -1901, -445, -1156]] 
 ![![751, 0, 0, 0, 0], ![0, 751, 0, 0, 0], ![403, 314, 1, 0, 0], ![286, 170, 0, 1, 0], ![16, 195, 0, 0, 1]] where
  M :=![![![-1657, -2041, -1901, -445, -1156], ![-7284, -10068, -9199, -2167, -5872], ![-6404, -8934, -8153, -1920, -5224], ![-45844, -63291, -57839, -13624, -36904], ![-33568, -46269, -42299, -9959, -26973]]]
  hmulB := by decide  
  f := ![![![237, 1981, 307, -293, -100]], ![![3176, 432, 6345, 793, -2544]], ![![1453, 1237, 2814, 175, -1116]], ![![802, 851, 1539, 66, -608]], ![![828, 161, 1650, 198, -661]]]
  g := ![![![1212, 1193, -1901, -445, -1156], ![5877, 5848, -9199, -2167, -5872], ![5209, 5188, -8153, -1920, -5224], ![36951, 36765, -57839, -13624, -36904], ![27021, 26882, -42299, -9959, -26973]]]
  hle1 := by decide   
  hle2 := by decide  


def P751P1 : CertificateIrreducibleZModOfList' 751 2 2 9 [282, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [694, 750], [0, 1]]
 g := ![![[152, 344], [55, 434], [159, 309], [742, 64], [298], [407, 542], [39, 639], [159, 245], [1]], ![[70, 407], [100, 317], [570, 442], [98, 687], [298], [304, 209], [415, 112], [463, 506], [1]]]
 h' := ![![[694, 750], [261, 363], [222, 44], [285, 213], [195, 743], [129, 386], [267, 541], [222, 620], [469, 694], [0, 1]], ![[0, 1], [598, 388], [718, 707], [160, 538], [651, 8], [657, 365], [221, 210], [179, 131], [714, 57], [694, 750]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [660]]
 b := ![[], [393, 330]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI751N1 : CertifiedPrimeIdeal' SI751N1 751 where
  n := 2
  hpos := by decide
  P := [282, 57, 1]
  hirr := P751P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![86540, 100939, 143773, -8611, 116516]
  a := ![21, 37, 37, -19, 92]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-76239, -88283, 143773, -8611, 116516]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI751N1 : Ideal.IsPrime I751N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI751N1 B_one_repr
lemma NI751N1 : Nat.card (O ⧸ I751N1) = 564001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI751N1

def I751N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-61, -53, -115, -7, 46]] i)))

def SI751N2: IdealEqSpanCertificate' Table ![![-61, -53, -115, -7, 46]] 
 ![![751, 0, 0, 0, 0], ![521, 1, 0, 0, 0], ![351, 0, 1, 0, 0], ![494, 0, 0, 1, 0], ![719, 0, 0, 0, 1]] where
  M :=![![![-61, -53, -115, -7, 46], ![-28, 256, -79, -55, 36], ![156, 52, 307, 34, -124], ![52, -433, 141, 94, -64], ![-140, -295, -255, 15, 99]]]
  hmulB := by decide  
  f := ![![![-911, -147, -875, 237, -466]], ![![-633, -105, -606, 162, -322]], ![![-427, -69, -414, 113, -222]], ![![-606, -115, -571, 142, -300]], ![![-879, -148, -850, 228, -455]]]
  g := ![![![51, -53, -115, -7, 46], ![-139, 256, -79, -55, 36], ![-83, 52, 307, 34, -124], ![234, -433, 141, 94, -64], ![219, -295, -255, 15, 99]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI751N2 : Nat.card (O ⧸ I751N2) = 751 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI751N2)

lemma isPrimeI751N2 : Ideal.IsPrime I751N2 := prime_ideal_of_norm_prime hp751.out _ NI751N2
def MulI751N0 : IdealMulLeCertificate' Table 
  ![![15, -30, 94, -66, 78]] ![![-1657, -2041, -1901, -445, -1156]]
  ![![-911, -147, -875, 237, -466]] where
 M := ![![![-911, -147, -875, 237, -466]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI751N1 : IdealMulLeCertificate' Table 
  ![![-911, -147, -875, 237, -466]] ![![-61, -53, -115, -7, 46]]
  ![![751, 0, 0, 0, 0]] where
 M := ![![![751, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC751 : ContainsPrimesAboveP 751 ![I751N0, I751N1, I751N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI751N0
    exact isPrimeI751N1
    exact isPrimeI751N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 751 (by decide) (𝕀 ⊙ MulI751N0 ⊙ MulI751N1)
instance hp757 : Fact (Nat.Prime 757) := {out := by norm_num}

def I757N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![112515, 5445, 26551, 4722, -17715]] i)))

def SI757N0: IdealEqSpanCertificate' Table ![![112515, 5445, 26551, 4722, -17715]] 
 ![![757, 0, 0, 0, 0], ![0, 757, 0, 0, 0], ![0, 0, 757, 0, 0], ![690, 432, 101, 1, 0], ![275, 81, 468, 0, 1]] where
  M :=![![![112515, 5445, 26551, 4722, -17715], ![-15096, -715, -3598, -608, 2346], ![-51972, -2534, -12213, -2218, 8228], ![-60116, -2828, -14378, -2375, 9286], ![-10490, -530, -2420, -480, 1703]]]
  hmulB := by decide  
  f := ![![![-27, 55, -63, -16, 35]], ![![148, 253, 254, 4, -58]], ![![76, -138, 147, 54, -24]], ![![70, 176, 107, -5, -4]], ![![53, -38, 95, 28, -8]]]
  g := ![![![2280, -792, 10357, 4722, -17715], ![-318, 95, -1374, -608, 2346], ![-1036, 382, -4807, -2218, 8228], ![-1288, 358, -5443, -2375, 9286], ![-195, 91, -992, -480, 1703]]]
  hle1 := by decide   
  hle2 := by decide  


def P757P0 : CertificateIrreducibleZModOfList' 757 3 2 9 [484, 520, 175, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [507, 702, 318], [75, 54, 439], [0, 1]]
 g := ![![[110, 202, 232], [4, 138], [300, 738, 332], [694, 145], [682, 299, 143], [102, 160, 406], [82, 203, 441], [582, 582, 1], []], ![[603, 111, 524, 146], [240, 637], [673, 92, 337, 672], [199, 133], [193, 572, 53, 107], [740, 460, 263, 677], [7, 486, 43, 293], [420, 125, 623, 720], [288, 443]], ![[170, 599, 375, 241], [450, 232], [296, 646, 664, 5], [338, 76], [318, 66, 484, 271], [31, 556, 318, 369], [588, 151, 707, 643], [246, 537, 728, 197], [167, 443]]]
 h' := ![![[507, 702, 318], [632, 197, 630], [144, 90, 294], [751, 318, 33], [721, 338, 566], [594, 234, 727], [433, 153, 584], [673, 76, 21], [0, 0, 1], [0, 1]], ![[75, 54, 439], [571, 233, 527], [397, 316, 590], [7, 234, 711], [63, 565, 274], [564, 265, 120], [345, 588, 705], [547, 630, 321], [322, 193, 54], [507, 702, 318]], ![[0, 1], [736, 327, 357], [98, 351, 630], [124, 205, 13], [31, 611, 674], [206, 258, 667], [113, 16, 225], [156, 51, 415], [497, 564, 702], [75, 54, 439]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [419, 408], []]
 b := ![[], [251, 612, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI757N0 : CertifiedPrimeIdeal' SI757N0 757 where
  n := 3
  hpos := by decide
  P := [484, 520, 175, 1]
  hirr := P757P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8399138586, -9150210839, -14578260427, 1011443322, -10475928029]
  a := ![-75, -156, -157, 98, -371]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2872635637, 531646558, 6322325339, 1011443322, -10475928029]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI757N0 : Ideal.IsPrime I757N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI757N0 B_one_repr
lemma NI757N0 : Nat.card (O ⧸ I757N0) = 433798093 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI757N0

def I757N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, 55, -63, -16, 35]] i)))

def SI757N1: IdealEqSpanCertificate' Table ![![-27, 55, -63, -16, 35]] 
 ![![757, 0, 0, 0, 0], ![0, 757, 0, 0, 0], ![626, 732, 1, 0, 0], ![345, 346, 0, 1, 0], ![570, 158, 0, 0, 1]] where
  M :=![![![-27, 55, -63, -16, 35], ![148, 253, 254, 4, -58], ![76, -138, 147, 54, -24], ![8, -76, -106, 73, 302], ![-10, 200, -130, 0, 249]]]
  hmulB := by decide  
  f := ![![![112515, 5445, 26551, 4722, -17715]], ![![-15096, -715, -3598, -608, 2346]], ![![78378, 3808, 18461, 3314, -12370]], ![![44299, 2151, 10437, 1871, -6989]], ![![81556, 3950, 19238, 3428, -12847]]]
  g := ![![![33, 61, -63, -16, 35], ![-168, -235, 254, 4, -58], ![-128, -162, 147, 54, -24], ![-173, 6, -106, 73, 302], ![-80, 74, -130, 0, 249]]]
  hle1 := by decide   
  hle2 := by decide  


def P757P1 : CertificateIrreducibleZModOfList' 757 2 2 9 [683, 112, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [645, 756], [0, 1]]
 g := ![![[244, 624], [525], [303, 531], [487], [490, 289], [199, 81], [78, 244], [142, 432], [1]], ![[0, 133], [525], [634, 226], [487], [673, 468], [211, 676], [2, 513], [206, 325], [1]]]
 h' := ![![[645, 756], [674, 371], [469, 306], [179, 186], [681, 128], [343, 17], [473, 9], [667, 344], [74, 645], [0, 1]], ![[0, 1], [0, 386], [262, 451], [543, 571], [728, 629], [710, 740], [222, 748], [746, 413], [506, 112], [645, 756]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [470]]
 b := ![[], [291, 235]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI757N1 : CertifiedPrimeIdeal' SI757N1 757 where
  n := 2
  hpos := by decide
  P := [683, 112, 1]
  hirr := P757P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![184798, 200177, 330838, -36071, 253970]
  a := ![-29, -59, -58, 36, -145]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-448135, -356169, 330838, -36071, 253970]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI757N1 : Ideal.IsPrime I757N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI757N1 B_one_repr
lemma NI757N1 : Nat.card (O ⧸ I757N1) = 573049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI757N1
def MulI757N0 : IdealMulLeCertificate' Table 
  ![![112515, 5445, 26551, 4722, -17715]] ![![-27, 55, -63, -16, 35]]
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

def I761N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, -28, 74, -52, 62]] i)))

def SI761N0: IdealEqSpanCertificate' Table ![![19, -28, 74, -52, 62]] 
 ![![761, 0, 0, 0, 0], ![0, 761, 0, 0, 0], ![321, 132, 1, 0, 0], ![39, 139, 0, 1, 0], ![595, 425, 0, 0, 1]] where
  M :=![![![19, -28, 74, -52, 62], ![-36, 133, -332, 240, -292], ![40, -170, 429, -310, 376], ![-204, 730, -1876, 1355, -1644], ![48, -200, 494, -362, 439]]]
  hmulB := by decide  
  f := ![![![35, -40, -66, -4, 10]], ![![-68, 109, -100, -48, -12]], ![![3, 2, -45, -10, 2]], ![![-11, 17, -22, -9, -2]], ![![-11, 29, -108, -30, 1]]]
  g := ![![![-77, -38, 74, -52, 62], ![356, 177, -332, 240, -292], ![-459, -228, 429, -310, 376], ![2007, 997, -1876, 1355, -1644], ![-533, -265, 494, -362, 439]]]
  hle1 := by decide   
  hle2 := by decide  


def P761P0 : CertificateIrreducibleZModOfList' 761 2 2 9 [182, 640, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [121, 760], [0, 1]]
 g := ![![[522, 46], [46], [715], [489, 323], [225, 256], [19, 25], [327, 230], [47, 182], [1]], ![[0, 715], [46], [715], [0, 438], [0, 505], [0, 736], [0, 531], [0, 579], [1]]]
 h' := ![![[121, 760], [760, 239], [0, 239], [39, 572], [144, 590], [347, 16], [605, 756], [578, 360], [579, 121], [0, 1]], ![[0, 1], [0, 522], [1, 522], [0, 189], [0, 171], [0, 745], [0, 5], [0, 401], [0, 640], [121, 760]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [315]]
 b := ![[], [174, 538]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI761N0 : CertifiedPrimeIdeal' SI761N0 761 where
  n := 2
  hpos := by decide
  P := [182, 640, 1]
  hirr := P761P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![336159, 406287, 564686, -53180, 522752]
  a := ![39, 71, 70, -37, 177]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-643747, -379645, 564686, -53180, 522752]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI761N0 : Ideal.IsPrime I761N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI761N0 B_one_repr
lemma NI761N0 : Nat.card (O ⧸ I761N0) = 579121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI761N0

def I761N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 341, 117, -42, -43]] i)))

def SI761N1: IdealEqSpanCertificate' Table ![![83, 341, 117, -42, -43]] 
 ![![761, 0, 0, 0, 0], ![107, 1, 0, 0, 0], ![536, 0, 1, 0, 0], ![366, 0, 0, 1, 0], ![691, 0, 0, 0, 1]] where
  M :=![![![83, 341, 117, -42, -43], ![512, -77, 1036, 158, -422], ![-340, -816, -601, 56, 232], ![-884, 112, -1772, -267, 722], ![-122, 946, -326, -208, 147]]]
  hmulB := by decide  
  f := ![![![-3847, -6425, -3313, -2576, -1689]], ![![-569, -936, -511, -362, -269]], ![![-2732, -4564, -2349, -1832, -1196]], ![![-2026, -3298, -1870, -1243, -1004]], ![![-3615, -6011, -3147, -2388, -1618]]]
  g := ![![![-71, 341, 117, -42, -43], ![-411, -77, 1036, 158, -422], ![300, -816, -601, 56, 232], ![704, 112, -1772, -267, 722], ![63, 946, -326, -208, 147]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI761N1 : Nat.card (O ⧸ I761N1) = 761 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI761N1)

lemma isPrimeI761N1 : Ideal.IsPrime I761N1 := prime_ideal_of_norm_prime hp761.out _ NI761N1

def I761N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![535, 24, 120, 22, -82]] i)))

def SI761N2: IdealEqSpanCertificate' Table ![![535, 24, 120, 22, -82]] 
 ![![761, 0, 0, 0, 0], ![136, 1, 0, 0, 0], ![289, 0, 1, 0, 0], ![693, 0, 0, 1, 0], ![373, 0, 0, 0, 1]] where
  M :=![![![535, 24, 120, 22, -82], ![-72, 13, -18, -6, 12], ![-240, -12, -41, -8, 32], ![-288, -42, -66, -7, 44], ![-60, -18, -30, -2, 15]]]
  hmulB := by decide  
  f := ![![![-169, -528, 264, -470, 314]], ![![-32, -95, 42, -82, 52]], ![![-65, -204, 103, -182, 122]], ![![-165, -486, 210, -417, 262]], ![![-89, -270, 126, -236, 153]]]
  g := ![![![-29, 24, 120, 22, -82], ![4, 13, -18, -6, 12], ![9, -12, -41, -8, 32], ![17, -42, -66, -7, 44], ![9, -18, -30, -2, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI761N2 : Nat.card (O ⧸ I761N2) = 761 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI761N2)

lemma isPrimeI761N2 : Ideal.IsPrime I761N2 := prime_ideal_of_norm_prime hp761.out _ NI761N2

def I761N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39, 155, -393, 285, -346]] i)))

def SI761N3: IdealEqSpanCertificate' Table ![![-39, 155, -393, 285, -346]] 
 ![![761, 0, 0, 0, 0], ![752, 1, 0, 0, 0], ![363, 0, 1, 0, 0], ![577, 0, 0, 1, 0], ![235, 0, 0, 0, 1]] where
  M :=![![![-39, 155, -393, 285, -346], ![188, -712, 1807, -1309, 1588], ![-244, 918, -2331, 1688, -2048], ![1060, -4013, 10183, -7376, 8948], ![-284, 1069, -2717, 1967, -2387]]]
  hmulB := by decide  
  f := ![![![-147, 267, -1151, -205, 418]], ![![-144, 268, -1135, -203, 412]], ![![-69, 125, -546, -97, 198]], ![![-115, 194, -878, -155, 318]], ![![-49, 80, -362, -64, 131]]]
  g := ![![![-75, 155, -393, 285, -346], ![344, -712, 1807, -1309, 1588], ![-443, 918, -2331, 1688, -2048], ![1939, -4013, 10183, -7376, 8948], ![-515, 1069, -2717, 1967, -2387]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI761N3 : Nat.card (O ⧸ I761N3) = 761 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI761N3)

lemma isPrimeI761N3 : Ideal.IsPrime I761N3 := prime_ideal_of_norm_prime hp761.out _ NI761N3
def MulI761N0 : IdealMulLeCertificate' Table 
  ![![19, -28, 74, -52, 62]] ![![83, 341, 117, -42, -43]]
  ![![485, 1079, 673, -90, -263]] where
 M := ![![![485, 1079, 673, -90, -263]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI761N1 : IdealMulLeCertificate' Table 
  ![![485, 1079, 673, -90, -263]] ![![535, 24, 120, 22, -82]]
  ![![61967, 26105, 25015, -32, -13191]] where
 M := ![![![61967, 26105, 25015, -32, -13191]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI761N2 : IdealMulLeCertificate' Table 
  ![![61967, 26105, 25015, -32, -13191]] ![![-39, 155, -393, 285, -346]]
  ![![761, 0, 0, 0, 0]] where
 M := ![![![99691, 9132, 22830, 3805, -15981]]]
 hmul := by decide  
 g := ![![![![131, 12, 30, 5, -21]]]]
 hle2 := by decide  


def PBC761 : ContainsPrimesAboveP 761 ![I761N0, I761N1, I761N2, I761N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI761N0
    exact isPrimeI761N1
    exact isPrimeI761N2
    exact isPrimeI761N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 761 (by decide) (𝕀 ⊙ MulI761N0 ⊙ MulI761N1 ⊙ MulI761N2)


lemma PB853I14_primes (p : ℕ) :
  p ∈ Set.range ![709, 719, 727, 733, 739, 743, 751, 757, 761] ↔ Nat.Prime p ∧ 701 < p ∧ p ≤ 761 := by
  rw [← List.mem_ofFn']
  convert primes_range 701 761 (by omega)

def PB853I14 : PrimesBelowBoundCertificateInterval O 701 761 853 where
  m := 9
  g := ![3, 2, 2, 2, 3, 3, 3, 2, 4]
  P := ![709, 719, 727, 733, 739, 743, 751, 757, 761]
  hP := PB853I14_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I709N0, I709N1, I709N2]
    · exact ![I719N0, I719N1]
    · exact ![I727N0, I727N1]
    · exact ![I733N0, I733N1]
    · exact ![I739N0, I739N1, I739N2]
    · exact ![I743N0, I743N1, I743N2]
    · exact ![I751N0, I751N1, I751N2]
    · exact ![I757N0, I757N1]
    · exact ![I761N0, I761N1, I761N2, I761N3]
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
    · exact ![356400829, 709, 709]
    · exact ![267248675521, 719]
    · exact ![384240583, 528529]
    · exact ![393832837, 537289]
    · exact ![403583419, 739, 739]
    · exact ![552049, 552049, 743]
    · exact ![564001, 564001, 751]
    · exact ![433798093, 573049]
    · exact ![579121, 761, 761, 761]
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
      exact NI751N1
      exact NI751N2
    · dsimp ; intro j
      fin_cases j
      exact NI757N0
      exact NI757N1
    · dsimp ; intro j
      fin_cases j
      exact NI761N0
      exact NI761N1
      exact NI761N2
      exact NI761N3
  β := ![I709N1, I709N2, I719N1, I739N1, I739N2, I743N2, I751N2, I761N1, I761N2, I761N3]
  Il := ![[I709N1, I709N2], [I719N1], [], [], [I739N1, I739N2], [I743N2], [I751N2], [], [I761N1, I761N2, I761N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
