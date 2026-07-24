
import IdealArithmetic.Examples.NF5_3_729000000_4.RI5_3_729000000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp647 : Fact (Nat.Prime 647) := {out := by norm_num}

def I647N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2112417207, 60415065, 238973935, 62126284, -204038434]] i)))

def SI647N0: IdealEqSpanCertificate' Table ![![-2112417207, 60415065, 238973935, 62126284, -204038434]] 
 ![![647, 0, 0, 0, 0], ![0, 647, 0, 0, 0], ![0, 0, 647, 0, 0], ![144, 56, 142, 1, 0], ![123, 413, 316, 0, 1]] where
  M :=![![![-2112417207, 60415065, 238973935, 62126284, -204038434], ![647434466, -19054121, -73368704, -19062402, 62761778], ![-199434478, 3092970, 21951587, 5761808, -18165202], ![127844820, -9118047, -15738939, -3976549, 14646090], ![-294617188, 4577139, 32430233, 8512044, -26837985]]]
  hmulB := by decide  
  f := ![![![-4296341, -17048799, 8017361, 4873394, -9972994]], ![![20624606, 81492035, -38271802, -22952430, 47150498]], ![![-98037910, -385759998, 180934813, 107075836, -220804834]], ![![-20255448, -79709647, 37387813, 22133377, -45637518]], ![![-35501559, -139502365, 65403900, 38535666, -79566785]]]
  g := ![![![21697257, 124960149, 86388233, 62126284, -204038434], ![-6688220, -38442309, -26583044, -19062402, 62761778], ![1862728, 11101484, 7641389, 5761808, -18165202], ![-1701702, -9018959, -6304843, -3976549, 14646090], ![2752273, 16401840, 11289835, 8512044, -26837985]]]
  hle1 := by decide   
  hle2 := by decide  


def P647P0 : CertificateIrreducibleZModOfList' 647 3 2 9 [2, 141, 75, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [632, 222, 208], [587, 424, 439], [0, 1]]
 g := ![![[331, 147, 339], [450, 543, 81], [316, 291, 12], [80, 602], [170, 21], [71, 17], [225, 408], [308, 572, 1], []], ![[418, 365, 576, 156], [561, 249, 435, 397], [78, 627, 412, 166], [189, 220], [310, 49], [67, 314], [79, 372], [466, 509, 40, 43], [383, 562]], ![[58, 485, 11, 472], [27, 350, 302, 461], [394, 571, 345, 605], [395, 1], [242, 402], [503, 330], [186, 449], [171, 364, 627, 643], [152, 562]]]
 h' := ![![[632, 222, 208], [394, 389, 131], [15, 495, 638], [65, 508, 403], [15, 88, 132], [238, 105, 301], [511, 329, 240], [31, 71, 413], [0, 0, 1], [0, 1]], ![[587, 424, 439], [34, 180, 586], [47, 210, 153], [225, 479, 267], [394, 324, 514], [160, 146, 7], [312, 287, 31], [42, 530, 309], [106, 325, 424], [632, 222, 208]], ![[0, 1], [573, 78, 577], [175, 589, 503], [638, 307, 624], [199, 235, 1], [6, 396, 339], [587, 31, 376], [260, 46, 572], [61, 322, 222], [587, 424, 439]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 334], []]
 b := ![[], [179, 425, 353], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI647N0 : CertifiedPrimeIdeal' SI647N0 647 where
  n := 3
  hpos := by decide
  P := [2, 141, 75, 1]
  hirr := P647P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1568546925, 3917051682, 2073366064, 793624919, -3700550652]
  a := ![47, 70, 42, 53, -188]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![529295655, 2299538602, 1636402834, 793624919, -3700550652]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI647N0 : Ideal.IsPrime I647N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI647N0 B_one_repr
lemma NI647N0 : Nat.card (O ⧸ I647N0) = 270840023 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI647N0

def I647N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4296341, -17048799, 8017361, 4873394, -9972994]] i)))

def SI647N1: IdealEqSpanCertificate' Table ![![-4296341, -17048799, 8017361, 4873394, -9972994]] 
 ![![647, 0, 0, 0, 0], ![0, 647, 0, 0, 0], ![351, 364, 1, 0, 0], ![319, 63, 0, 1, 0], ![216, 86, 0, 0, 1]] where
  M :=![![![-4296341, -17048799, 8017361, 4873394, -9972994], ![20624606, 81492035, -38271802, -22952430, 47150498], ![-98037910, -385759998, 180934813, 107075836, -220804834], ![279803532, 1097251203, -514107507, -300906449, 622495530], ![20958552, 82921035, -38958785, -23462146, 48140237]]]
  hmulB := by decide  
  f := ![![![-2112417207, 60415065, 238973935, 62126284, -204038434]], ![![647434466, -19054121, -73368704, -19062402, 62761778]], ![![-782058313, 22060403, 88401228, 22988212, -75410152]], ![![-978276465, 27917895, 110656442, 28768743, -94466186]], ![![-619624992, 17643859, 70078967, 18220128, -59817043]]]
  g := ![![![-3429422, -3685803, 8017361, 4873394, -9972994], ![16369930, 17625175, -38271802, -22952430, 47150498], ![-77387179, -83466142, 180934813, 107075836, -220804834], ![219878920, 237488214, -514107507, -300906449, 622495530], ![16664027, 17931953, -38958785, -23462146, 48140237]]]
  hle1 := by decide   
  hle2 := by decide  


def P647P1 : CertificateIrreducibleZModOfList' 647 2 2 9 [448, 438, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [209, 646], [0, 1]]
 g := ![![[518, 13], [109, 32], [115, 147], [411], [17], [369], [14], [525, 332], [1]], ![[0, 634], [327, 615], [429, 500], [411], [17], [369], [14], [37, 315], [1]]]
 h' := ![![[209, 646], [340, 51], [240, 144], [223, 207], [394, 466], [588, 240], [600, 164], [308, 590], [199, 209], [0, 1]], ![[0, 1], [0, 596], [574, 503], [137, 440], [91, 181], [282, 407], [585, 483], [41, 57], [531, 438], [209, 646]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [65, 343]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI647N1 : CertifiedPrimeIdeal' SI647N1 647 where
  n := 2
  hpos := by decide
  P := [448, 438, 1]
  hirr := P647P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-54126303, -121892423, -82130779, -38456491, 159311554]
  a := ![562, 811, 499, 623, -2245]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![10247453, 28586826, -82130779, -38456491, 159311554]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI647N1 : Ideal.IsPrime I647N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI647N1 B_one_repr
lemma NI647N1 : Nat.card (O ⧸ I647N1) = 418609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI647N1
def MulI647N0 : IdealMulLeCertificate' Table 
  ![![-2112417207, 60415065, 238973935, 62126284, -204038434]] ![![-4296341, -17048799, 8017361, 4873394, -9972994]]
  ![![647, 0, 0, 0, 0]] where
 M := ![![![647, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I653N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-87, -248, -88, -24, 128]] i)))

def SI653N0: IdealEqSpanCertificate' Table ![![-87, -248, -88, -24, 128]] 
 ![![653, 0, 0, 0, 0], ![0, 653, 0, 0, 0], ![572, 472, 1, 0, 0], ![546, 321, 0, 1, 0], ![347, 546, 0, 0, 1]] where
  M :=![![![-87, -248, -88, -24, 128], ![-496, -1535, -192, 16, 320], ![-1696, -4800, -1823, -512, 2624], ![-4176, -13200, -864, 481, 1728], ![-2504, -7528, -1544, -200, 2369]]]
  hmulB := by decide  
  f := ![![![104773, -2984, -11848, -3080, 10112]], ![![-32080, 1037, 3648, 944, -3136]], ![![68604, -1864, -7743, -2016, 6592]], ![![71826, -1983, -8112, -2111, 6912]], ![![28875, -718, -3248, -848, 2753]]]
  g := ![![![29, -32, -88, -24, 128], ![-16, -139, -192, 16, 320], ![628, -632, -1823, -512, 2624], ![-570, -1077, -864, 481, 1728], ![257, -778, -1544, -200, 2369]]]
  hle1 := by decide   
  hle2 := by decide  


def P653P0 : CertificateIrreducibleZModOfList' 653 2 2 9 [136, 566, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 652], [0, 1]]
 g := ![![[129, 629], [477], [164, 114], [487, 452], [87], [28], [583], [123, 386], [1]], ![[0, 24], [477], [287, 539], [631, 201], [87], [28], [583], [402, 267], [1]]]
 h' := ![![[87, 652], [384, 536], [551, 204], [374, 296], [98, 165], [295, 273], [190, 460], [250, 209], [517, 87], [0, 1]], ![[0, 1], [0, 117], [15, 449], [6, 357], [87, 488], [538, 380], [377, 193], [149, 444], [250, 566], [87, 652]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [248]]
 b := ![[], [483, 124]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI653N0 : CertifiedPrimeIdeal' SI653N0 653 where
  n := 2
  hpos := by decide
  P := [136, 566, 1]
  hirr := P653P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-309322, -705684, -502694, -221804, 915254]
  a := ![45, 66, 40, 50, -179]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![138964, -293972, -502694, -221804, 915254]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI653N0 : Ideal.IsPrime I653N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI653N0 B_one_repr
lemma NI653N0 : Nat.card (O ⧸ I653N0) = 426409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI653N0

def I653N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20015, -656, -2284, -592, 1968]] i)))

def SI653N1: IdealEqSpanCertificate' Table ![![20015, -656, -2284, -592, 1968]] 
 ![![653, 0, 0, 0, 0], ![0, 653, 0, 0, 0], ![400, 55, 1, 0, 0], ![554, 619, 0, 1, 0], ![579, 620, 0, 0, 1]] where
  M :=![![![20015, -656, -2284, -592, 1968], ![-6288, -241, 612, 168, -432], ![1152, -2184, -637, -120, 1008], ![-2736, -4344, -732, -97, 1584], ![1716, -3184, -932, -176, 1475]]]
  hmulB := by decide  
  f := ![![![835, 3184, -1492, -784, 1680]], ![![-3696, -13949, 6396, 3288, -7056]], ![![224, 865, -417, -224, 480]], ![![-2858, -10755, 4904, 2503, -5376]], ![![-2775, -10444, 4760, 2432, -5221]]]
  g := ![![![187, -1116, -2284, -592, 1968], ![-144, 199, 612, 168, -432], ![-400, -793, -637, -120, 1008], ![-878, -1357, -732, -97, 1584], ![-585, -1160, -932, -176, 1475]]]
  hle1 := by decide   
  hle2 := by decide  


def P653P1 : CertificateIrreducibleZModOfList' 653 2 2 9 [329, 141, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [512, 652], [0, 1]]
 g := ![![[187, 131], [625], [596, 325], [35, 634], [52], [10], [604], [160, 291], [1]], ![[0, 522], [625], [481, 328], [102, 19], [52], [10], [604], [268, 362], [1]]]
 h' := ![![[512, 652], [623, 625], [469, 25], [239, 134], [162, 274], [434, 576], [464, 513], [253, 390], [324, 512], [0, 1]], ![[0, 1], [0, 28], [209, 628], [282, 519], [55, 379], [190, 77], [614, 140], [115, 263], [615, 141], [512, 652]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [323]]
 b := ![[], [448, 488]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI653N1 : CertifiedPrimeIdeal' SI653N1 653 where
  n := 2
  hpos := by decide
  P := [329, 141, 1]
  hirr := P653P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7238724, -15907529, -11556289, -5558270, 22374645]
  a := ![-209, -304, -187, -235, 837]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8055683, -15026068, -11556289, -5558270, 22374645]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI653N1 : Ideal.IsPrime I653N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI653N1 B_one_repr
lemma NI653N1 : Nat.card (O ⧸ I653N1) = 426409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI653N1

def I653N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 24, -12, -8, 16]] i)))

def SI653N2: IdealEqSpanCertificate' Table ![![11, 24, -12, -8, 16]] 
 ![![653, 0, 0, 0, 0], ![126, 1, 0, 0, 0], ![449, 0, 1, 0, 0], ![547, 0, 0, 1, 0], ![626, 0, 0, 0, 1]] where
  M :=![![![11, 24, -12, -8, 16], ![-32, -125, 60, 40, -80], ![160, 648, -305, -200, 400], ![-480, -1944, 924, 595, -1200], ![-28, -120, 60, 40, -81]]]
  hmulB := by decide  
  f := ![![![2055, 5736, 1260, 200, -2000]], ![![410, 1147, 252, 40, -400]], ![![1475, 4128, 907, 144, -1440]], ![![1833, 5136, 1128, 179, -1792]], ![![2050, 5736, 1260, 200, -2001]]]
  g := ![![![-5, 24, -12, -8, 16], ![26, -125, 60, 40, -80], ![-131, 648, -305, -200, 400], ![391, -1944, 924, 595, -1200], ![26, -120, 60, 40, -81]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI653N2 : Nat.card (O ⧸ I653N2) = 653 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI653N2)

lemma isPrimeI653N2 : Ideal.IsPrime I653N2 := prime_ideal_of_norm_prime hp653.out _ NI653N2
def MulI653N0 : IdealMulLeCertificate' Table 
  ![![-87, -248, -88, -24, 128]] ![![20015, -656, -2284, -592, 1968]]
  ![![2055, 5736, 1260, 200, -2000]] where
 M := ![![![2055, 5736, 1260, 200, -2000]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI653N1 : IdealMulLeCertificate' Table 
  ![![2055, 5736, 1260, 200, -2000]] ![![11, 24, -12, -8, 16]]
  ![![653, 0, 0, 0, 0]] where
 M := ![![![653, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC653 : ContainsPrimesAboveP 653 ![I653N0, I653N1, I653N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI653N0
    exact isPrimeI653N1
    exact isPrimeI653N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 653 (by decide) (𝕀 ⊙ MulI653N0 ⊙ MulI653N1)
instance hp659 : Fact (Nat.Prime 659) := {out := by norm_num}

def I659N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![65, 658, 146, 24, -270]] i)))

def SI659N0: IdealEqSpanCertificate' Table ![![65, 658, 146, 24, -270]] 
 ![![659, 0, 0, 0, 0], ![0, 659, 0, 0, 0], ![0, 0, 659, 0, 0], ![321, 464, 71, 1, 0], ![514, 278, 367, 0, 1]] where
  M :=![![![65, 658, 146, 24, -270], ![1206, 3359, 660, 100, -1314], ![5970, 17388, 3419, 520, -6798], ![12450, 36138, 7134, 1079, -14154], ![8790, 25598, 5050, 768, -10027]]]
  hmulB := by decide  
  f := ![![![7, 34, 2, 0, -6]], ![![30, 85, 36, 4, -42]], ![![186, 540, 97, 40, -198]], ![![45, 136, 37, 7, -54]], ![![122, 364, 71, 24, -133]]]
  g := ![![![199, 98, 148, 24, -270], ![978, 489, 722, 100, -1314], ![5058, 2528, 3735, 520, -6798], ![10533, 5266, 7777, 1079, -14154], ![7460, 3728, 5509, 768, -10027]]]
  hle1 := by decide   
  hle2 := by decide  


def P659P0 : CertificateIrreducibleZModOfList' 659 3 2 9 [88, 202, 184, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [109, 225, 4], [366, 433, 655], [0, 1]]
 g := ![![[171, 466, 627], [61, 658, 651], [447, 613], [362, 92], [638, 630, 179], [526, 528], [181, 194], [45, 475, 1], []], ![[22, 280, 278, 207], [370, 196, 224, 275], [583, 211], [615, 236], [652, 431, 139, 14], [58, 168], [41, 325], [91, 337, 568, 14], [174, 16]], ![[192, 73, 250, 480], [26, 490, 35, 294], [264, 92], [79, 226], [174, 593, 360, 21], [374, 523], [507, 324], [317, 340, 614, 472], [182, 16]]]
 h' := ![![[109, 225, 4], [563, 349, 351], [273, 238, 505], [601, 527, 602], [530, 641, 435], [346, 136, 293], [583, 191, 235], [653, 512, 463], [0, 0, 1], [0, 1]], ![[366, 433, 655], [94, 512, 491], [370, 375, 170], [555, 176, 492], [36, 21, 468], [364, 283, 226], [645, 385, 374], [83, 554, 214], [523, 632, 433], [109, 225, 4]], ![[0, 1], [329, 457, 476], [332, 46, 643], [275, 615, 224], [623, 656, 415], [475, 240, 140], [313, 83, 50], [392, 252, 641], [638, 27, 225], [366, 433, 655]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [579, 19], []]
 b := ![[], [645, 71, 160], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI659N0 : CertifiedPrimeIdeal' SI659N0 659 where
  n := 3
  hpos := by decide
  P := [88, 202, 184, 1]
  hirr := P659P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![508922337, 979619511, 1286272985, 589618047, -2112279064]
  a := ![40, 60, 38, 49, -161]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1361081894, 477405805, 1114764504, 589618047, -2112279064]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI659N0 : Ideal.IsPrime I659N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI659N0 B_one_repr
lemma NI659N0 : Nat.card (O ⧸ I659N0) = 286191179 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI659N0

def I659N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 34, 2, 0, -6]] i)))

def SI659N1: IdealEqSpanCertificate' Table ![![7, 34, 2, 0, -6]] 
 ![![659, 0, 0, 0, 0], ![0, 659, 0, 0, 0], ![456, 518, 1, 0, 0], ![288, 243, 0, 1, 0], ![41, 167, 0, 0, 1]] where
  M :=![![![7, 34, 2, 0, -6], ![30, 85, 36, 4, -42], ![186, 540, 97, 40, -198], ![282, 930, 150, -83, -114], ![198, 590, 154, 24, -221]]]
  hmulB := by decide  
  f := ![![![65, 658, 146, 24, -270]], ![![1206, 3359, 660, 100, -1314]], ![![1002, 3122, 625, 96, -1230]], ![![492, 1581, 318, 49, -624]], ![![323, 931, 184, 28, -365]]]
  g := ![![![-1, 0, 2, 0, -6], ![-24, -19, 36, 4, -42], ![-72, -40, 97, 40, -198], ![-60, -57, 150, -83, -114], ![-103, -73, 154, 24, -221]]]
  hle1 := by decide   
  hle2 := by decide  


def P659P1 : CertificateIrreducibleZModOfList' 659 2 2 9 [61, 132, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [527, 658], [0, 1]]
 g := ![![[121, 605], [600, 547], [64], [566], [445, 585], [285], [3], [230, 290], [1]], ![[0, 54], [227, 112], [64], [566], [328, 74], [285], [3], [172, 369], [1]]]
 h' := ![![[527, 658], [304, 202], [373, 246], [461, 8], [533, 624], [581, 309], [53, 277], [468, 483], [598, 527], [0, 1]], ![[0, 1], [0, 457], [192, 413], [64, 651], [540, 35], [651, 350], [393, 382], [635, 176], [229, 132], [527, 658]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [487]]
 b := ![[], [255, 573]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI659N1 : CertifiedPrimeIdeal' SI659N1 659 where
  n := 2
  hpos := by decide
  P := [61, 132, 1]
  hirr := P659P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-173875, -483636, -100156, -20868, 243552]
  a := ![20, 30, 14, 14, -80]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![63007, 23968, -100156, -20868, 243552]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI659N1 : Ideal.IsPrime I659N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI659N1 B_one_repr
lemma NI659N1 : Nat.card (O ⧸ I659N1) = 434281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI659N1
def MulI659N0 : IdealMulLeCertificate' Table 
  ![![65, 658, 146, 24, -270]] ![![7, 34, 2, 0, -6]]
  ![![659, 0, 0, 0, 0]] where
 M := ![![![659, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC659 : ContainsPrimesAboveP 659 ![I659N0, I659N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI659N0
    exact isPrimeI659N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 659 (by decide) (𝕀 ⊙ MulI659N0)
instance hp661 : Fact (Nat.Prime 661) := {out := by norm_num}

def I661N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23393, 81604, -37876, -12382, 31866]] i)))

def SI661N0: IdealEqSpanCertificate' Table ![![23393, 81604, -37876, -12382, 31866]] 
 ![![661, 0, 0, 0, 0], ![0, 661, 0, 0, 0], ![0, 0, 661, 0, 0], ![174, 35, 542, 1, 0], ![296, 283, 429, 0, 1]] where
  M :=![![![23393, 81604, -37876, -12382, 31866], ![-85038, -279427, 118020, 23304, -74106], ![230706, 668604, -301231, 49608, 40554], ![-365562, -705786, 185478, -524467, 716958], ![-108468, -359404, 130744, 33502, -86053]]]
  hmulB := by decide  
  f := ![![![309686561, -8873320, -35038088, -9108542, 29919486]], ![![-94946178, 2710121, 10739844, 2792160, -9168606]], ![![29090070, -883740, -3302995, -857592, 2831598]], ![![100317870, -2916263, -11359796, -2952223, 9709560]], ![![116974384, -3388757, -13243211, -3441938, 11316779]]]
  g := ![![![-10975, -12864, -10586, -12382, 31866], ![26922, 30071, 29166, 23304, -74106], ![-30870, -18978, -67453, 49608, 40554], ![-183552, -280255, -34990, -524467, 716958], ![29552, 34525, 28577, 33502, -86053]]]
  hle1 := by decide   
  hle2 := by decide  


def P661P0 : CertificateIrreducibleZModOfList' 661 3 2 9 [271, 130, 137, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [603, 533, 348], [582, 127, 313], [0, 1]]
 g := ![![[149, 251, 647], [80, 234], [331, 140, 337], [25, 43], [403, 520, 280], [170, 311], [512, 553], [131, 524, 1], []], ![[64, 412, 261, 16], [50, 202], [530, 165, 51, 15], [547, 130], [43, 434, 15, 135], [358, 243], [493, 43], [291, 374, 655, 341], [660, 141]], ![[333, 628, 458, 56], [67, 286], [323, 73, 620, 17], [345, 272], [14, 86, 297, 570], [388, 243], [482, 153], [283, 188, 130, 154], [34, 141]]]
 h' := ![![[603, 533, 348], [481, 481, 359], [195, 521, 211], [587, 225, 75], [513, 199, 543], [273, 331, 542], [291, 331, 473], [193, 267, 253], [0, 0, 1], [0, 1]], ![[582, 127, 313], [496, 417, 139], [608, 547, 551], [389, 205, 573], [267, 634, 64], [634, 361, 264], [356, 513, 94], [114, 520, 118], [330, 563, 127], [603, 533, 348]], ![[0, 1], [367, 424, 163], [4, 254, 560], [441, 231, 13], [479, 489, 54], [55, 630, 516], [300, 478, 94], [301, 535, 290], [332, 98, 533], [582, 127, 313]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 465], []]
 b := ![[], [14, 359, 540], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI661N0 : CertifiedPrimeIdeal' SI661N0 661 where
  n := 3
  hpos := by decide
  P := [271, 130, 137, 1]
  hirr := P661P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![163396622, -113555149, 1300592445, 675225638, -2009321019]
  a := ![43, 64, 40, 51, -159]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![722289194, 824344018, 752385800, 675225638, -2009321019]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI661N0 : Ideal.IsPrime I661N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI661N0 B_one_repr
lemma NI661N0 : Nat.card (O ⧸ I661N0) = 288804781 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI661N0

def I661N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![150546333, -4309489, -17031939, -4427728, 14542900]] i)))

def SI661N1: IdealEqSpanCertificate' Table ![![150546333, -4309489, -17031939, -4427728, 14542900]] 
 ![![661, 0, 0, 0, 0], ![268, 1, 0, 0, 0], ![225, 0, 1, 0, 0], ![474, 0, 0, 1, 0], ![640, 0, 0, 0, 1]] where
  M :=![![![150546333, -4309489, -17031939, -4427728, 14542900], ![-46148132, 1338185, 5224940, 1357946, -4465172], ![14178184, -322410, -1584551, -413688, 1334500], ![-9184278, 437643, 1079859, 277045, -960756], ![20945050, -476435, -2340849, -611136, 1971483]]]
  hmulB := by decide  
  f := ![![![-200735, -719411, 310081, 130430, -294964]], ![![-80340, -287961, 123918, 52242, -117980]], ![![-72547, -259029, 111310, 45914, -104488]], ![![-136176, -491199, 210735, 92467, -205572]], ![![-193478, -693237, 298047, 125506, -283469]]]
  g := ![![![-3133188, -4309489, -17031939, -4427728, 14542900], ![958624, 1338185, 5224940, 1357946, -4465172], ![-303909, -322410, -1584551, -413688, 1334500], ![172653, 437643, 1079859, 277045, -960756], ![-448941, -476435, -2340849, -611136, 1971483]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI661N1 : Nat.card (O ⧸ I661N1) = 661 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI661N1)

lemma isPrimeI661N1 : Ideal.IsPrime I661N1 := prime_ideal_of_norm_prime hp661.out _ NI661N1

def I661N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -9, -1, 0, 2]] i)))

def SI661N2: IdealEqSpanCertificate' Table ![![-5, -9, -1, 0, 2]] 
 ![![661, 0, 0, 0, 0], ![632, 1, 0, 0, 0], ![481, 0, 1, 0, 0], ![124, 0, 0, 1, 0], ![438, 0, 0, 0, 1]] where
  M :=![![![-5, -9, -1, 0, 2], ![-10, -31, -10, -2, 14], ![-58, -174, -29, -4, 50], ![-84, -249, -75, -11, 102], ![-66, -195, -47, -8, 71]]]
  hmulB := by decide  
  f := ![![![-453, -387, -37, -2, 118]], ![![-434, -373, -36, -2, 114]], ![![-335, -297, -30, -2, 92]], ![![-96, -105, -13, -1, 34]], ![![-308, -279, -29, -2, 87]]]
  g := ![![![8, -9, -1, 0, 2], ![28, -31, -10, -2, 14], ![155, -174, -29, -4, 50], ![227, -249, -75, -11, 102], ![175, -195, -47, -8, 71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI661N2 : Nat.card (O ⧸ I661N2) = 661 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI661N2)

lemma isPrimeI661N2 : Ideal.IsPrime I661N2 := prime_ideal_of_norm_prime hp661.out _ NI661N2
def MulI661N0 : IdealMulLeCertificate' Table 
  ![![23393, 81604, -37876, -12382, 31866]] ![![150546333, -4309489, -17031939, -4427728, 14542900]]
  ![![453, 387, 37, 2, -118]] where
 M := ![![![453, 387, 37, 2, -118]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI661N1 : IdealMulLeCertificate' Table 
  ![![453, 387, 37, 2, -118]] ![![-5, -9, -1, 0, 2]]
  ![![661, 0, 0, 0, 0]] where
 M := ![![![-661, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC661 : ContainsPrimesAboveP 661 ![I661N0, I661N1, I661N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI661N0
    exact isPrimeI661N1
    exact isPrimeI661N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 661 (by decide) (𝕀 ⊙ MulI661N0 ⊙ MulI661N1)
instance hp673 : Fact (Nat.Prime 673) := {out := by norm_num}

def I673N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 8772, -5310, -10360, 17078]] i)))

def SI673N0: IdealEqSpanCertificate' Table ![![181, 8772, -5310, -10360, 17078]] 
 ![![673, 0, 0, 0, 0], ![0, 673, 0, 0, 0], ![397, 423, 1, 0, 0], ![634, 368, 0, 1, 0], ![280, 190, 0, 0, 1]] where
  M :=![![![181, 8772, -5310, -10360, 17078], ![-23230, -128593, 65622, 72260, -129094], ![211910, 1004652, -496531, -446836, 830582], ![-841902, -3784392, 1842834, 1514231, -2870286], ![-16904, -104508, 53970, 66368, -116193]]]
  hmulB := by decide  
  f := ![![![-146244807, 4216644, 16552362, 4302416, -14140118]], ![![44886094, -1145017, -5045490, -1314604, 4277158]], ![![-58077071, 1769361, 6595457, 1712344, -5655274]], ![![-113211928, 3348040, 12833190, 3333935, -10981518]], ![![-48202272, 1433510, 5465862, 1419808, -4678977]]]
  g := ![![![5787, 4194, -5310, -10360, 17078], ![-53108, -44503, 65622, 72260, -129094], ![368597, 323421, -496531, -446836, 830582], ![-1320638, -1181554, 1842834, 1514231, -2870286], ![-46042, -37564, 53970, 66368, -116193]]]
  hle1 := by decide   
  hle2 := by decide  


def P673P0 : CertificateIrreducibleZModOfList' 673 2 2 9 [640, 339, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [334, 672], [0, 1]]
 g := ![![[418, 526], [395], [657], [660], [24], [495, 507], [453], [240, 511], [1]], ![[449, 147], [395], [657], [660], [24], [237, 166], [453], [645, 162], [1]]]
 h' := ![![[334, 672], [339, 212], [266, 433], [662, 441], [631, 576], [183, 90], [251, 338], [517, 527], [33, 334], [0, 1]], ![[0, 1], [482, 461], [193, 240], [569, 232], [537, 97], [631, 583], [79, 335], [209, 146], [544, 339], [334, 672]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [617, 359]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI673N0 : CertifiedPrimeIdeal' SI673N0 673 where
  n := 2
  hpos := by decide
  P := [640, 339, 1]
  hirr := P673P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-39793, -108087, -40085, -12320, 75109]
  a := ![13, 18, 11, 13, -53]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3944, 10566, -40085, -12320, 75109]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI673N0 : Ideal.IsPrime I673N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI673N0 B_one_repr
lemma NI673N0 : Nat.card (O ⧸ I673N0) = 452929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI673N0

def I673N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -32, 64, 36, -90]] i)))

def SI673N1: IdealEqSpanCertificate' Table ![![-1, -32, 64, 36, -90]] 
 ![![673, 0, 0, 0, 0], ![0, 673, 0, 0, 0], ![46, 56, 1, 0, 0], ![35, 446, 0, 1, 0], ![458, 413, 0, 0, 1]] where
  M :=![![![-1, -32, 64, 36, -90], ![234, 845, -184, -160, 234], ![-210, -1368, 1621, 912, -2202], ![2874, 10788, -3420, -2483, 4338], ![710, 2264, 140, -108, -257]]]
  hmulB := by decide  
  f := ![![![5219, -1216, -840, -196, 954]], ![![-3594, -5419, -880, -112, 1974]], ![![44, -576, -139, -24, 246]], ![![-2141, -3742, -644, -87, 1392]], ![![1326, -4215, -1124, -204, 1885]]]
  g := ![![![55, 26, 64, 36, -90], ![-138, -21, -184, -160, 234], ![1340, 610, 1621, 912, -2202], ![-2585, -716, -3420, -2483, 4338], ![172, 221, 140, -108, -257]]]
  hle1 := by decide   
  hle2 := by decide  


def P673P1 : CertificateIrreducibleZModOfList' 673 2 2 9 [68, 656, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 672], [0, 1]]
 g := ![![[168, 505], [660], [332], [644], [234], [305, 12], [584], [582, 289], [1]], ![[4, 168], [660], [332], [644], [234], [509, 661], [584], [111, 384], [1]]]
 h' := ![![[17, 672], [332, 337], [662, 97], [612, 393], [563, 308], [123, 193], [331, 52], [131, 250], [605, 17], [0, 1]], ![[0, 1], [4, 336], [292, 576], [563, 280], [415, 365], [39, 480], [542, 621], [343, 423], [221, 656], [17, 672]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [554]]
 b := ![[], [1, 277]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI673N1 : CertifiedPrimeIdeal' SI673N1 673 where
  n := 2
  hpos := by decide
  P := [68, 656, 1]
  hirr := P673P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-157633, -285177, -319100, -183153, 643834]
  a := ![-32, -48, -29, -39, 131]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-407050, -247597, -319100, -183153, 643834]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI673N1 : Ideal.IsPrime I673N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI673N1 B_one_repr
lemma NI673N1 : Nat.card (O ⧸ I673N1) = 452929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI673N1

def I673N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1229390581, -35346676, -139122210, -36163812, 118825196]] i)))

def SI673N2: IdealEqSpanCertificate' Table ![![1229390581, -35346676, -139122210, -36163812, 118825196]] 
 ![![673, 0, 0, 0, 0], ![194, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![314, 0, 0, 1, 0], ![344, 0, 0, 0, 1]] where
  M :=![![![1229390581, -35346676, -139122210, -36163812, 118825196], ![-377143108, 10137341, 42513986, 11066076, -36155116], ![114379124, -6721284, -13745129, -3500636, 12500012], ![-77937684, -4947012, 7141266, 2007733, -4507596], ![168971682, -9923180, -20304174, -5171228, 18463619]]]
  hmulB := by decide  
  f := ![![![14481693, 58428460, -27612146, -17639732, 35601748]], ![![4067278, 16412389, -7756466, -4957228, 10003860]], ![![1646944, 6622444, -3126481, -1977868, 4002596]], ![![5207958, 21101348, -9984226, -6456003, 12986996]], ![![7294546, 29432500, -13909310, -8887308, 17936123]]]
  g := ![![![-21098707, -35346676, -139122210, -36163812, 118825196], ![6549922, 10137341, 42513986, 11066076, -36155116], ![-1586552, -6721284, -13745129, -3500636, 12500012], ![2125738, -4947012, 7141266, 2007733, -4507596], ![-2344478, -9923180, -20304174, -5171228, 18463619]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI673N2 : Nat.card (O ⧸ I673N2) = 673 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI673N2)

lemma isPrimeI673N2 : Ideal.IsPrime I673N2 := prime_ideal_of_norm_prime hp673.out _ NI673N2
def MulI673N0 : IdealMulLeCertificate' Table 
  ![![181, 8772, -5310, -10360, 17078]] ![![-1, -32, 64, 36, -90]]
  ![![-14481693, -58428460, 27612146, 17639732, -35601748]] where
 M := ![![![-14481693, -58428460, 27612146, 17639732, -35601748]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI673N1 : IdealMulLeCertificate' Table 
  ![![-14481693, -58428460, 27612146, 17639732, -35601748]] ![![1229390581, -35346676, -139122210, -36163812, 118825196]]
  ![![673, 0, 0, 0, 0]] where
 M := ![![![-673, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I677N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5491527, 21966684, -10355308, -6449926, 13109242]] i)))

def SI677N0: IdealEqSpanCertificate' Table ![![5491527, 21966684, -10355308, -6449926, 13109242]] 
 ![![677, 0, 0, 0, 0], ![0, 677, 0, 0, 0], ![418, 522, 1, 0, 0], ![367, 460, 0, 1, 0], ![621, 618, 0, 0, 1]] where
  M :=![![![5491527, 21966684, -10355308, -6449926, 13109242], ![-26846654, -106879285, 50310932, 30888792, -63033530], ![129834898, 514590108, -241901105, -146488472, 300096298], ![-375692778, -1483805418, 696760470, 417297019, -857572770], ![-27130076, -108164004, 50938192, 31412070, -64022151]]]
  hmulB := by decide  
  f := ![![![-1823034025, 53701944, 206601592, 53677474, -176744834]], ![![561659326, -8448449, -61761308, -16216608, 51045538]], ![![-692762160, 26708034, 79981023, 20647452, -69816026]], ![![-606425649, 23486894, 70038346, 18078489, -61160300]], ![![-1159870005, 41643606, 133192180, 34447592, -115597441]]]
  g := ![![![-2126597, 432632, -10355308, -6449926, 13109242], ![9971668, -2397797, 50310932, 30888792, -63033530], ![-46313198, 12868762, -241901105, -146488472, 300096298], ![129664867, -40132094, 696760470, 417297019, -857572770], ![10207137, -2336430, 50938192, 31412070, -64022151]]]
  hle1 := by decide   
  hle2 := by decide  


def P677P0 : CertificateIrreducibleZModOfList' 677 2 2 9 [476, 601, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 676], [0, 1]]
 g := ![![[125, 613], [297], [193, 401], [476], [57], [151, 193], [166], [367, 360], [1]], ![[0, 64], [297], [204, 276], [476], [57], [602, 484], [166], [647, 317], [1]]]
 h' := ![![[76, 676], [440, 208], [204, 589], [10, 483], [81, 511], [563, 477], [192, 105], [651, 514], [201, 76], [0, 1]], ![[0, 1], [0, 469], [286, 88], [160, 194], [328, 166], [257, 200], [48, 572], [449, 163], [561, 601], [76, 676]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [563]]
 b := ![[], [135, 620]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI677N0 : CertifiedPrimeIdeal' SI677N0 677 where
  n := 2
  hpos := by decide
  P := [476, 601, 1]
  hirr := P677P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-142487, -264163, -282155, -159440, 566873]
  a := ![-31, -46, -29, -37, 125]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-259550, -191971, -282155, -159440, 566873]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI677N0 : Ideal.IsPrime I677N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI677N0 B_one_repr
lemma NI677N0 : Nat.card (O ⧸ I677N0) = 458329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI677N0

def I677N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-117646, 3595, 13367, 3470, -11453]] i)))

def SI677N1: IdealEqSpanCertificate' Table ![![-117646, 3595, 13367, 3470, -11453]] 
 ![![677, 0, 0, 0, 0], ![0, 677, 0, 0, 0], ![416, 56, 1, 0, 0], ![330, 643, 0, 1, 0], ![521, 180, 0, 0, 1]] where
  M :=![![![-117646, 3595, 13367, 3470, -11453], ![36445, 13, -3858, -1026, 3109], ![-9389, 5262, 2311, 492, -2861], ![10371, 9057, 1155, 97, -2679], ![-14101, 7085, 3259, 702, -3990]]]
  hmulB := by decide  
  f := ![![![-6510, -26867, 12785, 8688, -17249]], ![![34117, 139535, -66210, -43934, 87769]], ![![-1437, -6018, 2877, 2028, -3989]], ![![30014, 122596, -58149, -38451, 76886]], ![![4111, 16628, -7862, -5060, 10191]]]
  g := ![![![-1265, -1351, 13367, 3470, -11453], ![532, 467, -3858, -1026, 3109], ![528, 110, 2311, 492, -2861], ![1320, 538, 1155, 97, -2679], ![705, 135, 3259, 702, -3990]]]
  hle1 := by decide   
  hle2 := by decide  


def P677P1 : CertificateIrreducibleZModOfList' 677 2 2 9 [107, 134, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [543, 676], [0, 1]]
 g := ![![[596, 348], [134], [387, 352], [452], [262], [54, 267], [583], [196, 354], [1]], ![[0, 329], [134], [609, 325], [452], [262], [157, 410], [583], [150, 323], [1]]]
 h' := ![![[543, 676], [237, 411], [565, 459], [107, 276], [106, 287], [315, 212], [128, 415], [15, 113], [570, 543], [0, 1]], ![[0, 1], [0, 266], [666, 218], [358, 401], [237, 390], [341, 465], [32, 262], [444, 564], [247, 134], [543, 676]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [366]]
 b := ![[], [75, 183]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI677N1 : CertifiedPrimeIdeal' SI677N1 677 where
  n := 2
  hpos := by decide
  P := [107, 134, 1]
  hirr := P677P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![851, 2805, -1090, -699, 1776]
  a := ![2, 3, 2, 3, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-355, 286, -1090, -699, 1776]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI677N1 : Ideal.IsPrime I677N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI677N1 B_one_repr
lemma NI677N1 : Nat.card (O ⧸ I677N1) = 458329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI677N1

def I677N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-318163, 9120, 35998, 9358, -30740]] i)))

def SI677N2: IdealEqSpanCertificate' Table ![![-318163, 9120, 35998, 9358, -30740]] 
 ![![677, 0, 0, 0, 0], ![99, 1, 0, 0, 0], ![354, 0, 1, 0, 0], ![579, 0, 0, 1, 0], ![638, 0, 0, 0, 1]] where
  M :=![![![-318163, 9120, 35998, 9358, -30740], ![97552, -2765, -11030, -2868, 9412], ![-29852, 1008, 3413, 884, -2948], ![19644, -246, -2148, -565, 1764], ![-44100, 1488, 5042, 1306, -4355]]]
  hmulB := by decide  
  f := ![![![-1287, -6036, 4226, 2630, -5756]], ![![-169, -809, 592, 366, -808]], ![![-730, -3408, 2369, 1472, -3220]], ![![-837, -4134, 3198, 1973, -4392]], ![![-1174, -5556, 3970, 2462, -5411]]]
  g := ![![![339, 9120, 35998, 9358, -30740], ![-101, -2765, -11030, -2868, 9412], ![46, 1008, 3413, 884, -2948], ![9, -246, -2148, -565, 1764], ![68, 1488, 5042, 1306, -4355]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI677N2 : Nat.card (O ⧸ I677N2) = 677 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI677N2)

lemma isPrimeI677N2 : Ideal.IsPrime I677N2 := prime_ideal_of_norm_prime hp677.out _ NI677N2
def MulI677N0 : IdealMulLeCertificate' Table 
  ![![5491527, 21966684, -10355308, -6449926, 13109242]] ![![-117646, 3595, 13367, 3470, -11453]]
  ![![-4238, -24451, 12897, 14432, -25813]] where
 M := ![![![-4238, -24451, 12897, 14432, -25813]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI677N1 : IdealMulLeCertificate' Table 
  ![![-4238, -24451, 12897, 14432, -25813]] ![![-318163, 9120, 35998, 9358, -30740]]
  ![![677, 0, 0, 0, 0]] where
 M := ![![![-14894, -3385, 3385, 1354, -3385]]]
 hmul := by decide  
 g := ![![![![-22, -5, 5, 2, -5]]]]
 hle2 := by decide  


def PBC677 : ContainsPrimesAboveP 677 ![I677N0, I677N1, I677N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI677N0
    exact isPrimeI677N1
    exact isPrimeI677N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 677 (by decide) (𝕀 ⊙ MulI677N0 ⊙ MulI677N1)
instance hp683 : Fact (Nat.Prime 683) := {out := by norm_num}

def I683N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-271676747932, 7782795217, 30737160725, 7990469672, -26246463839]] i)))

def SI683N0: IdealEqSpanCertificate' Table ![![-271676747932, 7782795217, 30737160725, 7990469672, -26246463839]] 
 ![![683, 0, 0, 0, 0], ![0, 683, 0, 0, 0], ![0, 0, 683, 0, 0], ![195, 132, 435, 1, 0], ![509, 560, 194, 0, 1]] where
  M :=![![![-271676747932, 7782795217, 30737160725, 7990469672, -26246463839], ![83289501163, -2386945073, -9422862090, -2449435926, 8046025255], ![-25533510719, 736096182, 2886808393, 749763228, -2464285439], ![16678179273, -490882623, -1881241593, -487126133, 1604302419], ![-37722056773, 1079590199, 4268281489, 1109749620, -3644864970]]]
  hmulB := by decide  
  f := ![![![336485015174551284, 1003545926220320641, 226193541329842085, 36264295586121834, -344652677047179677]], ![![1505677611719167381, 4490591156512790579, 1012153694033431722, 162272717970709498, -1542225645263333723]], ![![6737491918492411627, 20094156538406120298, 4529108542721965313, 726125644301187460, -6901034285546308109]], ![![4695283265112566112, 14003394447475918032, 3156285425464255641, 506028894327687523, -4809254123772516531]], ![![3411334053124983075, 10174094647912717168, 2293183040365543560, 367652706261980724, -3494138997844598881]]]
  g := ![![![16880866413, 19986911491, 2410976337, 7990469672, -26246463839], ![-5174959514, -6127138427, -739161250, -2449435926, 8046025255], ![1585042384, 1876672322, 226663513, 749763228, -2464285439], ![-1032096861, -1221961329, -148193328, -487126133, 1604302419], ![2344235779, 2775573973, 334745243, 1109749620, -3644864970]]]
  hle1 := by decide   
  hle2 := by decide  


def P683P0 : CertificateIrreducibleZModOfList' 683 3 2 9 [163, 631, 506, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [506, 596, 664], [354, 86, 19], [0, 1]]
 g := ![![[550, 38, 101], [356, 62, 633], [415, 553], [359, 68, 228], [478, 248], [270, 523, 642], [135, 228], [646, 177, 1], []], ![[608, 58, 666, 600], [57, 292, 574, 331], [551, 659], [174, 309, 152, 583], [212, 289], [39, 128, 84, 23], [546, 548], [578, 220, 376, 174], [269, 361]], ![[307, 327, 284, 4], [284, 270, 213, 303], [610, 266], [7, 382, 535, 451], [481, 42], [292, 171, 0, 360], [312, 300], [393, 209, 99, 381], [231, 361]]]
 h' := ![![[506, 596, 664], [27, 160, 655], [320, 31, 320], [221, 149, 223], [645, 175, 443], [385, 126, 115], [330, 309, 143], [567, 643, 443], [0, 0, 1], [0, 1]], ![[354, 86, 19], [518, 611, 16], [332, 33, 294], [392, 273, 638], [208, 144, 623], [133, 72, 666], [346, 355, 280], [620, 408, 610], [459, 286, 86], [506, 596, 664]], ![[0, 1], [116, 595, 12], [350, 619, 69], [399, 261, 505], [454, 364, 300], [76, 485, 585], [463, 19, 260], [79, 315, 313], [239, 397, 596], [354, 86, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 306], []]
 b := ![[], [524, 196, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI683N0 : CertifiedPrimeIdeal' SI683N0 683 where
  n := 3
  hpos := by decide
  P := [163, 631, 506, 1]
  hirr := P683P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![68491332718, 168743748391, 95549916869, 37329299442, -168868112793]
  a := ![170, 256, 148, 191, -673]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![115290113255, 131489633069, 24330481027, 37329299442, -168868112793]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI683N0 : Ideal.IsPrime I683N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI683N0 B_one_repr
lemma NI683N0 : Nat.card (O ⧸ I683N0) = 318611987 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI683N0

def I683N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2332430, -9125558, 4272454, 2481764, -5145421]] i)))

def SI683N1: IdealEqSpanCertificate' Table ![![-2332430, -9125558, 4272454, 2481764, -5145421]] 
 ![![683, 0, 0, 0, 0], ![0, 683, 0, 0, 0], ![137, 497, 1, 0, 0], ![37, 280, 0, 1, 0], ![497, 169, 0, 0, 1]] where
  M :=![![![-2332430, -9125558, 4272454, 2481764, -5145421], ![10836521, 42222167, -19743688, -11309204, 23544389], ![-49866721, -193457700, 90333703, 50986256, -106610173], ![138500025, 535323462, -249687618, -139104449, 292004553], ![11122413, 43394522, -20303944, -11681248, 24288644]]]
  hmulB := by decide  
  f := ![![![252490204446, -7232691818, -28566442980, -7426203680, 24392863097]], ![![-77407093405, 2218817305, 8758087282, 2276743480, -7478846641]], ![![-5646315726, 162812069, 639067547, 166111028, -545936485]], ![![-18078106805, 518474440, 2045480204, 531735083, -1746771088]], ![![164627956322, -4715463545, -18625724404, -4841997636, 15904408086]]]
  g := ![![![2749327, -2866549, 4272454, 2481764, -5145421], ![-12543776, 13239254, -19743688, -11309204, 23544389], ![56622519, -60539298, 90333703, 50986256, -106610173], ![-154661339, 167248237, -249687618, -139104449, 292004553], ![-12952397, 13617018, -20303944, -11681248, 24288644]]]
  hle1 := by decide   
  hle2 := by decide  


def P683P1 : CertificateIrreducibleZModOfList' 683 2 2 9 [77, 425, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [258, 682], [0, 1]]
 g := ![![[41, 479], [658, 241], [109], [413, 631], [662], [569, 349], [594], [42, 313], [1]], ![[0, 204], [0, 442], [109], [657, 52], [662], [455, 334], [594], [202, 370], [1]]]
 h' := ![![[258, 682], [559, 567], [330, 507], [300, 415], [207, 398], [582, 404], [0, 132], [181, 177], [606, 258], [0, 1]], ![[0, 1], [0, 116], [0, 176], [139, 268], [441, 285], [315, 279], [589, 551], [86, 506], [236, 425], [258, 682]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [409]]
 b := ![[], [598, 546]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI683N1 : CertifiedPrimeIdeal' SI683N1 683 where
  n := 2
  hpos := by decide
  P := [77, 425, 1]
  hirr := P683P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-218688, -475896, -390032, -180464, 707717]
  a := ![39, 60, 34, 44, -155]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-427295, 181985, -390032, -180464, 707717]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI683N1 : Ideal.IsPrime I683N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI683N1 B_one_repr
lemma NI683N1 : Nat.card (O ⧸ I683N1) = 466489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI683N1
def MulI683N0 : IdealMulLeCertificate' Table 
  ![![-271676747932, 7782795217, 30737160725, 7990469672, -26246463839]] ![![-2332430, -9125558, 4272454, 2481764, -5145421]]
  ![![683, 0, 0, 0, 0]] where
 M := ![![![241507840385, 1116832343301, -548063831029, -473764373372, 888084423660]]]
 hmul := by decide  
 g := ![![![![353598595, 1635186447, -802436063, -693652084, 1300270020]]]]
 hle2 := by decide  


def PBC683 : ContainsPrimesAboveP 683 ![I683N0, I683N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI683N0
    exact isPrimeI683N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 683 (by decide) (𝕀 ⊙ MulI683N0)
instance hp691 : Fact (Nat.Prime 691) := {out := by norm_num}

def I691N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-343090, 7746, 38274, 9996, -32369]] i)))

def SI691N0: IdealEqSpanCertificate' Table ![![-343090, 7746, 38274, 9996, -32369]] 
 ![![691, 0, 0, 0, 0], ![0, 691, 0, 0, 0], ![0, 0, 691, 0, 0], ![0, 0, 0, 691, 0], ![419, 494, 316, 630, 1]] where
  M :=![![![-343090, 7746, 38274, 9996, -32369], ![101869, -12257, -13956, -3420, 13321], ![-46085, -40524, -5693, -552, 11167], ![-3219, -72882, -18606, -3209, 26877], ![-64963, -50574, -6300, -472, 13284]]]
  hmulB := by decide  
  f := ![![![-54, -210, 96, 56, -115]], ![![239, 937, -450, -256, 539]], ![![-1159, -4464, 2023, 1148, -2371]], ![![3063, 11898, -5676, -3143, 6663]], ![![2401, 9350, -4514, -2490, 5307]]]
  g := ![![![19131, 23152, 14858, 29526, -32369], ![-7930, -9541, -6112, -12150, 13321], ![-6838, -8042, -5115, -10182, 11167], ![-16302, -19320, -12318, -24509, 26877], ![-8149, -9570, -6084, -12112, 13284]]]
  hle1 := by decide   
  hle2 := by decide  


def P691P0 : CertificateIrreducibleZModOfList' 691 4 2 9 [77, 364, 12, 268, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 566, 335, 481], [648, 595, 614, 120], [418, 220, 433, 90], [0, 1]]
 g := ![![[475, 211, 238, 400], [418, 339, 459, 218], [176, 349, 502], [255, 234, 589], [214, 119, 453, 181], [405, 652, 105, 159], [446, 18, 631], [423, 1], []], ![[49, 60, 279, 9, 289, 319], [436, 596, 109, 483, 551, 70], [274, 48, 263], [580, 508, 305], [281, 590, 639, 144, 177, 118], [459, 370, 447, 466, 588, 481], [524, 157, 624], [338, 15, 666, 273, 599, 457], [226, 328, 567]], ![[81, 20, 317, 448, 482, 96], [213, 594, 15, 614, 124, 582], [385, 282, 235], [318, 516, 614], [392, 281, 513, 578, 262, 169], [660, 259, 344, 567, 568, 69], [10, 233, 638], [662, 326, 590, 669, 221, 6], [651, 212, 580]], ![[600, 169, 323, 238, 122, 571], [382, 549, 326, 5, 655, 58], [639, 536, 679], [139, 99, 355], [404, 17, 327, 496, 603, 95], [389, 574, 127, 399, 296, 84], [288, 36, 343], [54, 122, 170, 425, 420, 450], [379, 179, 499]]]
 h' := ![![[48, 566, 335, 481], [291, 232, 389, 671], [661, 535, 451, 40], [584, 580, 169, 442], [106, 506, 212, 513], [601, 268, 604, 80], [61, 57, 220, 463], [597, 44, 88, 639], [0, 0, 1], [0, 1]], ![[648, 595, 614, 120], [297, 157, 623, 397], [212, 509, 689, 169], [571, 232, 39, 355], [130, 570, 121, 357], [6, 438, 180, 674], [347, 299, 92, 690], [459, 9, 65, 283], [104, 23, 183, 411], [48, 566, 335, 481]], ![[418, 220, 433, 90], [612, 189, 265, 652], [339, 149, 518, 478], [292, 475, 577, 262], [325, 241, 328, 180], [117, 82, 7, 278], [474, 647, 547, 648], [365, 127, 327, 527], [92, 273, 213, 528], [648, 595, 614, 120]], ![[0, 1], [16, 113, 105, 353], [440, 189, 415, 4], [435, 95, 597, 323], [321, 65, 30, 332], [146, 594, 591, 350], [242, 379, 523, 272], [416, 511, 211, 624], [431, 395, 294, 443], [418, 220, 433, 90]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [384, 269, 537], []]
 b := ![[], [], [318, 492, 381, 151], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI691N0 : CertifiedPrimeIdeal' SI691N0 691 where
  n := 4
  hpos := by decide
  P := [77, 364, 12, 268, 1]
  hirr := P691P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13634103736798, -38130213373461, -10302525316751, -2540569182817, 19853371189636]
  a := ![-50, -75, -43, -53, 203]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12058171681902, -14248474068095, -9094020001797, -18104434759267, 19853371189636]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI691N0 : Ideal.IsPrime I691N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI691N0 B_one_repr
lemma NI691N0 : Nat.card (O ⧸ I691N0) = 227988105361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI691N0

def I691N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![54, 210, -96, -56, 115]] i)))

def SI691N1: IdealEqSpanCertificate' Table ![![54, 210, -96, -56, 115]] 
 ![![691, 0, 0, 0, 0], ![75, 1, 0, 0, 0], ![594, 0, 1, 0, 0], ![231, 0, 0, 1, 0], ![568, 0, 0, 0, 1]] where
  M :=![![![54, 210, -96, -56, 115], ![-239, -937, 450, 256, -539], ![1159, 4464, -2023, -1148, 2371], ![-3063, -11898, 5676, 3143, -6663], ![-205, -846, 486, 268, -602]]]
  hmulB := by decide  
  f := ![![![343090, -7746, -38274, -9996, 32369]], ![![37091, -823, -4134, -1080, 3494]], ![![294995, -6600, -32893, -8592, 27809]], ![![114699, -2484, -12768, -3337, 10782]], ![![282113, -6294, -31452, -8216, 26588]]]
  g := ![![![-16, 210, -96, -56, 115], ![72, -937, 450, 256, -539], ![-309, 4464, -2023, -1148, 2371], ![834, -11898, 5676, 3143, -6663], ![79, -846, 486, 268, -602]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI691N1 : Nat.card (O ⧸ I691N1) = 691 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI691N1)

lemma isPrimeI691N1 : Ideal.IsPrime I691N1 := prime_ideal_of_norm_prime hp691.out _ NI691N1
def MulI691N0 : IdealMulLeCertificate' Table 
  ![![-343090, 7746, 38274, 9996, -32369]] ![![54, 210, -96, -56, 115]]
  ![![691, 0, 0, 0, 0]] where
 M := ![![![-691, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC691 : ContainsPrimesAboveP 691 ![I691N0, I691N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI691N0
    exact isPrimeI691N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 691 (by decide) (𝕀 ⊙ MulI691N0)
instance hp701 : Fact (Nat.Prime 701) := {out := by norm_num}

def I701N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![701, 0, 0, 0, 0]] i)))

def SI701N0: IdealEqSpanCertificate' Table ![![701, 0, 0, 0, 0]] 
 ![![701, 0, 0, 0, 0], ![0, 701, 0, 0, 0], ![0, 0, 701, 0, 0], ![0, 0, 0, 701, 0], ![0, 0, 0, 0, 701]] where
  M :=![![![701, 0, 0, 0, 0], ![0, 701, 0, 0, 0], ![0, 0, 701, 0, 0], ![0, 0, 0, 701, 0], ![0, 0, 0, 0, 701]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P701P0 : CertificateIrreducibleZModOfList' 701 5 2 9 [267, 352, 559, 195, 183, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [203, 539, 247, 59, 489], [94, 498, 497, 516, 320], [306, 662, 522, 404, 677], [616, 403, 136, 423, 617], [0, 1]]
 g := ![![[57, 225, 83, 423, 455], [353, 235, 141, 543], [634, 596, 11, 536, 369], [92, 613, 682, 28, 120], [574, 188, 103, 43, 564], [618, 592, 490, 211, 214], [258, 601, 224, 542], [1], []], ![[505, 27, 660, 78, 120, 262, 473, 477], [607, 140, 58, 13], [428, 687, 698, 153, 689, 550, 197, 228], [414, 38, 493, 102, 407, 579, 341, 596], [415, 206, 138, 242, 319, 148, 351, 588], [535, 646, 677, 278, 140, 35, 485, 275], [273, 699, 72, 279], [240, 318, 55, 327, 381, 161, 163, 360], [234, 516, 301, 80]], ![[584, 447, 66, 114, 468, 689, 505, 485], [74, 645, 276, 103], [665, 566, 599, 635, 127, 557, 625, 22], [332, 336, 22, 135, 670, 273, 161, 591], [6, 328, 559, 187, 571, 525, 644, 68], [487, 183, 516, 409, 350, 68, 13, 538], [398, 317, 364, 261], [592, 513, 172, 223, 47, 378, 430, 314], [339, 205, 1, 54]], ![[462, 678, 3, 332, 234, 175, 188, 88], [285, 495, 208, 560], [163, 685, 56, 132, 398, 272, 215, 337], [549, 605, 251, 654, 509, 96, 542, 223], [311, 624, 128, 468, 552, 337, 557, 256], [277, 27, 666, 495, 621, 1, 163, 468], [33, 572, 654, 652], [534, 130, 205, 652, 242, 93, 273, 293], [322, 424, 679, 576]], ![[657, 66, 89, 444, 667, 63, 102, 152], [226, 193, 621, 518], [76, 663, 624, 517, 685, 454, 627, 264], [657, 336, 594, 428, 692, 446, 262, 624], [289, 366, 16, 372, 307, 58, 84, 241], [539, 549, 134, 49, 632, 52, 228, 66], [374, 593, 458, 676], [288, 120, 664, 436, 498, 441, 423, 413], [389, 58, 432, 46]]]
 h' := ![![[203, 539, 247, 59, 489], [391, 566, 10, 406, 34], [364, 586, 61, 696, 564], [672, 349, 223, 42, 151], [261, 653, 128, 580, 558], [430, 408, 494, 24, 238], [300, 476, 519, 696, 479], [434, 349, 142, 506, 518], [0, 0, 1], [0, 1]], ![[94, 498, 497, 516, 320], [388, 256, 109, 497, 148], [351, 342, 515, 537, 46], [506, 678, 218, 565, 608], [397, 635, 595, 631, 605], [697, 548, 546, 484, 540], [401, 372, 687, 88, 650], [33, 179, 429, 444, 41], [462, 96, 101, 579, 108], [203, 539, 247, 59, 489]], ![[306, 662, 522, 404, 677], [508, 556, 20, 526, 217], [210, 208, 321, 459, 605], [628, 180, 213, 561, 485], [466, 398, 360, 14, 225], [247, 383, 35, 141, 374], [258, 160, 318, 249, 434], [561, 386, 533, 105, 573], [340, 176, 299, 485, 629], [94, 498, 497, 516, 320]], ![[616, 403, 136, 423, 617], [347, 544, 522, 371, 246], [88, 396, 554, 571, 58], [604, 104, 437, 43, 525], [115, 651, 510, 442, 233], [127, 112, 674, 29, 428], [424, 204, 689, 267, 373], [484, 506, 64, 197, 244], [652, 538, 417, 420, 75], [306, 662, 522, 404, 677]], ![[0, 1], [220, 181, 40, 303, 56], [153, 571, 652, 541, 129], [114, 91, 311, 191, 334], [325, 467, 510, 436, 482], [689, 652, 354, 23, 523], [518, 190, 591, 102, 167], [527, 683, 234, 150, 26], [100, 592, 584, 619, 590], [616, 403, 136, 423, 617]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124, 319, 654, 21], [], [], []]
 b := ![[], [310, 229, 590, 515, 301], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI701N0 : CertifiedPrimeIdeal' SI701N0 701 where
  n := 5
  hpos := by decide
  P := [267, 352, 559, 195, 183, 1]
  hirr := P701P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![294577734686173351, 735381749570594134, 443959686652452462, 159117589476168280, -728019945784611322]
  a := ![94, 142, 87, 113, -373]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![420225013817651, 1049046718360334, 633323376109062, 226986575572280, -1038544858465922]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI701N0 : Ideal.IsPrime I701N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI701N0 B_one_repr
lemma NI701N0 : Nat.card (O ⧸ I701N0) = 169273934903501 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI701N0

def PBC701 : ContainsPrimesAboveP 701 ![I701N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI701N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![701, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 701 (by decide) 𝕀



lemma PB1321I13_primes (p : ℕ) :
  p ∈ Set.range ![647, 653, 659, 661, 673, 677, 683, 691, 701] ↔ Nat.Prime p ∧ 643 < p ∧ p ≤ 701 := by
  rw [← List.mem_ofFn']
  convert primes_range 643 701 (by omega)

def PB1321I13 : PrimesBelowBoundCertificateInterval O 643 701 1321 where
  m := 9
  g := ![2, 3, 2, 3, 3, 3, 2, 2, 1]
  P := ![647, 653, 659, 661, 673, 677, 683, 691, 701]
  hP := PB1321I13_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I647N0, I647N1]
    · exact ![I653N0, I653N1, I653N2]
    · exact ![I659N0, I659N1]
    · exact ![I661N0, I661N1, I661N2]
    · exact ![I673N0, I673N1, I673N2]
    · exact ![I677N0, I677N1, I677N2]
    · exact ![I683N0, I683N1]
    · exact ![I691N0, I691N1]
    · exact ![I701N0]
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
    · exact ![426409, 426409, 653]
    · exact ![286191179, 434281]
    · exact ![288804781, 661, 661]
    · exact ![452929, 452929, 673]
    · exact ![458329, 458329, 677]
    · exact ![318611987, 466489]
    · exact ![227988105361, 691]
    · exact ![169273934903501]
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
    · dsimp ; intro j
      fin_cases j
      exact NI659N0
      exact NI659N1
    · dsimp ; intro j
      fin_cases j
      exact NI661N0
      exact NI661N1
      exact NI661N2
    · dsimp ; intro j
      fin_cases j
      exact NI673N0
      exact NI673N1
      exact NI673N2
    · dsimp ; intro j
      fin_cases j
      exact NI677N0
      exact NI677N1
      exact NI677N2
    · dsimp ; intro j
      fin_cases j
      exact NI683N0
      exact NI683N1
    · dsimp ; intro j
      fin_cases j
      exact NI691N0
      exact NI691N1
    · dsimp ; intro j
      fin_cases j
      exact NI701N0
  β := ![I653N2, I661N1, I661N2, I673N2, I677N2, I691N1]
  Il := ![[], [I653N2], [], [I661N1, I661N2], [I673N2], [I677N2], [], [I691N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
