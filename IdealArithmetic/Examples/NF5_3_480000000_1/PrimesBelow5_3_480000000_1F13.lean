
import IdealArithmetic.Examples.NF5_3_480000000_1.RI5_3_480000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp647 : Fact (Nat.Prime 647) := {out := by norm_num}

def I647N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-193, -139, -36, -49, 45]] i)))

def SI647N0: IdealEqSpanCertificate' Table ![![-193, -139, -36, -49, 45]] 
 ![![647, 0, 0, 0, 0], ![0, 647, 0, 0, 0], ![340, 205, 1, 0, 0], ![176, 524, 0, 1, 0], ![560, 142, 0, 0, 1]] where
  M :=![![![-193, -139, -36, -49, 45], ![360, 45, -180, 292, -102], ![-408, -311, -247, -683, 387], ![1368, 959, 462, 1303, -780], ![-1776, -997, -300, -1870, 1007]]]
  hmulB := by decide  
  f := ![![![745, -1255, 1122, -433, -927]], ![![-7416, -2335, -1644, -3812, -2226]], ![![-1972, -1412, 71, -1447, -1203]], ![![-5840, -2257, -1026, -3231, -2076]], ![![-1064, -1655, 612, -1270, -1339]]]
  g := ![![![-7, 41, -36, -49, 45], ![104, -157, -180, 292, -102], ![-20, 546, -247, -683, 387], ![80, -1029, 462, 1303, -780], ![-208, 1387, -300, -1870, 1007]]]
  hle1 := by decide   
  hle2 := by decide  


def P647P0 : CertificateIrreducibleZModOfList' 647 2 2 9 [431, 357, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [290, 646], [0, 1]]
 g := ![![[223, 544], [258, 437], [421, 406], [498], [351], [557], [364], [97, 637], [1]], ![[115, 103], [176, 210], [407, 241], [498], [351], [557], [364], [432, 10], [1]]]
 h' := ![![[290, 646], [86, 269], [356, 55], [378, 188], [184, 241], [300, 550], [376, 223], [248, 162], [216, 290], [0, 1]], ![[0, 1], [456, 378], [131, 592], [550, 459], [198, 406], [638, 97], [346, 424], [644, 485], [206, 357], [290, 646]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100]]
 b := ![[], [514, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI647N0 : CertifiedPrimeIdeal' SI647N0 647 where
  n := 2
  hpos := by decide
  P := [431, 357, 1]
  hirr := P647P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1831, 1422, 141, 689, -508]
  a := ![0, 1, 1, 0, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![181, -489, 141, 689, -508]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI647N0 : Ideal.IsPrime I647N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI647N0 B_one_repr
lemma NI647N0 : Nat.card (O ⧸ I647N0) = 418609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI647N0

def I647N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 13, -40, -12, 6]] i)))

def SI647N1: IdealEqSpanCertificate' Table ![![47, 13, -40, -12, 6]] 
 ![![647, 0, 0, 0, 0], ![0, 647, 0, 0, 0], ![547, 362, 1, 0, 0], ![615, 571, 0, 1, 0], ![32, 646, 0, 0, 1]] where
  M :=![![![47, 13, -40, -12, 6], ![48, 49, 50, -26, -30], ![-120, -13, 75, -42, -54], ![-240, -161, 4, -80, -75], ![-344, -223, 14, -209, -176]]]
  hmulB := by decide  
  f := ![![![2713, 1603, 514, 2768, -1518]], ![![-12144, -7131, -2330, -12366, 6786]], ![![-4459, -2610, -861, -4536, 2490]], ![![-8223, -4819, -1584, -8368, 4593]], ![![-11872, -6971, -2278, -12089, 6634]]]
  g := ![![![45, 27, -40, -12, 6], ![-16, 25, 50, -26, -30], ![-21, 49, 75, -42, -54], ![76, 143, 4, -80, -75], ![195, 352, 14, -209, -176]]]
  hle1 := by decide   
  hle2 := by decide  


def P647P1 : CertificateIrreducibleZModOfList' 647 2 2 9 [32, 402, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [245, 646], [0, 1]]
 g := ![![[53, 182], [562, 172], [586, 230], [469], [100], [400], [495], [310, 501], [1]], ![[0, 465], [0, 475], [0, 417], [469], [100], [400], [495], [125, 146], [1]]]
 h' := ![![[245, 646], [132, 319], [11, 404], [639, 412], [267, 475], [69, 637], [623, 20], [432, 124], [615, 245], [0, 1]], ![[0, 1], [0, 328], [0, 243], [0, 235], [182, 172], [207, 10], [347, 627], [403, 523], [469, 402], [245, 646]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [477]]
 b := ![[], [384, 562]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI647N1 : CertifiedPrimeIdeal' SI647N1 647 where
  n := 2
  hpos := by decide
  P := [32, 402, 1]
  hirr := P647P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![136911, 99230, -17532, 72050, 141054]
  a := ![3, -2, 0, -3, -61]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-60429, -194460, -17532, 72050, 141054]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI647N1 : Ideal.IsPrime I647N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI647N1 B_one_repr
lemma NI647N1 : Nat.card (O ⧸ I647N1) = 418609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI647N1

def I647N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-97, 36, -64, -13, 21]] i)))

def SI647N2: IdealEqSpanCertificate' Table ![![-97, 36, -64, -13, 21]] 
 ![![647, 0, 0, 0, 0], ![160, 1, 0, 0, 0], ![140, 0, 1, 0, 0], ![366, 0, 0, 1, 0], ![590, 0, 0, 0, 1]] where
  M :=![![![-97, 36, -64, -13, 21], ![168, -43, 98, 32, -18], ![-72, 72, -75, 19, 39], ![72, 36, 4, 36, 57], ![184, 154, -16, 159, 94]]]
  hmulB := by decide  
  f := ![![![-15143, -10998, -1496, 1957, 711]], ![![-3736, -2743, -410, 484, 186]], ![![-3236, -2370, -347, 419, 159]], ![![-8550, -6186, -812, 1104, 393]], ![![-13798, -10016, -1356, 1783, 646]]]
  g := ![![![-7, 36, -64, -13, 21], ![-12, -43, 98, 32, -18], ![-48, 72, -75, 19, 39], ![-82, 36, 4, 36, 57], ![-210, 154, -16, 159, 94]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI647N2 : Nat.card (O ⧸ I647N2) = 647 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI647N2)

lemma isPrimeI647N2 : Ideal.IsPrime I647N2 := prime_ideal_of_norm_prime hp647.out _ NI647N2
def MulI647N0 : IdealMulLeCertificate' Table 
  ![![-193, -139, -36, -49, 45]] ![![47, 13, -40, -12, 6]]
  ![![-15143, -10998, -1496, 1957, 711]] where
 M := ![![![-15143, -10998, -1496, 1957, 711]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI647N1 : IdealMulLeCertificate' Table 
  ![![-15143, -10998, -1496, 1957, 711]] ![![-97, 36, -64, -13, 21]]
  ![![647, 0, 0, 0, 0]] where
 M := ![![![647, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC647 : ContainsPrimesAboveP 647 ![I647N0, I647N1, I647N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI647N0
    exact isPrimeI647N1
    exact isPrimeI647N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 647 (by decide) (𝕀 ⊙ MulI647N0 ⊙ MulI647N1)
instance hp653 : Fact (Nat.Prime 653) := {out := by norm_num}

def I653N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13531, 4393, -8550, -2215, 2615]] i)))

def SI653N0: IdealEqSpanCertificate' Table ![![-13531, 4393, -8550, -2215, 2615]] 
 ![![653, 0, 0, 0, 0], ![0, 653, 0, 0, 0], ![0, 0, 653, 0, 0], ![534, 269, 315, 1, 0], ![354, 258, 522, 0, 1]] where
  M :=![![![-13531, 4393, -8550, -2215, 2615], ![20920, -6791, 13216, 3420, -4030], ![-16120, 5283, -10211, -2599, 3115], ![2000, -683, 1274, 281, -326], ![-3976, 1485, -2620, -504, 797]]]
  hmulB := by decide  
  f := ![![![409, 207, -84, -49, 13]], ![![104, 439, 512, -28, -134]], ![![-536, -13, 467, 57, -109]], ![![118, 343, 367, -24, -97]], ![![-166, 275, 530, 8, -133]]]
  g := ![![![373, -114, -1035, -2215, 2615], ![-580, 173, 1592, 3420, -4030], ![412, -152, -1252, -2599, 3115], ![-50, 12, 127, 281, -326], ![-26, -105, -398, -504, 797]]]
  hle1 := by decide   
  hle2 := by decide  


def P653P0 : CertificateIrreducibleZModOfList' 653 3 2 9 [214, 630, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 384, 214], [485, 268, 439], [0, 1]]
 g := ![![[317, 433, 553], [270, 82], [608, 245, 396], [94, 609, 135], [573, 572], [561, 516], [460, 307], [370, 559, 1], []], ![[203, 273, 627, 512], [246, 406], [310, 188, 92, 170], [27, 256, 70, 336], [413, 279], [348, 548], [430, 294], [377, 208, 279, 22], [201, 86]], ![[501, 627, 264, 416], [391, 386], [166, 512, 186, 93], [409, 168, 152, 50], [153, 230], [52, 438], [197, 625], [102, 111, 222, 641], [629, 86]]]
 h' := ![![[74, 384, 214], [136, 492, 184], [488, 538, 465], [127, 564, 116], [380, 534, 106], [174, 595, 618], [626, 529, 363], [486, 547, 65], [0, 0, 1], [0, 1]], ![[485, 268, 439], [418, 52, 492], [640, 591, 101], [520, 205, 288], [417, 256, 330], [447, 269, 410], [449, 623, 224], [116, 645, 613], [336, 606, 268], [74, 384, 214]], ![[0, 1], [451, 109, 630], [603, 177, 87], [142, 537, 249], [294, 516, 217], [87, 442, 278], [357, 154, 66], [450, 114, 628], [57, 47, 384], [485, 268, 439]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 636], []]
 b := ![[], [85, 314, 589], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI653N0 : CertifiedPrimeIdeal' SI653N0 653 where
  n := 3
  hpos := by decide
  P := [214, 630, 94, 1]
  hirr := P653P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-461973, -317373, 13501, -325609, -302448]
  a := ![1, 0, 1, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![429525, 253144, 398864, -325609, -302448]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI653N0 : Ideal.IsPrime I653N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI653N0 B_one_repr
lemma NI653N0 : Nat.card (O ⧸ I653N0) = 278445077 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI653N0

def I653N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-409, -207, 84, 49, -13]] i)))

def SI653N1: IdealEqSpanCertificate' Table ![![-409, -207, 84, 49, -13]] 
 ![![653, 0, 0, 0, 0], ![0, 653, 0, 0, 0], ![44, 338, 1, 0, 0], ![147, 380, 0, 1, 0], ![468, 317, 0, 0, 1]] where
  M :=![![![-409, -207, 84, 49, -13], ![-104, -439, -512, 28, 134], ![536, 13, -467, -57, 109], ![488, 555, 326, -71, -98], ![224, 179, 44, -40, -19]]]
  hmulB := by decide  
  f := ![![![13531, -4393, 8550, 2215, -2615]], ![![-20920, 6791, -13216, -3420, 4030]], ![![-9892, 3211, -6249, -1617, 1905]], ![![-9131, 2964, -5768, -1492, 1757]], ![![-452, 146, -284, -72, 81]]]
  g := ![![![-8, -66, 84, 49, -13], ![-68, 183, -512, 28, 134], ![-33, 222, -467, -57, 109], ![65, -79, 326, -71, -98], ![20, 10, 44, -40, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P653P1 : CertificateIrreducibleZModOfList' 653 2 2 9 [583, 373, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [280, 652], [0, 1]]
 g := ![![[4, 625], [374], [21, 355], [509, 76], [634], [371], [448], [119, 40], [1]], ![[0, 28], [374], [165, 298], [240, 577], [634], [371], [448], [218, 613], [1]]]
 h' := ![![[280, 652], [183, 25], [164, 292], [368, 148], [300, 626], [18, 274], [483, 32], [494, 534], [70, 280], [0, 1]], ![[0, 1], [0, 628], [299, 361], [16, 505], [576, 27], [337, 379], [301, 621], [477, 119], [110, 373], [280, 652]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [302]]
 b := ![[], [409, 151]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI653N1 : CertifiedPrimeIdeal' SI653N1 653 where
  n := 2
  hpos := by decide
  P := [583, 373, 1]
  hirr := P653P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12845, 8742, -5363, -71, 42572]
  a := ![1, -4, -2, -5, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-30114, -17836, -5363, -71, 42572]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI653N1 : Ideal.IsPrime I653N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI653N1 B_one_repr
lemma NI653N1 : Nat.card (O ⧸ I653N1) = 426409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI653N1
def MulI653N0 : IdealMulLeCertificate' Table 
  ![![-13531, 4393, -8550, -2215, 2615]] ![![-409, -207, 84, 49, -13]]
  ![![653, 0, 0, 0, 0]] where
 M := ![![![-653, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC653 : ContainsPrimesAboveP 653 ![I653N0, I653N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI653N0
    exact isPrimeI653N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 653 (by decide) (𝕀 ⊙ MulI653N0)
instance hp659 : Fact (Nat.Prime 659) := {out := by norm_num}

def I659N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![205, -77, 126, 37, -39]] i)))

def SI659N0: IdealEqSpanCertificate' Table ![![205, -77, 126, 37, -39]] 
 ![![659, 0, 0, 0, 0], ![0, 659, 0, 0, 0], ![0, 0, 659, 0, 0], ![213, 404, 207, 1, 0], ![332, 98, 548, 0, 1]] where
  M :=![![![205, -77, 126, 37, -39], ![-312, 99, -228, -58, 72], ![288, -61, 157, 53, -51], ![-48, 19, 0, -19, 18], ![120, 19, 54, 58, -17]]]
  hmulB := by decide  
  f := ![![![-1, 7, 12, 1, -3]], ![![-24, -5, 12, 2, 0]], ![![0, -7, -7, 11, 3]], ![![-15, -3, 9, 5, 0]], ![![-4, -3, 2, 10, 1]]]
  g := ![![![8, -17, 21, 37, -39], ![-18, 25, -42, -58, 72], ![9, -25, 26, 53, -51], ![-3, 9, -9, -19, 18], ![-10, -33, -4, 58, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P659P0 : CertificateIrreducibleZModOfList' 659 3 2 9 [43, 647, 269, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [282, 40, 473], [108, 618, 186], [0, 1]]
 g := ![![[208, 471, 44], [567, 294, 368], [17, 596], [388, 236], [555, 196, 509], [149, 217], [501, 432], [542, 390, 1], []], ![[371, 624, 637, 151], [608, 20, 402, 401], [306, 437], [379, 177], [119, 520, 484, 284], [265, 321], [572, 531], [636, 470, 450, 359], [351, 328]], ![[440, 278, 318, 237], [448, 68, 273, 132], [622, 546], [520, 432], [432, 469, 507, 302], [570, 148], [625, 52], [276, 294, 422, 391], [638, 328]]]
 h' := ![![[282, 40, 473], [2, 151, 523], [306, 380, 448], [561, 487, 145], [518, 112, 191], [362, 380, 542], [293, 397, 248], [418, 278, 524], [0, 0, 1], [0, 1]], ![[108, 618, 186], [515, 546, 555], [278, 658, 576], [16, 596, 346], [625, 266, 333], [638, 637, 17], [332, 275, 342], [349, 501, 616], [508, 147, 618], [282, 40, 473]], ![[0, 1], [169, 621, 240], [8, 280, 294], [517, 235, 168], [312, 281, 135], [434, 301, 100], [539, 646, 69], [508, 539, 178], [46, 512, 40], [108, 618, 186]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [547, 468], []]
 b := ![[], [183, 186, 619], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI659N0 : CertifiedPrimeIdeal' SI659N0 659 where
  n := 3
  hpos := by decide
  P := [43, 647, 269, 1]
  hirr := P659P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1866000, 980970, 566776, 2200294, -2176770]
  a := ![-1, 7, 6, 9, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![388302, -1023694, 1119842, 2200294, -2176770]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI659N0 : Ideal.IsPrime I659N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI659N0 B_one_repr
lemma NI659N0 : Nat.card (O ⧸ I659N0) = 286191179 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI659N0

def I659N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45, -25, -3, -29, -22]] i)))

def SI659N1: IdealEqSpanCertificate' Table ![![-45, -25, -3, -29, -22]] 
 ![![659, 0, 0, 0, 0], ![279, 1, 0, 0, 0], ![290, 0, 1, 0, 0], ![593, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] where
  M :=![![![-45, -25, -3, -29, -22], ![-176, -129, 8, -131, -109], ![-436, -291, 2, -308, -251], ![-916, -626, 13, -657, -533], ![-2076, -1416, 29, -1484, -1216]]]
  hmulB := by decide  
  f := ![![![-4311, -262, 3489, 441, -812]], ![![-1835, -119, 1475, 188, -343]], ![![-1894, -120, 1526, 194, -355]], ![![-3865, -229, 3136, 395, -730]], ![![-204, -11, 167, 21, -39]]]
  g := ![![![39, -25, -3, -29, -22], ![174, -129, 8, -131, -109], ![411, -291, 2, -308, -251], ![875, -626, 13, -657, -533], ![1978, -1416, 29, -1484, -1216]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI659N1 : Nat.card (O ⧸ I659N1) = 659 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI659N1)

lemma isPrimeI659N1 : Ideal.IsPrime I659N1 := prime_ideal_of_norm_prime hp659.out _ NI659N1

def I659N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, 111, 129, -7, -34]] i)))

def SI659N2: IdealEqSpanCertificate' Table ![![27, 111, 129, -7, -34]] 
 ![![659, 0, 0, 0, 0], ![625, 1, 0, 0, 0], ![81, 0, 1, 0, 0], ![76, 0, 0, 1, 0], ![490, 0, 0, 0, 1]] where
  M :=![![![27, 111, 129, -7, -34], ![-272, -7, 236, 27, -55], ![-220, -169, -34, 30, 13], ![188, -106, -317, -17, 79], ![36, -56, -109, 2, 26]]]
  hmulB := by decide  
  f := ![![![3537, -204, 1629, 1099, 40]], ![![3355, -187, 1541, 1046, 43]], ![![455, -16, 203, 147, 13]], ![![440, -1, 187, 150, 24]], ![![2706, -101, 1211, 871, 73]]]
  g := ![![![-95, 111, 129, -7, -34], ![15, -7, 236, 27, -55], ![151, -169, -34, 30, 13], ![83, -106, -317, -17, 79], ![47, -56, -109, 2, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI659N2 : Nat.card (O ⧸ I659N2) = 659 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI659N2)

lemma isPrimeI659N2 : Ideal.IsPrime I659N2 := prime_ideal_of_norm_prime hp659.out _ NI659N2
def MulI659N0 : IdealMulLeCertificate' Table 
  ![![205, -77, 126, 37, -39]] ![![-45, -25, -3, -29, -22]]
  ![![-3537, 204, -1629, -1099, -40]] where
 M := ![![![-3537, 204, -1629, -1099, -40]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI659N1 : IdealMulLeCertificate' Table 
  ![![-3537, 204, -1629, -1099, -40]] ![![27, 111, 129, -7, -34]]
  ![![659, 0, 0, 0, 0]] where
 M := ![![![-659, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I661N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![203465, 176970, 60387, -27456, -19977]] i)))

def SI661N0: IdealEqSpanCertificate' Table ![![203465, 176970, 60387, -27456, -19977]] 
 ![![661, 0, 0, 0, 0], ![0, 661, 0, 0, 0], ![0, 0, 661, 0, 0], ![0, 0, 0, 661, 0], ![446, 280, 520, 551, 1]] where
  M :=![![![203465, 176970, 60387, -27456, -19977], ![-159816, 191423, 408852, 8391, -102345], ![-409380, -135540, 183032, 46449, -38586], ![-74436, -328575, -386415, 20561, 101553], ![-80196, -127293, -103257, 13110, 28424]]]
  hmulB := by decide  
  f := ![![![29, -201, 111, -174, 69]], ![![552, 659, -54, 879, -453]], ![![-1812, -1323, -220, -2079, 1092]], ![![4092, 2424, 783, 4202, -2346]], ![![2230, 1118, 530, 2113, -1237]]]
  g := ![![![13787, 8730, 15807, 16611, -19977], ![68814, 43643, 81132, 85326, -102345], ![25416, 16140, 30632, 32235, -38586], ![-68634, -43515, -80475, -84622, 101553], ![-19300, -12233, -22517, -23674, 28424]]]
  hle1 := by decide   
  hle2 := by decide  


def P661P0 : CertificateIrreducibleZModOfList' 661 4 2 9 [644, 463, 248, 644, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 26, 533, 333], [587, 510, 551, 508], [623, 124, 238, 481], [0, 1]]
 g := ![![[202, 492, 71, 387], [610, 440, 133], [258, 420, 23, 9], [486, 644, 220], [307, 7, 626, 215], [247, 350, 506], [245, 517, 359], [17, 1], []], ![[498, 319, 533, 201, 548, 430], [613, 101, 547], [98, 645, 273, 279, 574, 659], [478, 635, 435], [627, 289, 97, 474, 387, 211], [70, 156, 390], [31, 220, 383], [555, 647, 504, 105, 458, 309], [437, 623, 502]], ![[290, 86, 447, 197, 622, 33], [549, 382, 141], [139, 624, 352, 134, 203, 492], [606, 515, 644], [247, 224, 615, 304, 437, 177], [558, 347, 123], [631, 166, 274], [369, 290, 37, 206, 120, 235], [590, 641, 274]], ![[224, 217, 568, 100, 155, 130], [403, 483, 227], [409, 154, 107, 611, 477, 153], [536, 632, 9], [418, 375, 436, 160, 577, 405], [423, 299, 498], [552, 200, 465], [508, 146, 629, 16, 159, 334], [180, 437, 11]]]
 h' := ![![[129, 26, 533, 333], [368, 497, 185, 354], [420, 527, 361, 46], [464, 240, 242, 658], [592, 66, 165, 243], [204, 292, 363, 350], [434, 589, 602, 294], [289, 78, 609, 41], [0, 0, 1], [0, 1]], ![[587, 510, 551, 508], [270, 526, 386, 236], [263, 100, 254, 99], [424, 503, 651, 249], [298, 28, 84, 306], [432, 653, 492, 430], [35, 425, 642, 66], [13, 272, 354, 274], [274, 48, 418, 512], [129, 26, 533, 333]], ![[623, 124, 238, 481], [561, 173, 86, 65], [160, 473, 152, 313], [242, 19, 653, 16], [326, 642, 222, 109], [405, 634, 272, 383], [537, 592, 220, 633], [216, 538, 19, 508], [303, 18, 541, 177], [587, 510, 551, 508]], ![[0, 1], [583, 126, 4, 6], [539, 222, 555, 203], [592, 560, 437, 399], [370, 586, 190, 3], [216, 404, 195, 159], [364, 377, 519, 329], [211, 434, 340, 499], [538, 595, 362, 633], [623, 124, 238, 481]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [534, 101, 59], []]
 b := ![[], [], [315, 143, 592, 238], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI661N0 : CertifiedPrimeIdeal' SI661N0 661 where
  n := 4
  hpos := by decide
  P := [644, 463, 248, 644, 1]
  hirr := P661P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10767451516, -6317357044, -2051064960, -10912735114, 5874106650]
  a := ![0, -12, 0, -22, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3979756456, -2497832404, -4624185360, -4913079424, 5874106650]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI661N0 : Ideal.IsPrime I661N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI661N0 B_one_repr
lemma NI661N0 : Nat.card (O ⧸ I661N0) = 190899960241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI661N0

def I661N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, -201, 111, -174, 69]] i)))

def SI661N1: IdealEqSpanCertificate' Table ![![29, -201, 111, -174, 69]] 
 ![![661, 0, 0, 0, 0], ![329, 1, 0, 0, 0], ![412, 0, 1, 0, 0], ![475, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![29, -201, 111, -174, 69], ![552, 659, -54, 879, -453], ![-1812, -1323, -220, -2079, 1092], ![4092, 2424, 783, 4202, -2346], ![-5916, -3540, -1089, -6045, 3215]]]
  hmulB := by decide  
  f := ![![![203465, 176970, 60387, -27456, -19977]], ![![101029, 88373, 30675, -13653, -10098]], ![![126200, 110100, 37916, -17043, -12510]], ![![146099, 126675, 42810, -19699, -14202]], ![![2649, 2217, 666, -354, -229]]]
  g := ![![![155, -201, 111, -174, 69], ![-919, 659, -54, 879, -453], ![2272, -1323, -220, -2079, 1092], ![-4676, 2424, 783, 4202, -2346], ![6732, -3540, -1089, -6045, 3215]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI661N1 : Nat.card (O ⧸ I661N1) = 661 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI661N1)

lemma isPrimeI661N1 : Ideal.IsPrime I661N1 := prime_ideal_of_norm_prime hp661.out _ NI661N1
def MulI661N0 : IdealMulLeCertificate' Table 
  ![![203465, 176970, 60387, -27456, -19977]] ![![29, -201, 111, -174, 69]]
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

def I673N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![433, 73, 172, 272, -170]] i)))

def SI673N0: IdealEqSpanCertificate' Table ![![433, 73, 172, 272, -170]] 
 ![![673, 0, 0, 0, 0], ![0, 673, 0, 0, 0], ![462, 164, 1, 0, 0], ![281, 592, 0, 1, 0], ![0, 507, 0, 0, 1]] where
  M :=![![![433, 73, 172, 272, -170], ![-1360, -517, -398, -1118, 646], ![2584, 1295, 601, 2422, -1354], ![-4736, -2745, -928, -4790, 2633], ![6712, 3873, 1322, 6767, -3722]]]
  hmulB := by decide  
  f := ![![![-863, -543, 70, -500, -434]], ![![-3472, -2463, -86, -2398, -1934]], ![![-1450, -981, 27, -936, -776]], ![![-3439, -2410, -46, -2336, -1897]], ![![-2672, -1894, -64, -1847, -1490]]]
  g := ![![![-231, -153, 172, 272, -170], ![738, 593, -398, -1118, 646], ![-1420, -1255, 601, 2422, -1354], ![2630, 2452, -928, -4790, 2633], ![-3723, -3465, 1322, 6767, -3722]]]
  hle1 := by decide   
  hle2 := by decide  


def P673P0 : CertificateIrreducibleZModOfList' 673 2 2 9 [614, 503, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [170, 672], [0, 1]]
 g := ![![[539, 529], [128], [168], [1], [671], [72, 72], [464], [643, 634], [1]], ![[287, 144], [128], [168], [1], [671], [198, 601], [464], [70, 39], [1]]]
 h' := ![![[170, 672], [500, 23], [32, 428], [369, 644], [237, 1], [210, 262], [541, 352], [249, 118], [59, 170], [0, 1]], ![[0, 1], [372, 650], [108, 245], [150, 29], [407, 672], [332, 411], [484, 321], [119, 555], [20, 503], [170, 672]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [509]]
 b := ![[], [240, 591]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI673N0 : CertifiedPrimeIdeal' SI673N0 673 where
  n := 2
  hpos := by decide
  P := [614, 503, 1]
  hirr := P673P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5650, 2062, 1461, 231, -1094]
  a := ![13, 5, 5, 6, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1091, 268, 1461, 231, -1094]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI673N0 : Ideal.IsPrime I673N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI673N0 B_one_repr
lemma NI673N0 : Nat.card (O ⧸ I673N0) = 452929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI673N0

def I673N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-601, -1002, -840, 100, 230]] i)))

def SI673N1: IdealEqSpanCertificate' Table ![![-601, -1002, -840, 100, 230]] 
 ![![673, 0, 0, 0, 0], ![79, 1, 0, 0, 0], ![581, 0, 1, 0, 0], ![566, 0, 0, 1, 0], ![55, 0, 0, 0, 1]] where
  M :=![![![-601, -1002, -840, 100, 230], ![1840, -391, -2204, -170, 530], ![2120, 1228, -221, -264, 10], ![-880, 1302, 2594, 31, -656], ![-16, 590, 830, -34, -223]]]
  hmulB := by decide  
  f := ![![![-532201, -313118, -101964, -542284, 297578]], ![![-58935, -34681, -11288, -60058, 32956]], ![![-467349, -274942, -89549, -476184, 261308]], ![![-431718, -254046, -82690, -439941, 241412]], ![![-65903, -38708, -12658, -67090, 36823]]]
  g := ![![![739, -1002, -840, 100, 230], ![2051, -391, -2204, -170, 530], ![271, 1228, -221, -264, 10], ![-2366, 1302, 2594, 31, -656], ![-739, 590, 830, -34, -223]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI673N1 : Nat.card (O ⧸ I673N1) = 673 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI673N1)

lemma isPrimeI673N1 : Ideal.IsPrime I673N1 := prime_ideal_of_norm_prime hp673.out _ NI673N1

def I673N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-98543, -64953, -582, 12470, 2260]] i)))

def SI673N2: IdealEqSpanCertificate' Table ![![-98543, -64953, -582, 12470, 2260]] 
 ![![673, 0, 0, 0, 0], ![127, 1, 0, 0, 0], ![348, 0, 1, 0, 0], ![384, 0, 0, 1, 0], ![74, 0, 0, 0, 1]] where
  M :=![![![-98543, -64953, -582, 12470, 2260], ![18080, -100295, -154846, 2186, 39670], ![158680, 29699, -102481, -17094, 23114], ![83416, 144579, 124216, -14128, -33919], ![49168, 51949, 27274, -7001, -8108]]]
  hmulB := by decide  
  f := ![![![-118463, 20447, -63744, -30350, 12268]], ![![-22209, 3724, -11878, -5744, 2198]], ![![-61724, 10437, -33079, -15944, 6260]], ![![-68000, 11357, -36332, -17594, 6641]], ![![-14382, 1381, -7046, -4321, 738]]]
  g := ![![![5048, -64953, -582, 12470, 2260], ![93413, -100295, -154846, 2186, 39670], ![54835, 29699, -102481, -17094, 23114], ![-79599, 144579, 124216, -14128, -33919], ![-18947, 51949, 27274, -7001, -8108]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI673N2 : Nat.card (O ⧸ I673N2) = 673 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI673N2)

lemma isPrimeI673N2 : Ideal.IsPrime I673N2 := prime_ideal_of_norm_prime hp673.out _ NI673N2

def I673N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4247, 3417, 878, -562, -318]] i)))

def SI673N3: IdealEqSpanCertificate' Table ![![4247, 3417, 878, -562, -318]] 
 ![![673, 0, 0, 0, 0], ![139, 1, 0, 0, 0], ![98, 0, 1, 0, 0], ![186, 0, 0, 1, 0], ![529, 0, 0, 0, 1]] where
  M :=![![![4247, 3417, 878, -562, -318], ![-2544, 4097, 7958, 92, -2004], ![-8016, -2349, 4005, 898, -864], ![-2184, -6663, -7226, 486, 1917], ![-1808, -2525, -1852, 285, 520]]]
  hmulB := by decide  
  f := ![![![-4044985, 1310925, -2554588, -664066, 781998]], ![![-826147, 267746, -521750, -135626, 159714]], ![![-596210, 193215, -376529, -97888, 115266]], ![![-1117002, 362025, -705446, -183360, 215937]], ![![-3181377, 1031014, -2009168, -522313, 615052]]]
  g := ![![![-422, 3417, 878, -562, -318], ![-459, 4097, 7958, 92, -2004], ![321, -2349, 4005, 898, -864], ![784, -6663, -7226, 486, 1917], ![301, -2525, -1852, 285, 520]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI673N3 : Nat.card (O ⧸ I673N3) = 673 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI673N3)

lemma isPrimeI673N3 : Ideal.IsPrime I673N3 := prime_ideal_of_norm_prime hp673.out _ NI673N3
def MulI673N0 : IdealMulLeCertificate' Table 
  ![![433, 73, 172, 272, -170]] ![![-601, -1002, -840, 100, 230]]
  ![![2087, 2651, 1844, -306, -522]] where
 M := ![![![2087, 2651, 1844, -306, -522]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI673N1 : IdealMulLeCertificate' Table 
  ![![2087, 2651, 1844, -306, -522]] ![![-98543, -64953, -582, 12470, 2260]]
  ![![83685767, -418032552, -652933468, 8276330, 167115596]] where
 M := ![![![83685767, -418032552, -652933468, 8276330, 167115596]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI673N2 : IdealMulLeCertificate' Table 
  ![![83685767, -418032552, -652933468, 8276330, 167115596]] ![![4247, 3417, 878, -562, -318]]
  ![![673, 0, 0, 0, 0]] where
 M := ![![![6332582441937, -370096450063, -6237528329102, -620174408862, 1478025511184]]]
 hmul := by decide  
 g := ![![![![9409483569, -549920431, -9268244174, -921507294, 2196174608]]]]
 hle2 := by decide  


def PBC673 : ContainsPrimesAboveP 673 ![I673N0, I673N1, I673N2, I673N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI673N0
    exact isPrimeI673N1
    exact isPrimeI673N2
    exact isPrimeI673N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 673 (by decide) (𝕀 ⊙ MulI673N0 ⊙ MulI673N1 ⊙ MulI673N2)
instance hp677 : Fact (Nat.Prime 677) := {out := by norm_num}

def I677N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14633, -36349, -63417, 3, 16106]] i)))

def SI677N0: IdealEqSpanCertificate' Table ![![14633, -36349, -63417, 3, 16106]] 
 ![![677, 0, 0, 0, 0], ![0, 677, 0, 0, 0], ![0, 0, 677, 0, 0], ![0, 0, 0, 677, 0], ![655, 194, 623, 615, 1]] where
  M :=![![![14633, -36349, -63417, 3, 16106], ![128848, 31743, -72704, -14095, 16115], ![64460, 75407, 45838, -9254, -13085], ![-116764, 11192, 121013, 11715, -28481], ![-28948, 14626, 46313, 3352, -10624]]]
  hmulB := by decide  
  f := ![![![23797, 13906, 4605, 24159, -13268]], ![![-106144, -62097, -20506, -107825, 59209]], ![![236836, 138610, 45728, 240638, -132133]], ![![-475460, -278321, -91775, -483144, 265286]], ![![-220373, -129038, -42519, -223970, 122974]]]
  g := ![![![-15561, -4669, -14915, -14631, 16106], ![-15401, -4571, -14937, -14660, 16115], ![12755, 3861, 12109, 11873, -13085], ![27383, 8178, 26388, 25890, -28481], ![10236, 3066, 9845, 9656, -10624]]]
  hle1 := by decide   
  hle2 := by decide  


def P677P0 : CertificateIrreducibleZModOfList' 677 4 2 9 [167, 447, 220, 168, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [141, 378, 429, 211], [554, 380, 564, 559], [491, 595, 361, 584], [0, 1]]
 g := ![![[514, 567, 93, 520], [526, 555, 511], [546, 489, 216, 652], [572, 104, 122], [666, 197, 140], [280, 172, 560, 133], [133, 379, 79], [509, 1], []], ![[504, 77, 628, 151, 366, 86], [551, 2, 262], [23, 117, 257, 314, 511, 46], [290, 149, 222], [386, 354, 562], [2, 442, 451, 147, 44, 263], [210, 666, 583], [20, 649, 608, 196, 235, 335], [335, 247, 516]], ![[285, 232, 308, 648, 195, 168], [561, 578, 62], [237, 169, 520, 108, 426, 366], [572, 357, 421], [599, 132, 354], [310, 178, 651, 336, 102, 45], [644, 527, 404], [190, 411, 81, 354, 272, 328], [497, 68, 384]], ![[234, 375, 46, 363, 168, 141], [230, 62, 341], [201, 334, 216, 197, 77, 248], [156, 389, 41], [5, 147, 201], [627, 350, 185, 351, 6, 543], [265, 537, 201], [505, 83, 174, 401, 572, 641], [63, 364, 525]]]
 h' := ![![[141, 378, 429, 211], [178, 502, 273, 335], [213, 429, 232, 176], [189, 650, 609, 547], [661, 544, 224, 590], [630, 604, 479, 188], [167, 90, 339, 563], [299, 459, 632, 247], [0, 0, 1], [0, 1]], ![[554, 380, 564, 559], [420, 113, 542, 79], [538, 257, 372, 465], [211, 116, 521, 342], [429, 585, 167, 179], [24, 311, 468, 609], [602, 473, 344, 273], [596, 340, 658, 113], [494, 227, 351, 580], [141, 378, 429, 211]], ![[491, 595, 361, 584], [75, 301, 292, 255], [61, 352, 503, 268], [27, 82, 320, 495], [447, 558, 0, 261], [646, 307, 667, 134], [432, 638, 67, 514], [316, 434, 530, 571], [507, 673, 153, 35], [554, 380, 564, 559]], ![[0, 1], [120, 438, 247, 8], [349, 316, 247, 445], [544, 506, 581, 647], [105, 344, 286, 324], [431, 132, 417, 423], [226, 153, 604, 4], [511, 121, 211, 423], [380, 454, 172, 62], [491, 595, 361, 584]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [123, 440, 502], []]
 b := ![[], [], [178, 415, 484, 119], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI677N0 : CertifiedPrimeIdeal' SI677N0 677 where
  n := 4
  hpos := by decide
  P := [167, 447, 220, 168, 1]
  hirr := P677P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2939987, -1805811, -391187, -2737526, 673851]
  a := ![-1, -2, 0, -3, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-656296, -195765, -620680, -616183, 673851]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI677N0 : Ideal.IsPrime I677N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI677N0 B_one_repr
lemma NI677N0 : Nat.card (O ⧸ I677N0) = 210065472241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI677N0

def I677N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23797, 13906, 4605, 24159, -13268]] i)))

def SI677N1: IdealEqSpanCertificate' Table ![![23797, 13906, 4605, 24159, -13268]] 
 ![![677, 0, 0, 0, 0], ![185, 1, 0, 0, 0], ![151, 0, 1, 0, 0], ![157, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![23797, 13906, 4605, 24159, -13268], ![-106144, -62097, -20506, -107825, 59209], ![236836, 138610, 45728, 240638, -132133], ![-475460, -278321, -91775, -483144, 265286], ![671452, 393047, 129607, 682301, -374639]]]
  hmulB := by decide  
  f := ![![![14633, -36349, -63417, 3, 16106]], ![![4189, -9886, -17437, -20, 4425]], ![![3359, -7996, -14077, -13, 3573]], ![![3221, -8413, -14528, 18, 3693]], ![![195, -569, -962, 5, 246]]]
  g := ![![![-10179, 13906, 4605, 24159, -13268], ![45429, -62097, -20506, -107825, 59209], ![-101385, 138610, 45728, 240638, -132133], ![203556, -278321, -91775, -483144, 265286], ![-287464, 393047, 129607, 682301, -374639]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI677N1 : Nat.card (O ⧸ I677N1) = 677 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI677N1)

lemma isPrimeI677N1 : Ideal.IsPrime I677N1 := prime_ideal_of_norm_prime hp677.out _ NI677N1
def MulI677N0 : IdealMulLeCertificate' Table 
  ![![14633, -36349, -63417, 3, 16106]] ![![23797, 13906, 4605, 24159, -13268]]
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

def I683N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8957, 1978, 10831, 819, -2610]] i)))

def SI683N0: IdealEqSpanCertificate' Table ![![-8957, 1978, 10831, 819, -2610]] 
 ![![683, 0, 0, 0, 0], ![0, 683, 0, 0, 0], ![0, 0, 683, 0, 0], ![417, 132, 362, 1, 0], ![587, 93, 497, 0, 1]] where
  M :=![![![-8957, 1978, 10831, 819, -2610], ![-20880, -11995, 2318, 2573, -153], ![-612, -10950, -14568, 496, 3783], ![25572, 7617, -12605, -2862, 2712], ![8388, 1037, -6155, -887, 1417]]]
  hmulB := by decide  
  f := ![![![-9535, 3095, -6025, -1563, 1848]], ![![14784, -4757, 9316, 2449, -2841]], ![![-11364, 3723, -7206, -1852, 2253]], ![![-8985, 2943, -5696, -1462, 1773]], ![![-14455, 4723, -9156, -2358, 2842]]]
  g := ![![![1730, 200, 1481, 819, -2610], ![-1470, -494, -1249, 2573, -153], ![-3555, -627, -3037, 496, 3783], ![-546, 195, -475, -2862, 2712], ![-664, -20, -570, -887, 1417]]]
  hle1 := by decide   
  hle2 := by decide  


def P683P0 : CertificateIrreducibleZModOfList' 683 3 2 9 [45, 249, 167, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [290, 55, 134], [226, 627, 549], [0, 1]]
 g := ![![[373, 353, 329], [510, 549, 559], [511, 4], [609, 419, 266], [509, 571], [580, 179, 146], [99, 672], [320, 516, 1], []], ![[485, 391, 301, 335], [193, 627, 671, 470], [594, 250], [228, 461, 413, 426], [327, 191], [308, 44, 518, 368], [174, 572], [621, 656, 680, 179], [115, 198]], ![[402, 606, 642, 81], [476, 130, 332, 650], [387, 19], [29, 228, 151, 604], [276, 509], [424, 667, 170, 544], [83, 438], [506, 123, 479, 352], [383, 198]]]
 h' := ![![[290, 55, 134], [272, 237, 523], [622, 395, 418], [598, 124, 2], [460, 87, 505], [537, 163, 579], [160, 507, 588], [626, 233, 392], [0, 0, 1], [0, 1]], ![[226, 627, 549], [6, 332, 421], [129, 24, 153], [436, 311, 112], [396, 121, 453], [91, 469, 346], [444, 2, 177], [645, 601, 391], [380, 502, 627], [290, 55, 134]], ![[0, 1], [141, 114, 422], [344, 264, 112], [1, 248, 569], [677, 475, 408], [528, 51, 441], [667, 174, 601], [456, 532, 583], [374, 181, 55], [226, 627, 549]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 195], []]
 b := ![[], [347, 88, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI683N0 : CertifiedPrimeIdeal' SI683N0 683 where
  n := 3
  hpos := by decide
  P := [45, 249, 167, 1]
  hirr := P683P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-697902, -427550, -108273, -732158, 407586]
  a := ![3, -4, 7, -8, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![95694, 85376, 91307, -732158, 407586]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI683N0 : Ideal.IsPrime I683N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI683N0 B_one_repr
lemma NI683N0 : Nat.card (O ⧸ I683N0) = 318611987 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI683N0

def I683N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9535, -3095, 6025, 1563, -1848]] i)))

def SI683N1: IdealEqSpanCertificate' Table ![![9535, -3095, 6025, 1563, -1848]] 
 ![![683, 0, 0, 0, 0], ![0, 683, 0, 0, 0], ![226, 321, 1, 0, 0], ![535, 547, 0, 1, 0], ![102, 537, 0, 0, 1]] where
  M :=![![![9535, -3095, 6025, 1563, -1848], ![-14784, 4757, -9316, -2449, 2841], ![11364, -3723, 7206, 1852, -2253], ![-1620, 348, -917, -381, 231], ![2724, -1114, 1879, 346, -782]]]
  hmulB := by decide  
  f := ![![![8957, -1978, -10831, -819, 2610]], ![![20880, 11995, -2318, -2573, 153]], ![![12778, 4999, -4652, -1481, 930]], ![![23701, 8046, -10322, -2698, 2163]], ![![17742, 9134, -3431, -2144, 508]]]
  g := ![![![-2928, -2635, 6025, 1563, -1848], ![4555, 4113, -9316, -2449, 2841], ![-3482, -3104, 7206, 1852, -2253], ![565, 555, -917, -381, 231], ![-772, -547, 1879, 346, -782]]]
  hle1 := by decide   
  hle2 := by decide  


def P683P1 : CertificateIrreducibleZModOfList' 683 2 2 9 [557, 576, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [107, 682], [0, 1]]
 g := ![![[93, 588], [329, 412], [445], [419, 273], [186], [562, 594], [64], [68, 521], [1]], ![[173, 95], [18, 271], [445], [261, 410], [186], [601, 89], [64], [492, 162], [1]]]
 h' := ![![[107, 682], [474, 165], [293, 437], [203, 301], [121, 485], [463, 263], [286, 506], [372, 8], [126, 107], [0, 1]], ![[0, 1], [371, 518], [608, 246], [309, 382], [108, 198], [601, 420], [471, 177], [545, 675], [647, 576], [107, 682]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [675]]
 b := ![[], [214, 679]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI683N1 : CertifiedPrimeIdeal' SI683N1 683 where
  n := 2
  hpos := by decide
  P := [557, 576, 1]
  hirr := P683P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-146, -2846, -3041, -4882, 9188]
  a := ![1, -4, -4, -5, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3458, -1889, -3041, -4882, 9188]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI683N1 : Ideal.IsPrime I683N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI683N1 B_one_repr
lemma NI683N1 : Nat.card (O ⧸ I683N1) = 466489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI683N1
def MulI683N0 : IdealMulLeCertificate' Table 
  ![![-8957, 1978, 10831, 819, -2610]] ![![9535, -3095, 6025, 1563, -1848]]
  ![![683, 0, 0, 0, 0]] where
 M := ![![![-683, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I691N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63791, -20681, 40290, 10465, -12327]] i)))

def SI691N0: IdealEqSpanCertificate' Table ![![63791, -20681, 40290, 10465, -12327]] 
 ![![691, 0, 0, 0, 0], ![0, 691, 0, 0, 0], ![516, 411, 1, 0, 0], ![61, 287, 0, 1, 0], ![219, 65, 0, 0, 1]] where
  M :=![![![63791, -20681, 40290, 10465, -12327], ![-98616, 31981, -62292, -16174, 19068], ![76272, -24697, 48155, 12533, -14727], ![-9600, 3139, -6084, -1569, 1902], ![19848, -6293, 12450, 3346, -3763]]]
  hmulB := by decide  
  f := ![![![-11779, -8713, -1380, 1529, 609]], ![![4872, -11643, -20484, -26, 5196]], ![![-5868, -13424, -13231, 1123, 3549]], ![![995, -5579, -8604, 122, 2205]], ![![-3267, -3847, -2358, 481, 680]]]
  g := ![![![-27011, -27181, 40290, 10465, -12327], ![41758, 42021, -62292, -16174, 19068], ![-32288, -32498, 48155, 12533, -14727], ![4065, 4096, -6084, -1569, 1902], ![-8371, -8450, 12450, 3346, -3763]]]
  hle1 := by decide   
  hle2 := by decide  


def P691P0 : CertificateIrreducibleZModOfList' 691 2 2 9 [491, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [597, 690], [0, 1]]
 g := ![![[117, 38], [296, 356], [143], [28], [472, 563], [493, 454], [329], [403, 544], [1]], ![[0, 653], [0, 335], [143], [28], [66, 128], [659, 237], [329], [401, 147], [1]]]
 h' := ![![[597, 690], [465, 27], [372, 298], [188, 88], [424, 277], [478, 517], [356, 213], [444, 358], [200, 597], [0, 1]], ![[0, 1], [0, 664], [0, 393], [208, 603], [644, 414], [250, 174], [373, 478], [651, 333], [53, 94], [597, 690]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [582]]
 b := ![[], [548, 291]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI691N0 : CertifiedPrimeIdeal' SI691N0 691 where
  n := 2
  hpos := by decide
  P := [491, 94, 1]
  hirr := P691P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![835, 75, -113, 143, 63]
  a := ![4, 1, -1, 2, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![53, 2, -113, 143, 63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI691N0 : Ideal.IsPrime I691N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI691N0 B_one_repr
lemma NI691N0 : Nat.card (O ⧸ I691N0) = 477481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI691N0

def I691N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![685, 458, 13, -87, -18]] i)))

def SI691N1: IdealEqSpanCertificate' Table ![![685, 458, 13, -87, -18]] 
 ![![691, 0, 0, 0, 0], ![217, 1, 0, 0, 0], ![295, 0, 1, 0, 0], ![361, 0, 0, 1, 0], ![535, 0, 0, 0, 1]] where
  M :=![![![685, 458, 13, -87, -18], ![-144, 695, 1090, -13, -279], ![-1116, -218, 708, 120, -159], ![-564, -1009, -883, 98, 240], ![-340, -365, -197, 47, 59]]]
  hmulB := by decide  
  f := ![![![103255, -33263, 65077, 17051, -19776]], ![![32197, -10370, 20291, 5318, -6165]], ![![44263, -14256, 27895, 7311, -8475]], ![![53929, -17365, 33984, 8910, -10323]], ![![80007, -25757, 50414, 13221, -15310]]]
  g := ![![![-89, 458, 13, -87, -18], ![-461, 695, 1090, -13, -279], ![-175, -218, 708, 120, -159], ![456, -1009, -883, 98, 240], ![128, -365, -197, 47, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI691N1 : Nat.card (O ⧸ I691N1) = 691 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI691N1)

lemma isPrimeI691N1 : Ideal.IsPrime I691N1 := prime_ideal_of_norm_prime hp691.out _ NI691N1

def I691N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![717, 378, 158, 689, -383]] i)))

def SI691N2: IdealEqSpanCertificate' Table ![![717, 378, 158, 689, -383]] 
 ![![691, 0, 0, 0, 0], ![488, 1, 0, 0, 0], ![471, 0, 1, 0, 0], ![229, 0, 0, 1, 0], ![386, 0, 0, 0, 1]] where
  M :=![![![717, 378, 158, 689, -383], ![-3064, -1729, -622, -3054, 1684], ![6736, 3894, 1325, 6799, -3739], ![-13424, -7852, -2594, -13634, 7487], ![18960, 11086, 3666, 19255, -10574]]]
  hmulB := by decide  
  f := ![![![56127, 38176, -970, 39891, 32635]], ![![40016, 27219, -690, 28442, 23268]], ![![39139, 26624, -673, 27822, 22760]], ![![20473, 13930, -348, 14561, 11910]], ![![35610, 24232, -602, 25331, 20718]]]
  g := ![![![-388, 378, 158, 689, -383], ![1712, -1729, -622, -3054, 1684], ![-3808, 3894, 1325, 6799, -3739], ![7630, -7852, -2594, -13634, 7487], ![-10775, 11086, 3666, 19255, -10574]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI691N2 : Nat.card (O ⧸ I691N2) = 691 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI691N2)

lemma isPrimeI691N2 : Ideal.IsPrime I691N2 := prime_ideal_of_norm_prime hp691.out _ NI691N2

def I691N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-48139, 3727, 48678, 4678, -11562]] i)))

def SI691N3: IdealEqSpanCertificate' Table ![![-48139, 3727, 48678, 4678, -11562]] 
 ![![691, 0, 0, 0, 0], ![546, 1, 0, 0, 0], ![198, 0, 1, 0, 0], ![262, 0, 0, 1, 0], ![166, 0, 0, 0, 1]] where
  M :=![![![-48139, 3727, 48678, 4678, -11562], ![-92496, -61949, -1902, 11744, 2472], ![9888, -46891, -73693, 878, 18852], ![121656, 45763, -46818, -14022, 9507], ![41664, 8809, -25512, -4529, 5708]]]
  hmulB := by decide  
  f := ![![![-60572953, 19641305, -38259624, -9934702, 11706702]], ![![-47726742, 15475815, -30145590, -7827764, 9223968]], ![![-17461410, 5662021, -11029135, -2863880, 3374706]], ![![-22953634, 7442935, -14498190, -3764664, 4436175]], ![![-14578570, 4727269, -9208272, -2391041, 2817578]]]
  g := ![![![-15959, 3727, 48678, 4678, -11562], ![44314, -61949, -1902, 11744, 2472], ![53320, -46891, -73693, 878, 18852], ![-19536, 45763, -46818, -14022, 9507], ![756, 8809, -25512, -4529, 5708]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI691N3 : Nat.card (O ⧸ I691N3) = 691 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI691N3)

lemma isPrimeI691N3 : Ideal.IsPrime I691N3 := prime_ideal_of_norm_prime hp691.out _ NI691N3
def MulI691N0 : IdealMulLeCertificate' Table 
  ![![63791, -20681, 40290, 10465, -12327]] ![![685, 458, 13, -87, -18]]
  ![![179, -67, 137, 37, -42]] where
 M := ![![![179, -67, 137, 37, -42]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI691N1 : IdealMulLeCertificate' Table 
  ![![179, -67, 137, 37, -42]] ![![717, 378, 158, 689, -383]]
  ![![-36545, -39153, 1531, -53756, 27499]] where
 M := ![![![-36545, -39153, 1531, -53756, 27499]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI691N2 : IdealMulLeCertificate' Table 
  ![![-36545, -39153, 1531, -53756, 27499]] ![![-48139, 3727, 48678, 4678, -11562]]
  ![![691, 0, 0, 0, 0]] where
 M := ![![![1852571, -301276, -2098567, -202463, 515486]]]
 hmul := by decide  
 g := ![![![![2681, -436, -3037, -293, 746]]]]
 hle2 := by decide  


def PBC691 : ContainsPrimesAboveP 691 ![I691N0, I691N1, I691N2, I691N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI691N0
    exact isPrimeI691N1
    exact isPrimeI691N2
    exact isPrimeI691N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 691 (by decide) (𝕀 ⊙ MulI691N0 ⊙ MulI691N1 ⊙ MulI691N2)
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


def P701P0 : CertificateIrreducibleZModOfList' 701 5 2 9 [228, 607, 473, 72, 85, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [235, 673, 485, 57, 236], [271, 259, 647, 197, 493], [690, 573, 668, 238, 124], [121, 597, 303, 209, 549], [0, 1]]
 g := ![![[660, 454, 129, 199, 221], [604, 18, 651, 76], [82, 463, 545, 617, 478], [293, 501, 511, 262, 261], [187, 172, 437, 401, 556], [577, 514, 121, 357, 203], [346, 558, 274, 215], [1], []], ![[514, 437, 337, 465, 385, 217, 242, 212], [246, 373, 212, 296], [333, 587, 421, 542, 7, 545, 311, 129], [229, 216, 531, 231, 94, 59, 677, 508], [686, 99, 498, 618, 571, 136, 227, 629], [353, 544, 485, 164, 523, 403, 515, 525], [436, 437, 44, 52], [658, 680, 283, 622, 374, 606, 258, 336], [392, 427, 660, 317]], ![[39, 374, 437, 674, 283, 622, 223, 22], [219, 71, 456, 556], [201, 255, 483, 106, 341, 697, 432, 141], [688, 440, 323, 604, 377, 277, 67, 83], [585, 296, 94, 694, 79, 633, 261, 175], [243, 201, 206, 285, 106, 408, 542, 19], [218, 284, 563, 119], [281, 415, 684, 668, 615, 331, 455, 177], [517, 95, 71, 503]], ![[463, 255, 643, 640, 259, 620, 65, 124], [449, 7, 229, 133], [449, 470, 477, 135, 620, 265, 315, 700], [458, 477, 694, 198, 456, 579, 555, 589], [296, 139, 196, 269, 68, 623, 186, 7], [422, 451, 12, 589, 665, 297, 388, 159], [393, 612, 355, 45], [352, 371, 481, 374, 87, 655, 244, 186], [625, 540, 545, 655]], ![[326, 408, 432, 262, 191, 551, 368, 646], [270, 487, 147, 443], [33, 629, 524, 302, 32, 699, 594, 342], [89, 422, 356, 542, 478, 324, 561, 113], [1, 570, 185, 422, 500, 263, 23, 27], [167, 335, 514, 284, 324, 650, 308, 62], [403, 461, 505, 666], [260, 131, 593, 333, 252, 520, 191, 393], [383, 53, 617, 672]]]
 h' := ![![[235, 673, 485, 57, 236], [470, 452, 156, 402, 55], [231, 503, 372, 483, 130], [492, 441, 616, 513, 403], [125, 641, 691, 189, 128], [232, 91, 516, 318, 356], [435, 533, 374, 524, 576], [473, 94, 228, 629, 616], [0, 0, 1], [0, 1]], ![[271, 259, 647, 197, 493], [264, 337, 49, 393, 155], [401, 547, 133, 297, 97], [491, 291, 695, 495, 345], [193, 229, 550, 456, 633], [87, 477, 692, 456, 91], [664, 5, 668, 11, 15], [388, 483, 66, 390, 92], [198, 638, 272, 343, 12], [235, 673, 485, 57, 236]], ![[690, 573, 668, 238, 124], [12, 489, 454, 567, 295], [553, 655, 234, 323, 356], [217, 333, 561, 642, 434], [432, 277, 386, 39, 432], [583, 150, 362, 625, 661], [453, 689, 82, 500, 402], [86, 567, 565, 65, 39], [429, 478, 520, 92, 4], [271, 259, 647, 197, 493]], ![[121, 597, 303, 209, 549], [565, 179, 194, 169, 1], [637, 168, 616, 688, 527], [185, 558, 628, 583, 72], [614, 250, 494, 655, 383], [463, 673, 64, 617, 568], [683, 689, 688, 562, 558], [614, 329, 503, 141, 159], [625, 134, 588, 46, 414], [690, 573, 668, 238, 124]], ![[0, 1], [596, 646, 549, 572, 195], [276, 230, 47, 312, 292], [149, 480, 304, 571, 148], [451, 5, 683, 63, 527], [155, 11, 469, 87, 427], [667, 187, 291, 506, 552], [636, 630, 40, 177, 496], [221, 152, 21, 220, 271], [121, 597, 303, 209, 549]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [444, 551, 519, 174], [], [], []]
 b := ![[], [661, 2, 657, 697, 326], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI701N0 : CertifiedPrimeIdeal' SI701N0 701 where
  n := 5
  hpos := by decide
  P := [228, 607, 473, 72, 85, 1]
  hirr := P701P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-217005766, -51865588, 136045874, 30874844, -30731840]
  a := ![7, -1, -26, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-309566, -73988, 194074, 44044, -43840]
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



lemma PB1072I13_primes (p : ℕ) :
  p ∈ Set.range ![647, 653, 659, 661, 673, 677, 683, 691, 701] ↔ Nat.Prime p ∧ 643 < p ∧ p ≤ 701 := by
  rw [← List.mem_ofFn']
  convert primes_range 643 701 (by omega)

def PB1072I13 : PrimesBelowBoundCertificateInterval O 643 701 1072 where
  m := 9
  g := ![3, 2, 3, 2, 4, 2, 2, 4, 1]
  P := ![647, 653, 659, 661, 673, 677, 683, 691, 701]
  hP := PB1072I13_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I647N0, I647N1, I647N2]
    · exact ![I653N0, I653N1]
    · exact ![I659N0, I659N1, I659N2]
    · exact ![I661N0, I661N1]
    · exact ![I673N0, I673N1, I673N2, I673N3]
    · exact ![I677N0, I677N1]
    · exact ![I683N0, I683N1]
    · exact ![I691N0, I691N1, I691N2, I691N3]
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
    · exact ![418609, 418609, 647]
    · exact ![278445077, 426409]
    · exact ![286191179, 659, 659]
    · exact ![190899960241, 661]
    · exact ![452929, 673, 673, 673]
    · exact ![210065472241, 677]
    · exact ![318611987, 466489]
    · exact ![477481, 691, 691, 691]
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
      exact NI647N2
    · dsimp ; intro j
      fin_cases j
      exact NI653N0
      exact NI653N1
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
      exact NI673N3
    · dsimp ; intro j
      fin_cases j
      exact NI677N0
      exact NI677N1
    · dsimp ; intro j
      fin_cases j
      exact NI683N0
      exact NI683N1
    · dsimp ; intro j
      fin_cases j
      exact NI691N0
      exact NI691N1
      exact NI691N2
      exact NI691N3
    · dsimp ; intro j
      fin_cases j
      exact NI701N0
  β := ![I647N2, I659N1, I659N2, I661N1, I673N1, I673N2, I673N3, I677N1, I691N1, I691N2, I691N3]
  Il := ![[I647N2], [], [I659N1, I659N2], [I661N1], [I673N1, I673N2, I673N3], [I677N1], [], [I691N1, I691N2, I691N3], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
