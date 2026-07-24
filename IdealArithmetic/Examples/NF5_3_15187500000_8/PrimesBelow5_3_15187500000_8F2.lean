
import IdealArithmetic.Examples.NF5_3_15187500000_8.RI5_3_15187500000_8
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25708, 2535, -642, 18768, 9909]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![25708, 2535, -642, 18768, 9909]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![30, 9, 1, 0, 0], ![46, 44, 0, 1, 0], ![51, 40, 0, 0, 1]] where
  M :=![![![25708, 2535, -642, 18768, 9909], ![-210891, 100078, 11802, 50466, 46395], ![-861159, 188757, 158275, 443598, 105003], ![34518, 25548, 16200, 141919, 55926], ![-290238, 170550, 28410, 176886, 111115]]]
  hmulB := by decide  
  f := ![![![9603284248, 1427139273, 250346064, -1220906964, -1074361833]], ![![23135858175, 3438282670, 603123504, -2941326102, -2588359059]], ![![8239703586, 1224505089, 214799113, -1047545808, -921816504]], ![![21661312816, 3219127076, 564684036, -2753872277, -2423379438]], ![![20954162904, 3114028969, 546249546, -2663973498, -2344261652]]]
  g := ![![![-19757, -18117, -642, 18768, 9909], ![-78396, -60932, 11802, 50466, 46395], ![-468210, -372450, 158275, 443598, 105003], ![-146746, -128384, 16200, 141919, 55926], ![-223077, -183772, 28410, 176886, 111115]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [24, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 66], [0, 1]]
 g := ![![[40, 14], [42, 1], [60], [54], [15], [1]], ![[0, 53], [20, 66], [60], [54], [15], [1]]]
 h' := ![![[45, 66], [64, 9], [35, 66], [1, 23], [15, 56], [43, 45], [0, 1]], ![[0, 1], [0, 58], [57, 1], [31, 44], [56, 11], [58, 22], [45, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [59, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [24, 22, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-684564, 246710, 186589, 514719, 447417]
  a := ![24, -100, -27, -63, -153]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-787725, -626521, 186589, 514719, 447417]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-620, -91, -16, 78, 69]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-620, -91, -16, 78, 69]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![10, 46, 1, 0, 0], ![53, 19, 0, 1, 0], ![48, 17, 0, 0, 1]] where
  M :=![![![-620, -91, -16, 78, 69], ![-1485, -224, -38, 190, 165], ![-3553, -533, -97, 458, 405], ![532, 84, 14, -71, -60], ![720, 106, 20, -92, -83]]]
  hmulB := by decide  
  f := ![![![-8, 3, -2, -2, -9]], ![![161, -76, -8, -82, 3]], ![![109, -51, -7, -58, -3]], ![![43, -21, -4, -27, -6]], ![![33, -16, -4, -22, -8]]]
  g := ![![![-118, -30, -16, 78, 69], ![-285, -73, -38, 190, 165], ![-691, -174, -97, 458, 405], ![105, 27, 14, -71, -60], ![140, 35, 20, -92, -83]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P1 : CertificateIrreducibleZModOfList' 67 2 2 6 [40, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 66], [0, 1]]
 g := ![![[17, 62], [30, 62], [62], [1], [33], [1]], ![[0, 5], [13, 5], [62], [1], [33], [1]]]
 h' := ![![[57, 66], [6, 14], [28, 14], [37, 14], [12, 1], [27, 57], [0, 1]], ![[0, 1], [0, 53], [22, 53], [31, 53], [2, 66], [60, 10], [57, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [56, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N1 : CertifiedPrimeIdeal' SI67N1 67 where
  n := 2
  hpos := by decide
  P := [40, 10, 1]
  hirr := P67P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-98387553, 38766816, 23219610, 71898563, 54406257]
  a := ![178, -1157, -304, -859, -1638]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-100786684, -49556930, 23219610, 71898563, 54406257]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N1 B_one_repr
lemma NI67N1 : Nat.card (O ⧸ I67N1) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8933483, 1292904, 233108, -1152262, -976842]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![8933483, 1292904, 233108, -1152262, -976842]] 
 ![![67, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![62, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  M :=![![![8933483, 1292904, 233108, -1152262, -976842], ![21110908, 3318817, 549170, -2597540, -2479944], ![53011496, 6928724, 1388043, -7191284, -5312676], ![-8344104, -880474, -219830, 1231903, 699444], ![-9339248, -2086810, -238974, 854774, 1499789]]]
  hmulB := by decide  
  f := ![![![303353, -61784, -15548, 51318, 16410]], ![![47520, -5695, -3694, 7412, 4992]], ![![215395, -54292, -6713, 43246, 6570]], ![![297594, -62410, -14550, 51299, 15168]], ![![174346, -30602, -10398, 29162, 12521]]]
  g := ![![![1323757, 1292904, 233108, -1152262, -976842], ![3063698, 3318817, 549170, -2597540, -2479944], ![8037159, 6928724, 1388043, -7191284, -5312676], ![-1316492, -880474, -219830, 1231903, 699444], ![-1203940, -2086810, -238974, 854774, 1499789]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![25708, 2535, -642, 18768, 9909]] ![![-620, -91, -16, 78, 69]]
  ![![-303353, 61784, 15548, -51318, -16410]] where
 M := ![![![-303353, 61784, 15548, -51318, -16410]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![-303353, 61784, 15548, -51318, -16410]] ![![8933483, 1292904, 233108, -1152262, -976842]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![-67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-121914, 53825, 19152, 85052, 37773]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-121914, 53825, 19152, 85052, 37773]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![64, 67, 1, 0, 0], ![4, 65, 0, 1, 0], ![33, 41, 0, 0, 1]] where
  M :=![![![-121914, 53825, 19152, 85052, 37773], ![-687827, 304688, 110750, 494766, 217383], ![-3960543, 1775737, 632821, 2854798, 1266915], ![-1022162, 454704, 161660, 723377, 321402], ![-1764714, 782908, 282056, 1260646, 556373]]]
  hmulB := by decide  
  f := ![![![103367230, 15379615, 2694542, -13132832, -11576037]], ![![249244787, 36945428, 6498120, -31732634, -27822459]], ![![336820444, 49988805, 8780927, -42852800, -37638684]], ![![232732517, 34497930, 6067624, -29630321, -25979313]], ![![190256511, 28232867, 4960022, -24207668, -21258109]]]
  g := ![![![-41329, -116992, 19152, 85052, 37773], ![-238430, -678705, 110750, 494766, 217383], ![-1375894, -3917305, 632821, 2854798, 1266915], ![-350256, -993993, 161660, 723377, 321402], ![-608721, -1730537, 282056, 1260646, 556373]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [21, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 70], [0, 1]]
 g := ![![[44, 20], [8, 19], [22, 3], [48], [1], [1]], ![[24, 51], [60, 52], [19, 68], [48], [1], [1]]]
 h' := ![![[70, 70], [45, 37], [35, 44], [22, 28], [65, 41], [50, 70], [0, 1]], ![[0, 1], [8, 34], [62, 27], [65, 43], [24, 30], [51, 1], [70, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [6, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [21, 1, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-540213, 205425, 135861, 398774, 322426]
  a := ![17, -87, -23, -60, -128]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-302401, -676578, 135861, 398774, 322426]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![258098, 38355, 6728, -32814, -28875]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![258098, 38355, 6728, -32814, -28875]] 
 ![![71, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![258098, 38355, 6728, -32814, -28875], ![621807, 92402, 16208, -79058, -69567], ![1498079, 222595, 39043, -190490, -167607], ![-226302, -33638, -5902, 28763, 25314], ![-302950, -45038, -7902, 38500, 33889]]]
  hmulB := by decide  
  f := ![![![-15758, 6349, -222, -3350, 1011]], ![![-4681, 1586, 38, -902, 129]], ![![-2249, 1793, -339, -754, 651]], ![![-8124, 3422, -166, -1773, 606]], ![![-1494, 241, 104, -206, -110]]]
  g := ![![![7301, 38355, 6728, -32814, -28875], ![17592, 92402, 16208, -79058, -69567], ![42402, 222595, 39043, -190490, -167607], ![-6394, -33638, -5902, 28763, 25314], ![-8555, -45038, -7902, 38500, 33889]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32643, 4851, 851, -4150, -3652]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![32643, 4851, 851, -4150, -3652]] 
 ![![71, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![63, 0, 1, 0, 0], ![45, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![32643, 4851, 851, -4150, -3652], ![78644, 11687, 2050, -9998, -8798], ![189460, 28158, 4939, -24088, -21196], ![-28624, -4254, -746, 3639, 3202], ![-38318, -5695, -999, 4872, 4287]]]
  hmulB := by decide  
  f := ![![![-271, 131, 27, 168, 46]], ![![-104, 49, 12, 66, 22]], ![![-355, 169, 38, 228, 62]], ![![-185, 89, 21, 119, 40]], ![![-192, 91, 19, 118, 29]]]
  g := ![![![2444, 4851, 851, -4150, -3652], ![5888, 11687, 2050, -9998, -8798], ![14185, 28158, 4939, -24088, -21196], ![-2143, -4254, -746, 3639, 3202], ![-2869, -5695, -999, 4872, 4287]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2

def I71N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![165433, -82027, 4997, -71762, 50894]] i)))

def SI71N3: IdealEqSpanCertificate' Table ![![165433, -82027, 4997, -71762, 50894]] 
 ![![71, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![53, 0, 0, 0, 1]] where
  M :=![![![165433, -82027, 4997, -71762, 50894], ![-865242, 429017, -26136, 375322, -266180], ![4525282, -2243816, 136701, -1962984, 1392146], ![-1713858, 849804, -51774, 743451, -527252], ![3331456, -1651869, 100637, -1445144, 1024893]]]
  hmulB := by decide  
  f := ![![![75815, -30339, -11023, -50852, -22832]], ![![38997, -15756, -5717, -26306, -11796]], ![![68631, -28697, -10364, -47256, -21094]], ![![11501, -5021, -1803, -8129, -3608]], ![![71045, -29142, -10552, -48358, -21641]]]
  g := ![![![863, -82027, 4997, -71762, 50894], ![-4517, 429017, -26136, 375322, -266180], ![23629, -2243816, 136701, -1962984, 1392146], ![-8947, 849804, -51774, 743451, -527252], ![17387, -1651869, 100637, -1445144, 1024893]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N3 : Nat.card (O ⧸ I71N3) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N3)

lemma isPrimeI71N3 : Ideal.IsPrime I71N3 := prime_ideal_of_norm_prime hp71.out _ NI71N3
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-121914, 53825, 19152, 85052, 37773]] ![![258098, 38355, 6728, -32814, -28875]]
  ![![3443157, -1533930, -549406, -2464158, -1090764]] where
 M := ![![![3443157, -1533930, -549406, -2464158, -1090764]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![3443157, -1533930, -549406, -2464158, -1090764]] ![![32643, 4851, 851, -4150, -3652]]
  ![![75815, -30339, -11023, -50852, -22832]] where
 M := ![![![75815, -30339, -11023, -50852, -22832]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI71N2 : IdealMulLeCertificate' Table 
  ![![75815, -30339, -11023, -50852, -22832]] ![![165433, -82027, 4997, -71762, 50894]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2, I71N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
    exact isPrimeI71N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1 ⊙ MulI71N2)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43266052, 21455292, -1315903, 18754876, -13339673]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-43266052, 21455292, -1315903, 18754876, -13339673]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![42, 21, 2, 1, 0], ![1, 17, 62, 0, 1]] where
  M :=![![![-43266052, 21455292, -1315903, 18754876, -13339673], ![226803493, -112444632, 6799716, -98460680, 69604301], ![-1183222743, 586766915, -36040615, 512821830, -364986341], ![449119504, -222670966, 13491264, -194933833, 137917886], ![-871542654, 432180165, -26459145, 377866856, -268554453]]]
  hmulB := by decide  
  f := ![![![-16022188, 5065870, 255793, -2973826, 233965]], ![![63249, -16057466, 5555628, 4984892, -9155443]], ![![202302293, -16550749, -19657281, 22846134, 24110119]], ![![-4347767, -1830938, 1180086, 187071, -1766339]], ![![171083075, -17823335, -15297910, 20507168, 18205099]]]
  g := ![![![-11200427, -1994831, 10797727, 18754876, -13339673], ![58802024, 10574747, -56325282, -98460680, 69604301], ![-306256894, -54489366, 295444779, 512821830, -364986341], ![116416748, 20908705, -111610274, -194933833, 137917886], ![-225662961, -40241070, 217372373, 377866856, -268554453]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [4, 20, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 9, 62], [12, 63, 11], [0, 1]]
 g := ![![[44, 14, 18], [58, 49], [22, 48], [52, 39, 71], [55, 1], []], ![[7, 63, 47, 5], [3, 37], [52, 12], [22, 58, 11, 40], [52, 27], [33, 48]], ![[2, 44, 37, 11], [49, 8], [32, 12], [18, 67, 4, 15], [19, 8], [11, 48]]]
 h' := ![![[43, 9, 62], [54, 72, 50], [33, 15, 7], [11, 46, 62], [72, 64, 12], [0, 0, 1], [0, 1]], ![[12, 63, 11], [13, 33, 22], [68, 27, 57], [38, 31, 42], [68, 5, 52], [38, 68, 63], [43, 9, 62]], ![[0, 1], [5, 41, 1], [37, 31, 9], [47, 69, 42], [69, 4, 9], [27, 5, 9], [12, 63, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 57], []]
 b := ![[], [7, 13, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [4, 20, 18, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-290810361473, 124304041218, 62849319915, 233037828993, 143819681079]
  a := ![-85, 448, 119, 311, 655]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-140030395346, -98827738986, -127671870753, 233037828993, 143819681079]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16022188, 5065870, 255793, -2973826, 233965]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-16022188, 5065870, 255793, -2973826, 233965]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![51, 46, 1, 0, 0], ![43, 53, 0, 1, 0], ![72, 5, 0, 0, 1]] where
  M :=![![![-16022188, 5065870, 255793, -2973826, 233965], ![63249, -16057466, 5555628, 4984892, -9155443], ![202302293, -16550749, -19657281, 22846134, 24110119], ![-50387910, 23883270, -1950654, -11818125, 5274788], ![-38730736, -7045965, 7302523, -1206382, -10446585]]]
  hmulB := by decide  
  f := ![![![-43266052, 21455292, -1315903, 18754876, -13339673]], ![![226803493, -112444632, 6799716, -98460680, 69604301]], ![![96481771, -47828305, 2871716, -41916038, 29540934]], ![![145332389, -72050122, 4346471, -63108085, 44566300]], ![![-39077821, 19379973, -1194597, 16930336, -12068348]]]
  g := ![![![1122759, 2051265, 255793, -2973826, 233965], ![2213257, -6712855, 5555628, 4984892, -9155443], ![-20732722, -6078240, -19657281, 22846134, 24110119], ![2431371, 9775343, -1950654, -11818125, 5274788], ![5381769, -3106724, 7302523, -1206382, -10446585]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [70, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 72], [0, 1]]
 g := ![![[70, 24], [72], [67], [56, 35], [8], [1]], ![[0, 49], [72], [67], [33, 38], [8], [1]]]
 h' := ![![[64, 72], [51, 30], [28, 46], [22, 33], [33, 20], [3, 64], [0, 1]], ![[0, 1], [0, 43], [52, 27], [17, 40], [72, 53], [11, 9], [64, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [47, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [70, 9, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-547462, 162087, 190701, 433304, 474340]
  a := ![35, -97, -26, -45, -163]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-863805, -465027, 190701, 433304, 474340]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-43266052, 21455292, -1315903, 18754876, -13339673]] ![![-16022188, 5065870, 255793, -2973826, 233965]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![73, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12642, -2008, -891, 1730, 951]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![12642, -2008, -891, 1730, 951]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![9, 42, 1, 0, 0], ![1, 47, 0, 1, 0], ![43, 1, 0, 0, 1]] where
  M :=![![![12642, -2008, -891, 1730, 951], ![-25145, 14732, -1948, -6768, 4239], ![-85461, -18167, 17023, -1838, -24543], ![52198, -13614, -1834, 8795, 888], ![372, 12859, -4501, -3950, 7403]]]
  hmulB := by decide  
  f := ![![![2098070, -1040374, 63379, -910144, 645495]], ![![-10973987, 5441170, -331500, 4760276, -3375927]], ![![-4868753, 2414019, -147074, 2111946, -1497756]], ![![-6777421, 3360414, -204731, 2939899, -2084940]], ![![1537927, -762603, 46458, -667148, 473153]]]
  g := ![![![-278, -593, -891, 1730, 951], ![-2318, 5195, -1948, -6768, 4239], ![10361, -7876, 17023, -1838, -24543], ![275, -4441, -1834, 8795, 888], ![-3462, 4812, -4501, -3950, 7403]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [11, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 78], [0, 1]]
 g := ![![[58, 36], [47, 21], [27, 44], [72, 25], [36], [1]], ![[0, 43], [0, 58], [0, 35], [1, 54], [36], [1]]]
 h' := ![![[73, 78], [36, 6], [19, 69], [77, 26], [41, 74], [68, 73], [0, 1]], ![[0, 1], [0, 73], [0, 10], [0, 53], [71, 5], [25, 6], [73, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [60, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [11, 6, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-536161, 247684, 89144, 380856, 193788]
  a := ![-14, -82, -18, -98, -84]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-127243, -273296, 89144, 380856, 193788]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11168, -6161, 734, 2934, -1693]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![11168, -6161, 734, 2934, -1693]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![11, 70, 1, 0, 0], ![18, 13, 0, 1, 0], ![31, 19, 0, 0, 1]] where
  M :=![![![11168, -6161, 734, 2934, -1693], ![33637, 8348, -7120, 118, 10495], ![-242243, 54005, 11723, -36710, -10141], ![19510, -24042, 5870, 8691, -10190], ![65890, -4076, -6836, 7952, 8025]]]
  hmulB := by decide  
  f := ![![![812193564, 120700453, 21172888, -103257330, -90864235]], ![![1956715123, 290788152, 51009106, -248764978, -218907755]], ![![1906560187, 283334606, 49701629, -242388584, -213296666]], ![![498032933, 74012866, 12983096, -63316899, -55717495]], ![![777242539, 115506315, 20261742, -98813920, -86954103]]]
  g := ![![![35, -804, 734, 2934, -1693], ![-2728, 3871, -7120, 118, 10495], ![7645, -1224, 11723, -36710, -10141], ![1448, -4485, 5870, 8691, -10190], ![-3175, 2767, -6836, 7952, 8025]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P1 : CertificateIrreducibleZModOfList' 79 2 2 6 [54, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 78], [0, 1]]
 g := ![![[28, 40], [40, 44], [3, 8], [59, 67], [42], [1]], ![[62, 39], [30, 35], [73, 71], [33, 12], [42], [1]]]
 h' := ![![[68, 78], [52, 44], [75, 53], [53, 18], [16, 15], [25, 68], [0, 1]], ![[0, 1], [42, 35], [45, 26], [13, 61], [9, 64], [67, 11], [68, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [55, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N1 : CertifiedPrimeIdeal' SI79N1 79 where
  n := 2
  hpos := by decide
  P := [54, 11, 1]
  hirr := P79P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-295458, 141418, 48350, 217228, 103548]
  a := ![17, 62, 14, 81, 55]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-100600, -101702, 48350, 217228, 103548]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N1 B_one_repr
lemma NI79N1 : Nat.card (O ⧸ I79N1) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1908496475, 283621325, 49752205, -242635094, -213512326]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![1908496475, 283621325, 49752205, -242635094, -213512326]] 
 ![![79, 0, 0, 0, 0], ![46, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![76, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![1908496475, 283621325, 49752205, -242635094, -213512326], ![4597882518, 683300655, 119861204, -584543086, -514392956], ![11077176474, 1646148920, 288768903, -1408300880, -1239236302], ![-1673503314, -248686400, -43626274, 212765485, 187214404], ![-2240327616, -332962793, -58402423, 284808860, 250654227]]]
  hmulB := by decide  
  f := ![![![-385894963, 188237537, -16785059, -92161076, 43438160]], ![![-235253704, 105579611, -7053444, -53338878, 21243468]], ![![9898705, 22298955, -8968534, -6048072, 14370690]], ![![-381359554, 190574790, -18164124, -92488723, 45524640]], ![![-44067436, 10457979, 1907613, -7101570, -1340215]]]
  g := ![![![92537272, 283621325, 49752205, -242635094, -213512326], ![222927320, 683300655, 119861204, -584543086, -514392956], ![537127429, 1646148920, 288768903, -1408300880, -1239236302], ![-81155908, -248686400, -43626274, 212765485, 187214404], ![-108598585, -332962793, -58402423, 284808860, 250654227]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![12642, -2008, -891, 1730, 951]] ![![11168, -6161, 734, 2934, -1693]]
  ![![385894963, -188237537, 16785059, 92161076, -43438160]] where
 M := ![![![385894963, -188237537, 16785059, 92161076, -43438160]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![385894963, -188237537, 16785059, 92161076, -43438160]] ![![1908496475, 283621325, 49752205, -242635094, -213512326]]
  ![![79, 0, 0, 0, 0]] where
 M := ![![![-79, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-257615096, 44536789, 16903248, -36367740, -17310319]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-257615096, 44536789, 16903248, -36367740, -17310319]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![0, 0, 0, 83, 0], ![72, 3, 40, 9, 1]] where
  M :=![![![-257615096, 44536789, 16903248, -36367740, -17310319], ![466683289, -296425262, 44129718, 132783558, -91792901], ![1876059869, 313487749, -344088445, 67058646, 490143575], ![-1041056162, 286949456, 31245252, -180137881, -8892278], ![-62578570, -248704716, 94025320, 71642854, -152346261]]]
  hmulB := by decide  
  f := ![![![325524, -133833, -93926, -295304, -241301]], ![![4316467, -1981142, -469060, -2762770, -644611]], ![![12196019, -5128329, -3094813, -10434506, -7643699]], ![![6931996, -3203670, -671008, -4314759, -764332]], ![![7111115, -3023230, -1679792, -5898805, -4046506]]]
  g := ![![![11912384, 1162262, 8545976, 1438857, -17310319], ![85250267, -253573, 44769226, 11553249, -91792901], ![-402581657, -13939072, -240359415, -52340163, 490143575], ![-4829062, 3778630, 4661884, -1206113, -8892278], ![131401834, 2510049, 74552720, 17382641, -152346261]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 4 2 6 [22, 79, 69, 28, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 79, 79, 14], [23, 23, 20, 58], [21, 63, 67, 11], [0, 1]]
 g := ![![[41, 43, 45, 37], [35, 7, 29, 12], [42, 29, 28], [21, 61, 28], [55, 1], []], ![[68, 29, 74, 49, 44, 34], [44, 75, 30, 7, 68, 79], [45, 42, 16], [38, 40, 11], [8, 70, 1, 25, 17, 19], [5, 44, 30]], ![[24, 15, 7, 59, 63, 19], [71, 35, 13, 66, 65, 50], [17, 40, 78], [23, 3, 26], [41, 25, 21, 78, 74, 20], [29, 9, 44]], ![[32, 73, 29, 5, 36, 38], [73, 49, 61, 79, 66, 27], [82, 27, 31], [24, 8, 78], [56, 38, 22, 9, 53, 23], [73, 78, 38]]]
 h' := ![![[11, 79, 79, 14], [60, 2, 3, 28], [79, 78, 68, 57], [16, 69, 14, 32], [35, 32, 27, 51], [0, 0, 1], [0, 1]], ![[23, 23, 20, 58], [66, 64, 49, 11], [29, 3, 28, 68], [43, 0, 82, 4], [76, 31, 6, 29], [11, 43, 12, 23], [11, 79, 79, 14]], ![[21, 63, 67, 11], [24, 53, 29, 15], [2, 22, 43, 74], [25, 20, 74, 24], [38, 72, 32, 62], [57, 63, 10, 7], [23, 23, 20, 58]], ![[0, 1], [49, 47, 2, 29], [48, 63, 27, 50], [21, 77, 79, 23], [36, 31, 18, 24], [80, 60, 60, 53], [21, 63, 67, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [30, 74, 72], []]
 b := ![[], [], [76, 53, 62, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 4
  hpos := by decide
  P := [22, 79, 69, 28, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-605782937847, 269078243762, 99679192153, 438253764807, 201653003645]
  a := ![-1, -46, -11, -45, -55]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-182226496389, -4046756231, -95981216309, -16585822506, 201653003645]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 47458321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-325524, 133833, 93926, 295304, 241301]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-325524, 133833, 93926, 295304, 241301]] 
 ![![83, 0, 0, 0, 0], ![57, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![81, 0, 0, 0, 1]] where
  M :=![![![-325524, 133833, 93926, 295304, 241301], ![-4316467, 1981142, 469060, 2762770, 644611], ![-12196019, 5128329, 3094813, 10434506, 7643699], ![-6931996, 3203670, 671008, 4314759, 764332], ![-3606692, 1382498, 1421292, 3837546, 3925545]]]
  hmulB := by decide  
  f := ![![![257615096, -44536789, -16903248, 36367740, 17310319]], ![![171293701, -27014117, -12139938, 23375634, 12993748]], ![![197766409, -41874696, -10313761, 30301818, 8902278]], ![![18750438, -4530398, -783756, 3046667, 524252]], ![![252161462, -40467171, -17628776, 34628242, 18728700]]]
  g := ![![![-418780, 133833, 93926, 295304, 241301], ![-2509444, 1981142, 469060, 2762770, 644611], ![-14027122, 5128329, 3094813, 10434506, 7643699], ![-3707508, 3203670, 671008, 4314759, 764332], ![-6132109, 1382498, 1421292, 3837546, 3925545]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-257615096, 44536789, 16903248, -36367740, -17310319]] ![![-325524, 133833, 93926, 295304, 241301]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![-83, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-782975933, 492934508, -72516808, -221415200, 151498262]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-782975933, 492934508, -72516808, -221415200, 151498262]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![0, 0, 0, 89, 0], ![16, 6, 70, 63, 1]] where
  M :=![![![-782975933, 492934508, -72516808, -221415200, 151498262], ![-3092152626, -530502409, 571915962, -106245740, -815743862], ![19036874890, -4661365766, -774330309, 3112360296, 497006642], ![-927683706, 1812290454, -511482432, -643212795, 880610086], ![-5616032246, 555768780, 512328446, -664087664, -614335449]]]
  hmulB := by decide  
  f := ![![![-8700937, -1523100, -225364, 996688, 1123114]], ![![-23688038, -2317749, -625350, 3583588, 1866950]], ![![-42807738, -12654850, -1076149, 2446800, 8883814]], ![![4246102, 3013214, 95232, 593453, -2026258]], ![![-33624260, -8272664, -856120, 2715075, 5892193]]]
  g := ![![![-36033125, -4674776, -119970732, -109728154, 151498262], ![111907294, 49033267, 648022318, 576242894, -815743862], ![124547962, -85880962, -399604441, -316843350, 497006642], ![-168735338, -39004158, -698361668, -630580317, 880610086], ![47340842, 47660466, 488941684, 427405007, -614335449]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 4 2 6 [39, 29, 6, 66, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 54, 9, 73], [66, 74, 75, 19], [62, 49, 5, 86], [0, 1]]
 g := ![![[78, 18, 35, 55], [38, 7, 34], [13, 1, 50], [24, 34, 49, 32], [23, 1], []], ![[3, 86, 88, 34, 88, 10], [5, 14, 25], [44, 83, 55], [57, 73, 27, 49, 33, 53], [65, 15, 16, 5, 32, 32], [38, 82, 78]], ![[2, 2, 18, 9, 0, 28], [61, 19, 25], [13, 76, 57], [8, 14, 44, 54, 58, 82], [26, 1, 7, 31, 48, 60], [62, 28, 5]], ![[41, 34, 27, 39, 75, 19], [75, 59, 34], [44, 25, 84], [51, 0, 45, 55, 6, 43], [11, 22, 40, 51, 76, 41], [10, 88, 9]]]
 h' := ![![[73, 54, 9, 73], [80, 17, 29, 77], [7, 74, 67, 52], [43, 74, 79, 53], [82, 6, 11, 78], [0, 0, 1], [0, 1]], ![[66, 74, 75, 19], [28, 77, 45, 12], [32, 12, 65, 84], [71, 35, 27, 77], [54, 32, 84, 46], [20, 24, 6, 49], [73, 54, 9, 73]], ![[62, 49, 5, 86], [56, 11, 88, 63], [11, 62, 69, 5], [47, 22, 17, 71], [21, 9, 4, 86], [69, 25, 24, 36], [66, 74, 75, 19]], ![[0, 1], [59, 73, 16, 26], [15, 30, 66, 37], [29, 47, 55, 66], [45, 42, 79, 57], [72, 40, 58, 4], [62, 49, 5, 86]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [53, 0, 42], []]
 b := ![[], [], [55, 75, 11, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 4
  hpos := by decide
  P := [39, 29, 6, 66, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2288908792599, 941292713547, 676021509057, 2103647556048, 1752958652502]
  a := ![-27, 63, 21, 23, 111]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-340856710479, -107600665185, -1371135777147, -1217221882602, 1752958652502]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 62742241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8700937, 1523100, 225364, -996688, -1123114]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![8700937, 1523100, 225364, -996688, -1123114]] 
 ![![89, 0, 0, 0, 0], ![79, 1, 0, 0, 0], ![78, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![46, 0, 0, 0, 1]] where
  M :=![![![8700937, 1523100, 225364, -996688, -1123114], ![23688038, 2317749, 625350, -3583588, -1866950], ![42807738, 12654850, 1076149, -2446800, -8883814], ![-4246102, -3013214, -95232, -593453, 2026258], ![-17821314, 1983984, -494058, 4470400, -1020927]]]
  hmulB := by decide  
  f := ![![![782975933, -492934508, 72516808, 221415200, -151498262]], ![![729744397, -431587907, 57942830, 197730860, -125310324]], ![![472306156, -379635122, 72254397, 159078936, -138358102]], ![![45613342, -42517174, 9006176, 17178355, -16703406]], ![![467785676, -261019732, 31724098, 121900976, -71399827]]]
  g := ![![![-826431, 1523100, 225364, -996688, -1123114], ![-1213229, 2317749, 625350, -3583588, -1866950], ![-6993510, 12654850, 1076149, -2446800, -8883814], ![1689796, -3013214, -95232, -593453, 2026258], ![-1201556, 1983984, -494058, 4470400, -1020927]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-782975933, 492934508, -72516808, -221415200, 151498262]] ![![8700937, 1523100, 225364, -996688, -1123114]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![-89, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-68822, 30660, 10983, 49256, 21807]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-68822, 30660, 10983, 49256, 21807]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![49, 8, 41, 1, 0], ![83, 23, 61, 0, 1]] where
  M :=![![![-68822, 30660, 10983, 49256, 21807], ![-397691, 177174, 63450, 284604, 125961], ![-2297163, 1023379, 366585, 1644066, 727851], ![-584106, 260224, 93188, 418005, 184992], ![-1014952, 452155, 161979, 726412, 321623]]]
  hmulB := by decide  
  f := ![![![570, 10, 3, -18, -39]], ![![777, 336, -26, -192, -15]], ![![321, 339, 295, -454, -561]], ![![491, 173, 124, -215, -258]], ![![872, 302, 181, -346, -388]]]
  g := ![![![-44251, -8917, -34420, 49256, 21807], ![-255650, -51513, -198855, 284604, 125961], ![-1476990, -297626, -1148856, 1644066, 727851], ![-375471, -75656, -292057, 418005, 184992], ![-652617, -131510, -507628, 726412, 321623]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [40, 82, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 80, 63], [73, 16, 34], [0, 1]]
 g := ![![[7, 76, 88], [49, 27], [83, 44], [27, 24], [32, 72], [1]], ![[37, 43, 4, 30], [81, 50], [22, 35], [85, 16], [88, 66], [17, 64, 73, 78]], ![[82, 94, 46, 20], [41, 48], [10, 72], [47, 49], [19, 85], [89, 62, 48, 19]]]
 h' := ![![[11, 80, 63], [69, 76, 31], [63, 58, 67], [52, 68, 74], [29, 86, 86], [57, 15, 84], [0, 1]], ![[73, 16, 34], [76, 61, 46], [42, 17, 70], [7, 43, 36], [77, 73, 4], [69, 60, 58], [11, 80, 63]], ![[0, 1], [5, 57, 20], [53, 22, 57], [68, 83, 84], [69, 35, 7], [76, 22, 52], [73, 16, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 16], []]
 b := ![[], [29, 60, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [40, 82, 13, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1474429768, 613736500, 380206756, 1281485080, 925132512]
  a := ![-23, 80, 21, 45, 127]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1454156672, -318723628, -1119523348, 1281485080, 925132512]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![570, 10, 3, -18, -39]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![570, 10, 3, -18, -39]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![47, 9, 1, 0, 0], ![50, 32, 0, 1, 0], ![48, 18, 0, 0, 1]] where
  M :=![![![570, 10, 3, -18, -39], ![777, 336, -26, -192, -15], ![321, 339, 295, -454, -561], ![320, -296, -6, 177, 6], ![-178, 57, -89, 42, 167]]]
  hmulB := by decide  
  f := ![![![-68822, 30660, 10983, 49256, 21807]], ![![-397691, 177174, 63450, 284604, 125961]], ![![-93928, 41845, 14988, 67222, 29757]], ![![-172694, 76936, 27554, 123589, 54702]], ![![-118318, 52711, 18879, 84676, 37481]]]
  g := ![![![33, 13, 3, -18, -39], ![127, 72, -26, -192, -15], ![372, 230, 295, -454, -561], ![-88, -62, -6, 177, 6], ![-63, -36, -89, 42, 167]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P1 : CertificateIrreducibleZModOfList' 97 2 2 6 [35, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 96], [0, 1]]
 g := ![![[2, 61], [31], [4], [61], [31], [27, 1]], ![[0, 36], [31], [4], [61], [31], [54, 96]]]
 h' := ![![[27, 96], [25, 35], [72, 82], [42, 2], [25, 35], [25, 15], [0, 1]], ![[0, 1], [0, 62], [55, 15], [96, 95], [0, 62], [42, 82], [27, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [87, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N1 : CertifiedPrimeIdeal' SI97N1 97 where
  n := 2
  hpos := by decide
  P := [35, 70, 1]
  hirr := P97P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-203307, 90490, 40402, 146109, 93817]
  a := ![-1, 51, 12, 47, 64]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-143411, -68426, 40402, 146109, 93817]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N1 B_one_repr
lemma NI97N1 : Nat.card (O ⧸ I97N1) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-68822, 30660, 10983, 49256, 21807]] ![![570, 10, 3, -18, -39]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![97, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0, 0, 0]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]] where
  M :=![![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 5 2 6 [88, 20, 31, 20, 76, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 47, 52, 57, 28], [98, 96, 23, 14, 66], [58, 61, 41, 78, 20], [41, 98, 86, 53, 88], [0, 1]]
 g := ![![[80, 73, 28, 22, 14], [44, 60, 95, 76], [62, 90, 29, 1, 70], [83, 30, 77, 1], [25, 1], []], ![[62, 10, 49, 49, 43, 32, 18, 34], [50, 90, 54, 30], [32, 8, 17, 50, 73, 90, 86, 72], [88, 96, 6, 88], [31, 44, 40, 24], [13, 66, 66, 43, 0, 89, 3, 35]], ![[58, 61, 94, 66, 82, 55, 34, 28], [54, 34, 97, 68], [30, 12, 72, 67, 23, 43, 31, 28], [54, 36, 49, 45], [70, 26, 8, 56], [65, 25, 68, 99, 5, 78, 79, 50]], ![[72, 72, 70, 5, 89, 17, 72, 22], [1, 97, 36, 6], [17, 98, 98, 30, 34, 94, 21, 84], [49, 0, 41, 25], [68, 42, 5, 1], [52, 77, 88, 31, 21, 50, 94, 21]], ![[3, 12, 46, 12, 39, 33, 22, 31], [71, 71, 66, 84], [24, 64, 95, 69, 50, 97, 65, 31], [13, 37, 19, 49], [74, 56, 46, 68], [54, 57, 22, 47, 25, 3, 24, 25]]]
 h' := ![![[30, 47, 52, 57, 28], [71, 54, 9, 43, 69], [99, 12, 55, 88, 50], [48, 27, 37, 55, 75], [22, 18, 13, 75, 100], [0, 0, 0, 1], [0, 1]], ![[98, 96, 23, 14, 66], [21, 92, 92, 12, 14], [49, 26, 19, 44, 38], [34, 89, 6, 9, 57], [100, 53, 76, 97, 47], [0, 36, 96, 100, 78], [30, 47, 52, 57, 28]], ![[58, 61, 41, 78, 20], [38, 71, 38, 74, 79], [12, 59, 62, 50, 88], [96, 95, 75, 86, 79], [0, 69, 86, 99, 67], [10, 1, 78, 74, 37], [98, 96, 23, 14, 66]], ![[41, 98, 86, 53, 88], [7, 85, 40, 86, 71], [87, 99, 28, 17, 62], [6, 46, 72, 68, 61], [51, 16, 95, 18, 96], [50, 79, 31, 10, 100], [58, 61, 41, 78, 20]], ![[0, 1], [95, 1, 23, 88, 70], [92, 6, 38, 3, 65], [77, 46, 12, 85, 31], [98, 46, 33, 14, 94], [34, 86, 98, 17, 88], [41, 98, 86, 53, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 33, 80, 17], [], [], []]
 b := ![[], [23, 75, 69, 100, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 5
  hpos := by decide
  P := [88, 20, 31, 20, 76, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1397103252548004522, -586132201642372202, -358463557184312952, -1200489945848491648, -888404200171566692]
  a := ![79, -177, -62, -63, -317]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![13832705470772322, -5803289125172002, -3549144130537752, -11886039067806848, -8796081189817492]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10510100501 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2219817944, 329888364, 57867971, -282213920, -248342345]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![2219817944, 329888364, 57867971, -282213920, -248342345]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![24, 87, 44, 70, 1]] where
  M :=![![![2219817944, 329888364, 57867971, -282213920, -248342345], ![5347926301, 794757780, 139413990, -679902476, -598299415], ![12884075301, 1914711275, 335872355, -1638000630, -1441408013], ![-1946468126, -289266244, -50742036, 247461707, 217761764], ![-2605831932, -387252489, -67930845, 331290212, 291526809]]]
  hmulB := by decide  
  f := ![![![-79984, -25958, 19033, 1046, -28085]], ![![646767, -133250, -35010, 97952, 31223]], ![![-901249, 721997, -137037, -302802, 262633]], ![![-572064, -15516, 77178, -45279, -103750]], ![![-240447, 177115, -31187, -75976, 61216]]]
  g := ![![![79417808, 212967693, 106649817, 166036410, -248342345], ![191331187, 513075795, 256937750, 400010258, -598299415], ![460950171, 1236089402, 619008009, 963694760, -1441408013], ![-69638354, -186743104, -93517084, -145590891, 217761764], ![-93227916, -250000824, -125195247, -194908606, 291526809]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 4 2 6 [85, 86, 99, 84, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 95, 46, 22], [63, 86, 54, 18], [27, 24, 3, 63], [0, 1]]
 g := ![![[59, 6, 57, 13], [96, 4, 32, 79], [23, 18, 83, 50], [19, 57, 61], [56, 19, 1], []], ![[92, 14, 92, 79, 50, 102], [66, 94, 68, 9, 58, 90], [49, 76, 58, 90, 45, 75], [50, 70, 33], [11, 73, 81], [84, 78, 74, 17, 68, 39]], ![[64, 57, 63, 81, 87, 23], [78, 33, 11, 76, 11, 66], [31, 98, 62, 12, 83, 25], [12, 90, 72], [34, 95, 63], [60, 3, 47, 41, 41, 64]], ![[68, 69, 85, 12, 82, 16], [97, 53, 25, 43, 70, 25], [13, 89, 68, 77, 39, 81], [62, 84, 25], [75, 78, 91], [53, 9, 53, 16, 101, 66]]]
 h' := ![![[32, 95, 46, 22], [80, 60, 93, 61], [2, 101, 67, 39], [2, 33, 11, 87], [81, 58, 50, 24], [0, 0, 0, 1], [0, 1]], ![[63, 86, 54, 18], [16, 50, 72, 23], [38, 79, 2, 64], [55, 2, 59, 86], [44, 65, 101, 62], [84, 92, 70, 94], [32, 95, 46, 22]], ![[27, 24, 3, 63], [12, 11, 15, 78], [73, 10, 9, 55], [5, 17, 52, 37], [60, 27, 88, 22], [13, 20, 87, 28], [63, 86, 54, 18]], ![[0, 1], [68, 85, 26, 44], [39, 16, 25, 48], [16, 51, 84, 99], [41, 56, 70, 98], [37, 94, 49, 83], [27, 24, 3, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [9, 15, 4], []]
 b := ![[], [], [50, 21, 67, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 4
  hpos := by decide
  P := [85, 86, 99, 84, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-936208329617, 382307305190, 286646732050, 874356910810, 751245118226]
  a := ![23, -51, -17, -18, -92]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-184136807447, -630835126024, -318137266698, -502066032670, 751245118226]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 112550881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79984, 25958, -19033, -1046, 28085]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![79984, 25958, -19033, -1046, 28085]] 
 ![![103, 0, 0, 0, 0], ![100, 1, 0, 0, 0], ![94, 0, 1, 0, 0], ![74, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![79984, 25958, -19033, -1046, 28085], ![-646767, 133250, 35010, -97952, -31223], ![901249, -721997, 137037, 302802, -262633], ![572064, 15516, -77178, 45279, 103750], ![-584282, 223161, -3985, -120362, 30465]]]
  hmulB := by decide  
  f := ![![![-2219817944, -329888364, -57867971, 282213920, 248342345]], ![![-2207084667, -327996060, -57536030, 280595092, 246917805]], ![![-2150941379, -319652597, -56072443, 273457370, 240636781]], ![![-1575922910, -234198764, -41082406, 200353091, 176306522]], ![![-104010444, -15457065, -2711427, 13223236, 11636187]]]
  g := ![![![-7940, 25958, -19033, -1046, 28085], ![-95407, 133250, 35010, -97952, -31223], ![382407, -721997, 137037, 302802, -262633], ![22350, 15516, -77178, 45279, 103750], ![-133998, 223161, -3985, -120362, 30465]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![2219817944, 329888364, 57867971, -282213920, -248342345]] ![![79984, 25958, -19033, -1046, 28085]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![-103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)


lemma PB6026I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB6026I2 : PrimesBelowBoundCertificateInterval O 61 103 6026 where
  m := 9
  g := ![3, 4, 2, 3, 2, 2, 2, 1, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB6026I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1, I71N2, I71N3]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![4489, 4489, 67]
    · exact ![5041, 71, 71, 71]
    · exact ![389017, 5329]
    · exact ![6241, 6241, 79]
    · exact ![47458321, 83]
    · exact ![62742241, 89]
    · exact ![912673, 9409]
    · exact ![10510100501]
    · exact ![112550881, 103]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
      exact NI71N3
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
  β := ![I67N0, I67N1, I67N2, I71N0, I71N1, I71N2, I71N3, I73N1, I79N2, I83N1, I89N1, I103N1]
  Il := ![[I67N0, I67N1, I67N2], [I71N0, I71N1, I71N2, I71N3], [I73N1], [I79N2], [I83N1], [I89N1], [], [], [I103N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
