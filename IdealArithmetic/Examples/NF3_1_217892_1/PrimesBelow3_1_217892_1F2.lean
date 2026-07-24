
import IdealArithmetic.Examples.NF3_1_217892_1.RI3_1_217892_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35728209502507, -10688362833468, -13032812023216]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![35728209502507, -10688362833468, -13032812023216]] 
 ![![83, 0, 0], ![0, 83, 0], ![9, 76, 1]] where
  M :=![![![35728209502507, -10688362833468, -13032812023216], ![1037936063477784, 160056865280695, -38064552954376], ![-65571728591400, 245555662210560, 187433055401603]]]
  hmulB := by decide  
  f := ![![![-474059202470170366114859815, 14420822695285675721097732, -30034202304802799308270736]], ![![2313826134384046994602921944, -70386306726679747252317787, 146593340781319652943127864]], ![![2028759870622799547424964163, -61714626006870995476686848, 128532858479811502475047387]]]
  g := ![![![1843656839897, 11804883746156, -13032812023216], ![16632735422496, 36782685419437, -38064552954376], ![-21114087074769, -168666946365196, 187433055401603]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [79, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 82], [0, 1]]
 g := ![![[24, 36], [30, 75], [63], [69], [60, 3], [1]], ![[77, 47], [9, 8], [63], [69], [16, 80], [1]]]
 h' := ![![[13, 82], [37, 77], [47, 65], [25, 48], [74, 61], [4, 13], [0, 1]], ![[0, 1], [42, 6], [62, 18], [68, 35], [37, 22], [7, 70], [13, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [40, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [79, 70, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1183, -2114, -1524]
  a := ![3, -5, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![151, 1370, -1524]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![474059202470170366114859815, -14420822695285675721097732, 30034202304802799308270736]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![474059202470170366114859815, -14420822695285675721097732, 30034202304802799308270736]] 
 ![![83, 0, 0], ![44, 1, 0], ![70, 0, 1]] where
  M :=![![![474059202470170366114859815, -14420822695285675721097732, 30034202304802799308270736], ![-2313826134384046994602921944, 70386306726679747252317787, -146593340781319652943127864], ![3197184129263675858516303880, -97257948399797085121263840, 202558824812713724474347919]]]
  hmulB := by decide  
  f := ![![![-35728209502507, 10688362833468, 13032812023216]], ![![-31445509416724, 3737724089059, 7367569662360]], ![![-29342204055230, 6055779953400, 8733298629199]]]
  g := ![![![-11973720003294648840190259, -14420822695285675721097732, 30034202304802799308270736], ![58442291859450841353181276, 70386306726679747252317787, -146593340781319652943127864], ![-80754022626930278425933030, -97257948399797085121263840, 202558824812713724474347919]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![35728209502507, -10688362833468, -13032812023216]] ![![474059202470170366114859815, -14420822695285675721097732, 30034202304802799308270736]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [27, 10, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 49, 19], [55, 39, 70], [0, 1]]
 g := ![![[78, 78, 71], [39, 88], [22, 88], [49, 62, 32], [6, 85, 1], []], ![[86, 78, 83, 33], [53, 32], [28, 20], [43, 35, 31, 24], [32, 1, 45, 63], [62, 5]], ![[75, 62, 70, 77], [80, 84], [72, 16], [38, 67, 17, 33], [60, 88, 50, 38], [11, 5]]]
 h' := ![![[30, 49, 19], [40, 69, 31], [84, 28, 34], [12, 50, 34], [16, 48, 78], [0, 0, 1], [0, 1]], ![[55, 39, 70], [10, 5, 28], [62, 12, 78], [27, 22, 51], [2, 33, 38], [27, 49, 39], [30, 49, 19]], ![[0, 1], [26, 15, 30], [36, 49, 66], [17, 17, 4], [60, 8, 62], [58, 40, 49], [55, 39, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88, 59], []]
 b := ![[], [84, 65, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [27, 10, 4, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![488610, 179157, 65148]
  a := ![-3, 3, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5490, 2013, 732]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-191603381358012194714700714131315170824191859404, 5828551320138041542866573221617434487405547745, -12139105596948990026255109983405230921507139455]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-191603381358012194714700714131315170824191859404, 5828551320138041542866573221617434487405547745, -12139105596948990026255109983405230921507139455]] 
 ![![97, 0, 0], ![0, 97, 0], ![3, 74, 1]] where
  M :=![![![-191603381358012194714700714131315170824191859404, 5828551320138041542866573221617434487405547745, -12139105596948990026255109983405230921507139455], ![935193133921745138962165432262373142902745782000, -28448460234210189771039674665600096303889542709, 59249519114726229309709659296515068767447565380], ![-1292225289160247552155195300141120823601625346505, 39309334530884411721897111191237864444697682155, -81869428028798377537882760740497730583931560344]]]
  hmulB := by decide  
  f := ![![![177552437885770029103732, 50451309748596525869085, 10185585375386113839335]], ![![-895378278777309931206300, 206679342626926240638967, 282336687740806927535840]], ![![-710904454488170226647727, 152046796889450495359874, 215446037253408111527241]]]
  g := ![![![-1599856335743971387999333857537108021233715887, 9320849128807869108100460948387675491535400695, -12139105596948990026255109983405230921507139455], ![7808706975026458258072540766730184913406217380, -45493947162102589264840767655749641083453704957, 59249519114726229309709659296515068767447565380], ![-10789866031689200201459247607418841565462171809, 62862340295484168551806406247299689975831269563, -81869428028798377537882760740497730583931560344]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [22, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 96], [0, 1]]
 g := ![![[41, 75], [72], [94], [2], [6], [68, 1]], ![[0, 22], [72], [94], [2], [6], [39, 96]]]
 h' := ![![[68, 96], [92, 50], [30, 13], [62, 26], [94, 83], [56, 43], [0, 1]], ![[0, 1], [0, 47], [41, 84], [84, 71], [15, 14], [70, 54], [68, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [35, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [22, 29, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-610677, -1376181, -745789]
  a := ![65, -129, -259]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16770, 554765, -745789]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-177552437885770029103732, -50451309748596525869085, -10185585375386113839335]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-177552437885770029103732, -50451309748596525869085, -10185585375386113839335]] 
 ![![97, 0, 0], ![43, 1, 0], ![58, 0, 1]] where
  M :=![![![-177552437885770029103732, -50451309748596525869085, -10185585375386113839335], ![895378278777309931206300, -206679342626926240638967, -282336687740806927535840], ![3232396769488887162874515, 697085985361633334983035, 25206035365284161027788]]]
  hmulB := by decide  
  f := ![![![191603381358012194714700714131315170824191859404, -5828551320138041542866573221617434487405547745, 12139105596948990026255109983405230921507139455]], ![![75296415097657517873917167787465764974613445076, -2290507696203356665693020349112882336644835158, 4770433211897735482672784226700101658323293105]], ![![127888880494071699439256048657292791045409826721, -3890364031947328053692354206649990357878551045, 8102448996410719577945145770907228082797377822]]]
  g := ![![![26624926114188403978849, -50451309748596525869085, -10185585375386113839335], ![269671318563937526554233, -206679342626926240638967, -282336687740806927535840], ![-290765470641730181247502, 697085985361633334983035, 25206035365284161027788]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-191603381358012194714700714131315170824191859404, 5828551320138041542866573221617434487405547745, -12139105596948990026255109983405230921507139455]] ![![-177552437885770029103732, -50451309748596525869085, -10185585375386113839335]]
  ![![97, 0, 0]] where
 M := ![![![-97, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19430, 591, -1231]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-19430, 591, -1231]] 
 ![![101, 0, 0], ![0, 101, 0], ![2, 38, 1]] where
  M :=![![![-19430, 591, -1231], ![94836, -2885, 6008], ![-131037, 3987, -8302]]]
  hmulB := by decide  
  f := ![![![26, 15, 7]], ![![-576, -13, 76]], ![![-223, -7, 28]]]
  g := ![![![-168, 469, -1231], ![820, -2289, 6008], ![-1133, 3163, -8302]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [64, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 100], [0, 1]]
 g := ![![[4, 30], [1], [34, 17], [76], [71], [47, 1]], ![[0, 71], [1], [25, 84], [76], [71], [94, 100]]]
 h' := ![![[47, 100], [32, 38], [46, 1], [81, 57], [81, 50], [22, 24], [0, 1]], ![[0, 1], [0, 63], [93, 100], [33, 44], [7, 51], [39, 77], [47, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [40, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [64, 54, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15, -2644, -1962]
  a := ![4, -5, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![39, 712, -1962]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26, 15, 7]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![26, 15, 7]] 
 ![![101, 0, 0], ![77, 1, 0], ![84, 0, 1]] where
  M :=![![![26, 15, 7], ![-576, -13, 76], ![-687, -243, -74]]]
  hmulB := by decide  
  f := ![![![-19430, 591, -1231]], ![![-13874, 422, -879]], ![![-17457, 531, -1106]]]
  g := ![![![-17, 15, 7], ![-59, -13, 76], ![240, -243, -74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-19430, 591, -1231]] ![![26, 15, 7]]
  ![![101, 0, 0]] where
 M := ![![![101, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [11, 62, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [87, 48, 97], [12, 54, 6], [0, 1]]
 g := ![![[67, 61, 76], [70, 44, 72], [33, 67, 72], [89, 61], [20, 16], [1]], ![[29, 86, 23, 16], [12, 89, 99, 29], [83, 1, 15, 59], [57, 56], [56, 28], [77, 75, 74, 93]], ![[32, 94, 11, 86], [17, 18, 101, 87], [59, 52, 5, 53], [8, 72], [5, 32], [88, 23, 24, 10]]]
 h' := ![![[87, 48, 97], [54, 49, 30], [49, 58, 81], [67, 90, 22], [4, 51, 79], [92, 41, 99], [0, 1]], ![[12, 54, 6], [28, 6, 90], [14, 96, 9], [0, 4, 30], [3, 40, 46], [1, 56, 53], [87, 48, 97]], ![[0, 1], [43, 48, 86], [65, 52, 13], [76, 9, 51], [24, 12, 81], [39, 6, 54], [12, 54, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 89], []]
 b := ![[], [73, 39, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [11, 62, 4, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1059561, -295404, -61800]
  a := ![3, -5, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10287, -2868, -600]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀

instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151597703, 35962170, 3548098]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![151597703, 35962170, 3548098]] 
 ![![107, 0, 0], ![0, 107, 0], ![78, 63, 1]] where
  M :=![![![151597703, 35962170, 3548098], ![-348675984, 216907037, 208676824], ![-2560230498, -463478922, 44192383]]]
  hmulB := by decide  
  f := ![![![993485498022457, -30221706788238, 62942654164322]], ![![-4849083611240640, 147508527685879, -307215549058072]], ![![-2068224882201756, 62915146810353, -131033179400801]]]
  g := ![![![-1169663, -1752972, 3548098], ![-155378208, -120838625, 208676824], ![-56142396, -30351393, 44192383]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [46, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 106], [0, 1]]
 g := ![![[106, 79], [61, 35], [87], [103, 11], [85], [46, 1]], ![[102, 28], [66, 72], [87], [74, 96], [85], [92, 106]]]
 h' := ![![[46, 106], [83, 20], [1, 28], [77, 27], [90, 15], [24, 37], [0, 1]], ![[0, 1], [40, 87], [5, 79], [35, 80], [31, 92], [14, 70], [46, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [79, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [46, 61, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-144205, -103267, -44181]
  a := ![-22, 43, 67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![30859, 25048, -44181]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-993485498022457, 30221706788238, -62942654164322]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-993485498022457, 30221706788238, -62942654164322]] 
 ![![107, 0, 0], ![52, 1, 0], ![58, 0, 1]] where
  M :=![![![-993485498022457, 30221706788238, -62942654164322], ![4849083611240640, -147508527685879, 307215549058072], ![-6700336266820782, 203823406020042, -424502369955713]]]
  hmulB := by decide  
  f := ![![![-151597703, -35962170, -3548098]], ![![-70414996, -19504111, -3674560]], ![![-58247068, -15161934, -2336281]]]
  g := ![![![10146352247849, 30221706788238, -62942654164322], ![-49523128920204, -147508527685879, 307215549058072], ![68429757734284, 203823406020042, -424502369955713]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![151597703, 35962170, 3548098]] ![![-993485498022457, 30221706788238, -62942654164322]]
  ![![107, 0, 0]] where
 M := ![![![-107, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, 3, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![8, 3, 1]] 
 ![![109, 0, 0], ![10, 1, 0], ![87, 0, 1]] where
  M :=![![![8, 3, 1], ![-84, 5, 16], ![-165, -45, -8]]]
  hmulB := by decide  
  f := ![![![680, -21, 43]], ![![32, -1, 2]], ![![585, -18, 37]]]
  g := ![![![-1, 3, 1], ![-14, 5, 16], ![9, -45, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-947702689375159744425240918663585379110051753, 28828999374154187329455707765272178406885652, -60042066790782881279342960595363472426386186]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-947702689375159744425240918663585379110051753, 28828999374154187329455707765272178406885652, -60042066790782881279342960595363472426386186]] 
 ![![109, 0, 0], ![17, 1, 0], ![52, 0, 1]] where
  M :=![![![-947702689375159744425240918663585379110051753, 28828999374154187329455707765272178406885652, -60042066790782881279342960595363472426386186], ![4625623210932756365129839510907806492444351204, -140710889763302607084758268223407174772760565, 293058129826490886535420167782360015294086284], ![-6391564559748045419972209486771309513157727690, 194430608627195683560618152175005110954847850, -404940020215639306290722728240495011659961197]]]
  hmulB := by decide  
  f := ![![![-46008051023834479906905, 19679752591613035754656, 21064181203652591957922]], ![![-22610114738287288097657, 869879140959588364139, 3982029666096028384374]], ![![-22697347269111751366290, 5482683236987597271238, 7333284902260076246023]]]
  g := ![![![15453135728302099977062807342070533524265815, 28828999374154187329455707765272178406885652, -60042066790782881279342960595363472426386186], ![-75424902881363535910744207834651305795515651, -140710889763302607084758268223407174772760565, 293058129826490886535420167782360015294086284], ![104220148117457540244173062337241689971815056, 194430608627195683560618152175005110954847850, -404940020215639306290722728240495011659961197]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4915038194407020276282, -1010638722571933715099, -2634568988170969993]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![-4915038194407020276282, -1010638722571933715099, -2634568988170969993]] 
 ![![109, 0, 0], ![81, 1, 0], ![101, 0, 1]] where
  M :=![![![-4915038194407020276282, -1010638722571933715099, -2634568988170969993], ![2226773826221203089652, -7915339534264769781663, -6058563197455260350608], ![78648035100427032848205, 12151375791756743311125, -2867415059381443146154]]]
  hmulB := by decide  
  f := ![![![96316441951054279984618303356573068705088102, -2929934330521360941989009626961013891651371, 6102165062429696919205909656322745188791833]], ![![67261676989237826063669721449019875854767670, -2046091950109141304338802029211238903294762, 4261389302282732944636080780621383362978409]], ![![95206833982979793755475221616542279273296713, -2896180192461177945962156364279219661065124, 6031865424708251573544349553540045033655483]]]
  g := ![![![708374218364448427670, -1010638722571933715099, -2634568988170969993], ![11516368431602283035007, -7915339534264769781663, -6058563197455260350608], ![-5651417275544435023774, 12151375791756743311125, -2867415059381443146154]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![8, 3, 1]] ![![-947702689375159744425240918663585379110051753, 28828999374154187329455707765272178406885652, -60042066790782881279342960595363472426386186]]
  ![![-96316441951054279984618303356573068705088102, 2929934330521360941989009626961013891651371, -6102165062429696919205909656322745188791833]] where
 M := ![![![-96316441951054279984618303356573068705088102, 2929934330521360941989009626961013891651371, -6102165062429696919205909656322745188791833]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![-96316441951054279984618303356573068705088102, 2929934330521360941989009626961013891651371, -6102165062429696919205909656322745188791833]] ![![-4915038194407020276282, -1010638722571933715099, -2634568988170969993]]
  ![![109, 0, 0]] where
 M := ![![![-109, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [32, 34, 90, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 8, 53], [85, 104, 60], [0, 1]]
 g := ![![[9, 21, 112], [101, 41], [36, 64], [7, 16], [19, 94, 77], [1]], ![[92, 98, 23, 25], [102, 51], [99, 4], [89, 30], [46, 50, 93, 16], [30, 61, 0, 56]], ![[30, 74, 20, 4], [63, 41], [88, 100], [5, 61], [48, 49, 42, 41], [24, 61, 48, 57]]]
 h' := ![![[51, 8, 53], [67, 9, 15], [19, 27, 43], [43, 108, 8], [70, 82, 4], [81, 79, 23], [0, 1]], ![[85, 104, 60], [111, 62, 3], [18, 112, 27], [94, 30, 2], [111, 13, 16], [46, 14, 25], [51, 8, 53]], ![[0, 1], [26, 42, 95], [11, 87, 43], [62, 88, 103], [30, 18, 93], [106, 20, 65], [85, 104, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 66], []]
 b := ![[], [21, 109, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [32, 34, 90, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21470, 2147, -113]
  a := ![0, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![190, 19, -1]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀

instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18, -17, -15]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![18, -17, -15]] 
 ![![127, 0, 0], ![0, 127, 0], ![75, 35, 1]] where
  M :=![![![18, -17, -15], ![1204, 147, -72], ![291, 339, 202]]]
  hmulB := by decide  
  f := ![![![-426, 13, -27]], ![![2080, -63, 132]], ![![299, -9, 19]]]
  g := ![![![9, 4, -15], ![52, 21, -72], ![-117, -53, 202]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [40, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [111, 126], [0, 1]]
 g := ![![[102, 17], [111, 26], [81, 9], [120, 1], [11, 47], [111, 1]], ![[84, 110], [76, 101], [64, 118], [104, 126], [21, 80], [95, 126]]]
 h' := ![![[111, 126], [5, 12], [62, 36], [26, 124], [68, 1], [5, 89], [0, 1]], ![[0, 1], [67, 115], [121, 91], [74, 3], [52, 126], [105, 38], [111, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [21, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [40, 16, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3338, -4665, -2256]
  a := ![-5, 8, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1306, 585, -2256]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-426, 13, -27]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-426, 13, -27]] 
 ![![127, 0, 0], ![46, 1, 0], ![5, 0, 1]] where
  M :=![![![-426, 13, -27], ![2080, -63, 132], ![-2877, 87, -182]]]
  hmulB := by decide  
  f := ![![![18, -17, -15]], ![![16, -5, -6]], ![![3, 2, 1]]]
  g := ![![![-7, 13, -27], ![34, -63, 132], ![-47, 87, -182]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![18, -17, -15]] ![![-426, 13, -27]]
  ![![127, 0, 0]] where
 M := ![![![127, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4771137247775747575725320606717621674438795591007630051829190, -145137408885922286793769124744073240576935932227776797392927, 302277227352618814355987222303999379309891489008029864243335]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![4771137247775747575725320606717621674438795591007630051829190, -145137408885922286793769124744073240576935932227776797392927, 302277227352618814355987222303999379309891489008029864243335]] 
 ![![131, 0, 0], ![0, 131, 0], ![118, 91, 1]] where
  M :=![![![4771137247775747575725320606717621674438795591007630051829190, -145137408885922286793769124744073240576935932227776797392927, 302277227352618814355987222303999379309891489008029864243335], ![-23287348915732422946179465090223805105017664278170775816194276, 708398292886554943072166564837409400989289926227941288730389, -1475378908020771349474589193072438202081398571382720512844232], ![32177846580432636560477110069013669937383515455320650829438421, -978846139542501887678655503807115526865792214338947209474891, 2038639792021404005752986633165774362493752565382885004181694]]]
  hmulB := by decide  
  f := ![![![-260953486158218442011545518166, 143491853738814634473510090663, 142538741704254899984770567479]], ![![-11405005560409511467759124444688, -1540942825392833338408262055925, 575873639024378006871519409020]], ![![-8167978692961597504682651248289, -964110757937189134662768798368, 513364489020168550478663525260]]]
  g := ![![![-235859355571246355101382989504994695298690077190380869686140, -211086756473085758726630582858076463799824896427164079721652, 302277227352618814355987222303999379309891489008029864243335], ![1151201238402432032762000455666594677409063871335803394652100, 1030289152082265249963815138430757906796920304748515327920271, -1475378908020771349474589193072438202081398571382720512844232], ![-1590699609756435390216605440034715304098315169922593737893141, -1423626467278551651993896481846508263464101340947950248778695, 2038639792021404005752986633165774362493752565382885004181694]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [75, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 130], [0, 1]]
 g := ![![[116, 7], [93, 9], [129], [7], [52], [34], [1]], ![[0, 124], [0, 122], [129], [7], [52], [34], [1]]]
 h' := ![![[77, 130], [99, 111], [100, 128], [122, 28], [75, 111], [62, 107], [56, 77], [0, 1]], ![[0, 1], [0, 20], [0, 3], [51, 103], [107, 20], [48, 24], [90, 54], [77, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [79, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [75, 54, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3430, -8740, -5480]
  a := ![5, -10, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4910, 3740, -5480]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![260953486158218442011545518166, -143491853738814634473510090663, -142538741704254899984770567479]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![260953486158218442011545518166, -143491853738814634473510090663, -142538741704254899984770567479]] 
 ![![131, 0, 0], ![111, 1, 0], ![74, 0, 1]] where
  M :=![![![260953486158218442011545518166, -143491853738814634473510090663, -142538741704254899984770567479], ![11405005560409511467759124444688, 1540942825392833338408262055925, -575873639024378006871519409020], ![1357191414033953389984617915663, 3004750920204069713545056195267, 1973324610678396710806271374282]]]
  hmulB := by decide  
  f := ![![![-4771137247775747575725320606717621674438795591007630051829190, 145137408885922286793769124744073240576935932227776797392927, -302277227352618814355987222303999379309891489008029864243335]], ![![-3864953325094469908086497116453680921814417147508978320128594, 117571405293517701458291651005761223687409149244696818487668, -244865597924579519420152614371538113750508066477164842886763]], ![![-2940778648212503489802678129512348655311865566335002096677851, 89458125168708023743645578128767445263809551138888780279019, -186314157374925162351878176211158232300959715663947289757164]]]
  g := ![![![204094779673904621888886928055, -143491853738814634473510090663, -142538741704254899984770567479], ![-893320601300694783107370438897, 1540942825392833338408262055925, -575873639024378006871519409020], ![-3650352533731443827581532072182, 3004750920204069713545056195267, 1973324610678396710806271374282]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![4771137247775747575725320606717621674438795591007630051829190, -145137408885922286793769124744073240576935932227776797392927, 302277227352618814355987222303999379309891489008029864243335]] ![![260953486158218442011545518166, -143491853738814634473510090663, -142538741704254899984770567479]]
  ![![131, 0, 0]] where
 M := ![![![-131, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)


lemma PB133I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 132 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 132 (by omega)

def PB133I2 : PrimesBelowBoundCertificateInterval O 79 132 133 where
  m := 10
  g := ![2, 1, 2, 2, 1, 2, 3, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131]
  hP := PB133I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![109, 109, 109]
    · exact ![1442897]
    · exact ![16129, 127]
    · exact ![17161, 131]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
  β := ![I83N1, I97N1, I101N1, I107N1, I109N0, I109N1, I109N2, I127N1, I131N1]
  Il := ![[I83N1], [], [I97N1], [I101N1], [], [I107N1], [I109N0, I109N1, I109N2], [], [I127N1], [I131N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
