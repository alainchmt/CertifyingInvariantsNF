
import IdealArithmetic.Examples.NF3_1_383732_1.RI3_1_383732_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0]] 
 ![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [56, 42, 119, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 117, 121], [102, 21, 18], [0, 1]]
 g := ![![[66, 62, 54], [71, 111, 64], [52, 137], [19, 27, 107], [69, 6], [20, 1], []], ![[115, 108, 56, 13], [47, 3, 61, 44], [47, 47], [108, 14, 65, 118], [50, 117], [124, 24], [44, 46]], ![[78, 92, 58, 68], [27, 33, 39, 128], [26, 112], [101, 24, 126, 32], [77, 42], [47, 67], [8, 46]]]
 h' := ![![[57, 117, 121], [55, 39, 101], [87, 47, 131], [48, 38, 89], [92, 121, 78], [131, 77, 80], [0, 0, 1], [0, 1]], ![[102, 21, 18], [109, 126, 29], [100, 73, 98], [77, 71, 73], [109, 132, 16], [44, 24, 16], [90, 18, 21], [57, 117, 121]], ![[0, 1], [32, 113, 9], [15, 19, 49], [130, 30, 116], [38, 25, 45], [72, 38, 43], [87, 121, 117], [102, 21, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111, 4], []]
 b := ![[], [108, 131, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [56, 42, 119, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-370574, -5282, 21128]
  a := ![0, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2666, -38, 152]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-773212578689470569563243512983, 191852367894896487877409602750, -52862655952922361694705688893]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-773212578689470569563243512983, 191852367894896487877409602750, -52862655952922361694705688893]] 
 ![![149, 0, 0], ![0, 149, 0], ![57, 16, 1]] where
  M :=![![![-773212578689470569563243512983, 191852367894896487877409602750, -52862655952922361694705688893], ![6872145273879907020311739556090, -1705142129925280121166532760235, 469831791778844740242817430464], ![-18068662552456636403751508801410, 4483263452927911127903727860862, -1235310338146435380923715329771]]]
  hmulB := by decide  
  f := ![![![373772417796267, 159191104727084, 44551103915395]], ![![-5791643509001350, 838296767884713, 566675522012042]], ![![-656696345323199, 155708585158758, 87323446746758]]]
  g := ![![![15033280608235597631107253382, 6964126598266136073776514262, -52862655952922361694705688893], ![-133612529245062034721670160942, -61895642942193261510413500991, 469831791778844740242817430464], ![351302192764363626234229966413, 162739791028663605521363578102, -1235310338146435380923715329771]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [148, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 148], [0, 1]]
 g := ![![[67, 148], [144], [22, 47], [112], [68, 35], [19], [1]], ![[0, 1], [144], [42, 102], [112], [29, 114], [19], [1]]]
 h' := ![![[67, 148], [32, 44], [22, 12], [117, 135], [68, 74], [20, 66], [1, 67], [0, 1]], ![[0, 1], [0, 105], [81, 137], [73, 14], [109, 75], [121, 83], [20, 82], [67, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97]]
 b := ![[], [126, 123]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [148, 82, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-843, -2503, 1287]
  a := ![-1, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-498, -155, 1287]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![373772417796267, 159191104727084, 44551103915395]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![373772417796267, 159191104727084, 44551103915395]] 
 ![![149, 0, 0], ![99, 1, 0], ![44, 0, 1]] where
  M :=![![![373772417796267, 159191104727084, 44551103915395], ![-5791643509001350, 838296767884713, 566675522012042], ![-26486487123522270, 713937933055746, 1404972289896755]]]
  hmulB := by decide  
  f := ![![![-773212578689470569563243512983, 191852367894896487877409602750, -52862655952922361694705688893]], ![![-467623490042803217224492404223, 116028471756170954219443073235, -31970276158123953473376146107]], ![![-349597422918076117211639083038, 86743406981901722110803693838, -23901122148154491916045406987]]]
  g := ![![![-116418761895721, 159191104727084, 44551103915395], ![-763199640926965, 838296767884713, 566675522012042], ![-1067014250010056, 713937933055746, 1404972289896755]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-773212578689470569563243512983, 191852367894896487877409602750, -52862655952922361694705688893]] ![![373772417796267, 159191104727084, 44551103915395]]
  ![![149, 0, 0]] where
 M := ![![![149, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [75, 105, 100, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 106, 77], [87, 44, 74], [0, 1]]
 g := ![![[79, 22, 8], [75, 115, 103], [73, 135, 90], [59, 90], [34, 143, 58], [51, 1], []], ![[59, 34, 102, 60], [34, 41, 74, 33], [62, 133, 57, 112], [121, 4], [107, 109, 109, 23], [134, 124], [93, 40]], ![[55, 60, 3, 118], [150, 92, 9, 42], [32, 87, 76, 124], [90, 85], [38, 101, 46, 40], [119, 62], [96, 40]]]
 h' := ![![[115, 106, 77], [113, 121, 92], [112, 36, 109], [92, 67, 40], [17, 134, 40], [101, 6, 80], [0, 0, 1], [0, 1]], ![[87, 44, 74], [128, 95, 77], [113, 92, 18], [40, 129, 124], [120, 134, 149], [75, 129, 56], [59, 139, 44], [115, 106, 77]], ![[0, 1], [43, 86, 133], [128, 23, 24], [145, 106, 138], [10, 34, 113], [94, 16, 15], [67, 12, 106], [87, 44, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 99], []]
 b := ![[], [8, 16, 85], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [75, 105, 100, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![98301, 27784, -6191]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![651, 184, -41]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def PBC151 : ContainsPrimesAboveP 151 ![I151N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![151, 0, 0]]) timesTableT_eq_Table B_one_repr 151 (by decide) 𝕀

instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-327405727254250827965498006124331, 81237121287579550088284998190174, -22383930103921222828172154373683]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-327405727254250827965498006124331, 81237121287579550088284998190174, -22383930103921222828172154373683]] 
 ![![157, 0, 0], ![0, 157, 0], ![119, 17, 1]] where
  M :=![![![-327405727254250827965498006124331, 81237121287579550088284998190174, -22383930103921222828172154373683], ![2909910913509758967662380068578790, -722017869996727497648193165546067, 198943503654896204608510685823156], ![-7650914853875582543814669696143830, 1898373321559435277393843223367658, -523074366341831293039682479722911]]]
  hmulB := by decide  
  f := ![![![-25536993363107977, -2642274235505300, 87855539159781]], ![![-11421220090771530, -21664741579365743, -7751111628196338]], ![![-18477633893172279, -4603249480909905, -960063323101184]]]
  g := ![![![14880776784155252793547696588178, 2941171548116180497880328806005, -22383930103921222828172154373683], ![-132257108416706301788219054422782, -26140493198280018955368629455667, 198943503654896204608510685823156], ![347738437839505358776481180833647, 68730175473697880631009206233485, -523074366341831293039682479722911]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [14, 141, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 156], [0, 1]]
 g := ![![[111, 101], [10], [58, 101], [152, 90], [98, 113], [99], [1]], ![[0, 56], [10], [104, 56], [22, 67], [22, 44], [99], [1]]]
 h' := ![![[16, 156], [118, 130], [130, 18], [70, 27], [41, 103], [66, 37], [143, 16], [0, 1]], ![[0, 1], [0, 27], [104, 139], [31, 130], [119, 54], [30, 120], [85, 141], [16, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135]]
 b := ![[], [88, 146]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [14, 141, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1924, -2428, -189]
  a := ![1, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![131, 5, -189]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25536993363107977, 2642274235505300, -87855539159781]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![25536993363107977, 2642274235505300, -87855539159781]] 
 ![![157, 0, 0], ![104, 1, 0], ![145, 0, 1]] where
  M :=![![![25536993363107977, 2642274235505300, -87855539159781], ![11421220090771530, 21664741579365743, 7751111628196338], ![-332074430524917470, 39978927628506754, 29415853207562081]]]
  hmulB := by decide  
  f := ![![![327405727254250827965498006124331, -81237121287579550088284998190174, 22383930103921222828172154373683]], ![![198345762553709090068467595976762, -49214284993067170137155711122497, 13560415459572681334531167955668]], ![![351113027425107978336381404994725, -87119464383811911084045655802184, 24004740327454831867035954547178]]]
  g := ![![![-1506499834084554, 2642274235505300, -87855539159781], ![-21437089746826336, 21664741579365743, 7751111628196338], ![-55765488019019883, 39978927628506754, 29415853207562081]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-327405727254250827965498006124331, 81237121287579550088284998190174, -22383930103921222828172154373683]] ![![25536993363107977, 2642274235505300, -87855539159781]]
  ![![157, 0, 0]] where
 M := ![![![-157, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [131, 108, 119, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 83, 130], [148, 79, 33], [0, 1]]
 g := ![![[119, 21, 64], [129, 144, 100], [33, 126], [73, 46], [43, 43], [35, 44, 1], []], ![[162, 80, 96, 92], [108, 25, 111, 117], [67, 57], [69, 87], [44, 1], [6, 27, 25, 79], [58, 111]], ![[148, 7, 72, 155], [129, 102, 106, 91], [152, 160], [36, 64], [73, 47], [7, 127, 89, 115], [155, 111]]]
 h' := ![![[59, 83, 130], [53, 80, 8], [73, 115, 153], [141, 71, 146], [24, 23, 32], [142, 73, 80], [0, 0, 1], [0, 1]], ![[148, 79, 33], [36, 52, 111], [106, 13, 142], [154, 88, 63], [37, 7, 139], [111, 0, 162], [121, 73, 79], [59, 83, 130]], ![[0, 1], [72, 31, 44], [125, 35, 31], [92, 4, 117], [154, 133, 155], [153, 90, 84], [132, 90, 83], [148, 79, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 154], []]
 b := ![[], [79, 134, 59], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [131, 108, 119, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-370499, -5216, 20864]
  a := ![0, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2273, -32, 128]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀

instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![353380865320362916774137606004384914914813, 81220828190330380595716669373362566326170, 15768892668604190474689804624229086770967]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![353380865320362916774137606004384914914813, 81220828190330380595716669373362566326170, 15768892668604190474689804624229086770967]] 
 ![![167, 0, 0], ![0, 167, 0], ![160, 93, 1]] where
  M :=![![![353380865320362916774137606004384914914813, 81220828190330380595716669373362566326170, 15768892668604190474689804624229086770967], ![-2049956046918544761709674601149781280225710, 492924534490491202824078201370229563382181, 275200269908199522736529617368545872520444], ![-12608663711661494239152841619686914902627810, 600949243932082852200580014003286978353502, 768124804398690725560607818738775435902625]]]
  hmulB := by decide  
  f := ![![![-1276923158728063473962426831843525583299511133904982981241115718324521509973785211, 316834902035648722306446110666369203862484047661215928952638298188835268650735448, -87300118335593899312132702711147138367717318450040470839361265943190278027911859]], ![![11349015383627206910577251352449127987803251398505261209116964572614736143628541670, -2815959717462026786638730780465954724310037639866765501944811739718020671015286685, 775904469435758368295072926576813334852017506083566845179192362680125249896382626]], ![![4918031158082832094972666704482790066008748046938558119129180695385108808267554940, -1220280100277577370655495972665907456193166990342851760686048771657785126983501141, 336233781292240933791358634035754231215238544790311632398811184438941966076519657]]]
  g := ![![![-12991868033870105144767851101031550709221, -8295126886166822356589432099879895229783, 15768892668604190474689804624229086770967], ![-275940115163056697003319840599503717865250, -150303596209413559351336384514398422640833, 275200269908199522736529617368545872520444], ![-811428936619473115741617321065215476928430, -424159626138599728293029623525166638087369, 768124804398690725560607818738775435902625]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [34, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [159, 166], [0, 1]]
 g := ![![[69, 48], [151, 127], [82, 65], [94], [93], [32, 64], [1]], ![[19, 119], [137, 40], [63, 102], [94], [93], [21, 103], [1]]]
 h' := ![![[159, 166], [43, 81], [51, 36], [118, 137], [59, 125], [81, 60], [133, 159], [0, 1]], ![[0, 1], [63, 86], [97, 131], [24, 30], [61, 42], [102, 107], [30, 8], [159, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [130, 116]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [34, 8, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-57157, -17083, 7879]
  a := ![1, -1, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7891, -4490, 7879]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1276923158728063473962426831843525583299511133904982981241115718324521509973785211, -316834902035648722306446110666369203862484047661215928952638298188835268650735448, 87300118335593899312132702711147138367717318450040470839361265943190278027911859]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![1276923158728063473962426831843525583299511133904982981241115718324521509973785211, -316834902035648722306446110666369203862484047661215928952638298188835268650735448, 87300118335593899312132702711147138367717318450040470839361265943190278027911859]] 
 ![![167, 0, 0], ![53, 1, 0], ![139, 0, 1]] where
  M :=![![![1276923158728063473962426831843525583299511133904982981241115718324521509973785211, -316834902035648722306446110666369203862484047661215928952638298188835268650735448, 87300118335593899312132702711147138367717318450040470839361265943190278027911859], ![-11349015383627206910577251352449127987803251398505261209116964572614736143628541670, 2815959717462026786638730780465954724310037639866765501944811739718020671015286685, -775904469435758368295072926576813334852017506083566845179192362680125249896382626], ![29839521881007126989260743034178868514319674797452809554726014191933848780967066570, -7403892651909274688902757441508171558577165494558399013875219216712163214059299478, 2040055248026268418343657853889141389458020133783198656765619377037895421118904059]]]
  hmulB := by decide  
  f := ![![![-353380865320362916774137606004384914914813, -81220828190330380595716669373362566326170, -15768892668604190474689804624229086770967]], ![![-99875627635093951061794122856782150959637, -28728313943580846553275818432086500471073, -6652404678707913879611312948818487852585]], ![![-218630398609993719715283147394746037548091, -71201463247832369790450281777848405375396, -17724556199608821566122698571895919144114]]]
  g := ![![![35535667772274812885135479163542761406577595181998812988381614109157737141215662, -316834902035648722306446110666369203862484047661215928952638298188835268650735448, 87300118335593899312132702711147138367717318450040470839361265943190278027911859], ![-315833288368528224008472131275255537914998880034898451091522445300194143543961383, 2815959717462026786638730780465954724310037639866765501944811739718020671015286685, -775904469435758368295072926576813334852017506083566845179192362680125249896382626], ![830408101536211828451128417625876095714039804869361341315518199218030153237019609, -7403892651909274688902757441508171558577165494558399013875219216712163214059299478, 2040055248026268418343657853889141389458020133783198656765619377037895421118904059]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![353380865320362916774137606004384914914813, 81220828190330380595716669373362566326170, 15768892668604190474689804624229086770967]] ![![1276923158728063473962426831843525583299511133904982981241115718324521509973785211, -316834902035648722306446110666369203862484047661215928952638298188835268650735448, 87300118335593899312132702711147138367717318450040470839361265943190278027911859]]
  ![![167, 0, 0]] where
 M := ![![![-167, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-76279813963460321351, 2716479251195740508, 4297415565701662242]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-76279813963460321351, 2716479251195740508, 4297415565701662242]] 
 ![![173, 0, 0], ![0, 173, 0], ![43, 115, 1]] where
  M :=![![![-76279813963460321351, 2716479251195740508, 4297415565701662242], ![-558664023541216091460, -18832475294832790471, 16744268884990546008], ![-911806326196662357500, -108081419717116149116, -2088206409842244463]]]
  hmulB := by decide  
  f := ![![![10688268490397555967533285180619800237, -2652012751855023592778806931555439716, 730730817775871040114280872547984902]], ![![-94995006310863235214856513431238037260, 23570512691114774121912024327847028581, -6494576620013328698107859049570349344]], ![![-59046609995560042261607973376617073693, 14650863496058283606171128629694316395, -4036872543734502312911477155507226269]]]
  g := ![![![-1509067533460299409, -2840961334130031314, 4297415565701662242], ![-7391142113270575548, -11239441601553442667, 16744268884990546008], ![-4751522835684658067, 763365996617005573, -2088206409842244463]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [130, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [171, 172], [0, 1]]
 g := ![![[8, 4], [57], [106, 78], [121, 124], [124], [166, 4], [1]], ![[0, 169], [57], [123, 95], [46, 49], [124], [158, 169], [1]]]
 h' := ![![[171, 172], [169, 171], [60, 24], [13, 50], [91, 41], [45, 132], [43, 171], [0, 1]], ![[0, 1], [0, 2], [12, 149], [86, 123], [9, 132], [127, 41], [47, 2], [171, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [114]]
 b := ![[], [57, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [130, 2, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![129, -1, 3]
  a := ![-1, 1, 0]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![0, -2, 3]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10688268490397555967533285180619800237, 2652012751855023592778806931555439716, -730730817775871040114280872547984902]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-10688268490397555967533285180619800237, 2652012751855023592778806931555439716, -730730817775871040114280872547984902]] 
 ![![173, 0, 0], ![172, 1, 0], ![57, 0, 1]] where
  M :=![![![-10688268490397555967533285180619800237, 2652012751855023592778806931555439716, -730730817775871040114280872547984902], ![94995006310863235214856513431238037260, -23570512691114774121912024327847028581, 6494576620013328698107859049570349344], ![-249766651430289831846388387670969125820, 61973026330349945662788846708407642692, -17075936071101445423804165278276679237]]]
  hmulB := by decide  
  f := ![![![76279813963460321351, -2716479251195740508, -4297415565701662242]], ![![79068161995701684184, -2591918820293841485, -4369362694714892784]], ![![30403212266554339159, -270276864745902080, -1403840929682962447]]]
  g := ![![![-2457704076278826385196381894063123075, 2652012751855023592778806931555439716, -730730817775871040114280872547984902], ![21843539432611818776829923306331890408, -23570512691114774121912024327847028581, 6494576620013328698107859049570349344], ![-57432363145651434084908858963325508395, 61973026330349945662788846708407642692, -17075936071101445423804165278276679237]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-76279813963460321351, 2716479251195740508, 4297415565701662242]] ![![-10688268490397555967533285180619800237, 2652012751855023592778806931555439716, -730730817775871040114280872547984902]]
  ![![173, 0, 0]] where
 M := ![![![-173, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)


lemma PB176I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 175 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 175 (by omega)

def PB176I3 : PrimesBelowBoundCertificateInterval O 137 175 176 where
  m := 7
  g := ![1, 2, 1, 2, 1, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173]
  hP := PB176I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2685619]
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![4330747]
    · exact ![27889, 167]
    · exact ![29929, 173]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
  β := ![I149N1, I157N1, I167N1, I173N1]
  Il := ![[], [I149N1], [], [I157N1], [], [I167N1], [I173N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
