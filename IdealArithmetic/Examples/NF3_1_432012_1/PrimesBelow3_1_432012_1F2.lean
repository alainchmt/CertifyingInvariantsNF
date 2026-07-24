
import IdealArithmetic.Examples.NF3_1_432012_1.RI3_1_432012_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [82, 22, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 7, 45], [43, 75, 38], [0, 1]]
 g := ![![[29, 26, 30], [11, 46, 78], [48, 78], [2, 7], [16, 72, 1], []], ![[33, 49, 20, 42], [74, 21, 67, 35], [48, 40], [51, 69], [77, 15, 58, 58], [18, 33]], ![[21, 79, 9, 77], [55, 54, 5, 41], [4, 49], [57, 33], [20, 21, 74, 36], [25, 33]]]
 h' := ![![[29, 7, 45], [11, 11, 69], [46, 5, 24], [9, 50, 24], [16, 52, 67], [0, 0, 1], [0, 1]], ![[43, 75, 38], [7, 56, 26], [57, 71, 33], [80, 54, 66], [64, 8, 61], [29, 43, 75], [29, 7, 45]], ![[0, 1], [61, 16, 71], [2, 7, 26], [74, 62, 76], [73, 23, 38], [48, 40, 7], [43, 75, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 66], []]
 b := ![[], [56, 76, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [82, 22, 11, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23489, -14110, -913]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-283, -170, -11]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-75905170465, 5183557923, -1784681943]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-75905170465, 5183557923, -1784681943]] 
 ![![89, 0, 0], ![0, 89, 0], ![68, 41, 1]] where
  M :=![![![-75905170465, 5183557923, -1784681943], ![144559237383, -9871938574, 3398875980], ![-275308954380, 18800826123, -6473062594]]]
  hmulB := by decide  
  f := ![![![-43544, -31857, -4722]], ![![382482, 131170, -36579]], ![![176221, 55591, -19396]]]
  g := ![![![510710131, 880399074, -1784681943], ![-972632913, -1676694986, 3398875980], ![1852351708, 3193217893, -6473062594]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [55, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 88], [0, 1]]
 g := ![![[68, 34], [87], [40], [55, 39], [34, 4], [1]], ![[0, 55], [87], [40], [66, 50], [26, 85], [1]]]
 h' := ![![[87, 88], [74, 37], [26, 40], [1, 60], [88, 67], [34, 87], [0, 1]], ![[0, 1], [0, 52], [35, 49], [59, 29], [43, 22], [38, 2], [87, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [75, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [55, 2, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![297, -618, -332]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![257, 146, -332]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43544, -31857, -4722]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-43544, -31857, -4722]] 
 ![![89, 0, 0], ![47, 1, 0], ![16, 0, 1]] where
  M :=![![![-43544, -31857, -4722], ![382482, 131170, -36579], ![2962899, 1735905, 94591]]]
  hmulB := by decide  
  f := ![![![-75905170465, 5183557923, -1784681943]], ![![-38460491848, 2626463863, -904282869]], ![![-16739232380, 1143120819, -393572738]]]
  g := ![![![17183, -31857, -4722], ![-58396, 131170, -36579], ![-900428, 1735905, 94591]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-75905170465, 5183557923, -1784681943]] ![![-43544, -31857, -4722]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-212518144891282, -83261093468013, 14874437515808]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-212518144891282, -83261093468013, 14874437515808]] 
 ![![97, 0, 0], ![0, 97, 0], ![83, 81, 1]] where
  M :=![![![-212518144891282, -83261093468013, 14874437515808], ![-1204829438780448, -762872332976178, -68386655952205], ![5539319132128605, 1325476831451137, -831258988928383]]]
  hmulB := by decide  
  f := ![![![-7472055796250331743937649147, 510266083146607949751971539, -175682934047363119193677737]], ![![14230317657836412654687896697, -971787236497896333771572878, 334583149099244830558293802]], ![![5210039836277660402140958302, -355793197051513291567554014, 122498427460917947205497595]]]
  g := ![![![-14918520192818, -13279283837613, 14874437515808], ![46095494899511, 49241719578891, -68386655952205], ![768389847558602, 707808813759280, -831258988928383]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [23, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [89, 96], [0, 1]]
 g := ![![[13, 24], [22], [22], [81], [32], [89, 1]], ![[15, 73], [22], [22], [81], [32], [81, 96]]]
 h' := ![![[89, 96], [49, 11], [78, 64], [83, 33], [43, 88], [87, 41], [0, 1]], ![[0, 1], [58, 86], [51, 33], [13, 64], [18, 9], [50, 56], [89, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [28, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [23, 8, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3688, -164, 83]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33, -71, 83]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3025235562516187522642, 2910430081894545248792, 694123925086292785239]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![3025235562516187522642, 2910430081894545248792, 694123925086292785239]] 
 ![![97, 0, 0], ![15, 1, 0], ![66, 0, 1]] where
  M :=![![![3025235562516187522642, 2910430081894545248792, 694123925086292785239], ![-56224037931989715604359, -22657349665676645531201, 3604554006980838034031], ![-291968874565447880756511, -189592536190280722863506, -19052795658695807497170]]]
  hmulB := by decide  
  f := ![![![1115082389366092825698304025555319010750173856, -76148885758204595013199184631658923882669294, 26217810895722628451527709656806774024382591]], ![![150542197504514015267018720630190066652346577, -10280514434522818063981536095066139034969293, 3539547304879973816610764637909788252654146]], ![![800410873835290368944159331542413184000337087, -54659993532816530027454083441456784819325312, 18819255984325433858050887944617147501020436]]]
  g := ![![![-891169017748425928196, 2910430081894545248792, 694123925086292785239], ![471501470024996465130, -22657349665676645531201, 3604554006980838034031], ![39272202904769961412467, -189592536190280722863506, -19052795658695807497170]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-212518144891282, -83261093468013, 14874437515808]] ![![3025235562516187522642, 2910430081894545248792, 694123925086292785239]]
  ![![97, 0, 0]] where
 M := ![![![-304515353485108225206775477034964265, -1552125826614551955448742087696160579, -731032655496455195898209206123600161]]]
 hmul := by decide  
 g := ![![![![-3139333541083589950585314196236745, -16001297181593319128337547295836707, -7536419128829435009259888722923713]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-681255258542613658, -269106475892969527, 46525800908969950]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-681255258542613658, -269106475892969527, 46525800908969950]] 
 ![![101, 0, 0], ![0, 101, 0], ![15, 34, 1]] where
  M :=![![![-681255258542613658, -269106475892969527, 46525800908969950], ![-3768589873626565950, -2402709892174501808, -222580674983999577], ![18029034673703965737, 4466895100781418399, -2625290567158501385]]]
  hmulB := by decide  
  f := ![![![-72297585565928598848786270636921003, 4937196243394752647844866809150345, -1699860427050951429710619896381779]], ![![137688694591127065806560211606924099, -9402749765043395949493334470795180, 3237335816343801218134246912768566]], ![![33017105262233102534875040942052975, -2254735435387601503262448455794988, 776297994071538368708376327033445]]]
  g := ![![![-13654873981952108, -18326571354435127, 46525800908969950], ![-4256235137292795, 51138941161202810, -222580674983999577], ![568399932485955312, 927987865189806589, -2625290567158501385]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [58, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 100], [0, 1]]
 g := ![![[17, 54], [30], [59, 70], [21], [68], [24, 1]], ![[0, 47], [30], [22, 31], [21], [68], [48, 100]]]
 h' := ![![[24, 100], [20, 16], [12, 38], [64, 26], [75, 83], [22, 13], [0, 1]], ![[0, 1], [0, 85], [15, 63], [82, 75], [47, 18], [31, 88], [24, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [40, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [58, 77, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-107, -761, -566]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![83, 183, -566]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1039729433838603440, 975677118814991294, 225645767515414975]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![1039729433838603440, 975677118814991294, 225645767515414975]] 
 ![![101, 0, 0], ![66, 1, 0], ![88, 0, 1]] where
  M :=![![![1039729433838603440, 975677118814991294, 225645767515414975], ![-18277307168748612975, -7309163964231750635, 1201322886330406269], ![-97307153792762907789, -62726253962973644928, -6107841077901344366]]]
  hmulB := by decide  
  f := ![![![119997696365344502842501156222165426042, -8194632933775393865764343265038047196, 2821385165106446577632006151462781211]], ![![76151641205337772423929542696974582581, -5200389389829406095745838879945233601, 1790476961666896305302772959237309841]], ![![108861686627846544361176446076734198381, -7434155733713918646678794380094540494, 2559555366505983475382189433992000018]]]
  g := ![![![-823879088607003364, 975677118814991294, 225645767515414975], ![3548624757163080963, -7309163964231750635, 1201322886330406269], ![45347679431869464967, -62726253962973644928, -6107841077901344366]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-681255258542613658, -269106475892969527, 46525800908969950]] ![![1039729433838603440, 975677118814991294, 225645767515414975]]
  ![![101, 0, 0]] where
 M := ![![![-317072687649442585009116733819911245, -1616131015340925231962092276879507407, -761178332011772935935248761015295013]]]
 hmul := by decide  
 g := ![![![![-3139333541083589950585314196236745, -16001297181593319128337547295836707, -7536419128829435009259888722923713]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251375925451, 100996284034, -16275484696]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![251375925451, 100996284034, -16275484696]] 
 ![![103, 0, 0], ![0, 103, 0], ![60, 44, 1]] where
  M :=![![![251375925451, 100996284034, -16275484696], ![1318314260376, 853568859203, 84720799338], ![-6862384746378, -1816355315130, 938289658541]]]
  hmulB := by decide  
  f := ![![![9269688423518953988221, -633026269187137260038, 217948862315230800260]], ![![-17653857847533694821060, 1205580517855414378601, -415077406871906459778]], ![![-1815215241977872908654, 123960901370260594630, -42679330606471148503]]]
  g := ![![![11921407837, 7933180686, -16275484696], ![-36552754368, -27904333123, 84720799338], ![-613201594746, -418457284378, 938289658541]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [93, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 102], [0, 1]]
 g := ![![[70, 72], [5, 64], [58, 49], [93], [79], [82, 1]], ![[0, 31], [0, 39], [59, 54], [93], [79], [61, 102]]]
 h' := ![![[82, 102], [50, 22], [65, 8], [18, 96], [85, 89], [99, 39], [0, 1]], ![[0, 1], [0, 81], [0, 95], [62, 7], [70, 14], [1, 64], [82, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [40, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [93, 21, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-150, -213, -54]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![30, 21, -54]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9269688423518953988221, 633026269187137260038, -217948862315230800260]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-9269688423518953988221, 633026269187137260038, -217948862315230800260]] 
 ![![103, 0, 0], ![58, 1, 0], ![35, 0, 1]] where
  M :=![![![-9269688423518953988221, 633026269187137260038, -217948862315230800260], ![17653857847533694821060, -1205580517855414378601, 415077406871906459778], ![-33621269956624423242018, 2295993793273155809274, -790503110983507918823]]]
  hmulB := by decide  
  f := ![![![-251375925451, -100996284034, 16275484696]], ![![-154350659578, -65158770225, 8342304010]], ![![-18793909169, -16684608020, -3579103827]]]
  g := ![![![-372398076265435311275, 633026269187137260038, -217948862315230800260], ![709221540219718472696, -1205580517855414378601, 415077406871906459778], ![-1350692243514996922535, 2295993793273155809274, -790503110983507918823]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![251375925451, 100996284034, -16275484696]] ![![-9269688423518953988221, 633026269187137260038, -217948862315230800260]]
  ![![103, 0, 0]] where
 M := ![![![-103, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-110775924523674879935216339444134, 7564878884069045514740847432403, -2604562917195384913700174261276]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-110775924523674879935216339444134, 7564878884069045514740847432403, -2604562917195384913700174261276]] 
 ![![107, 0, 0], ![0, 107, 0], ![58, 88, 1]] where
  M :=![![![-110775924523674879935216339444134, 7564878884069045514740847432403, -2604562917195384913700174261276], ![210969596292826178009714115163356, -14407096587445638128309891776922, 4960315966873660601040673171127], ![-401785593316766508684294526861287, 27437905518500735771209207831657, -9446780620571977527269218605795]]]
  hmulB := by decide  
  f := ![![![2429231941799107, 1493002360518121, 114184509824713]], ![![-9248945295801753, -1795594921715274, 1607186870342834]], ![![-7506484765457716, -1309654913078315, 1381932131856358]]]
  g := ![![![376530137136985467844801567382, 2212770239226756242246319461913, -2604562917195384913700174261276], ![-717090932578001278977989988430, -4214157959554465149718590007814, 4960315966873660601040673171127], ![1365679277349609232685235067989, 8025743926437708020288789206931, -9446780620571977527269218605795]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [51, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 106], [0, 1]]
 g := ![![[72, 79], [34, 92], [12], [91, 11], [48], [73, 1]], ![[61, 28], [9, 15], [12], [38, 96], [48], [39, 106]]]
 h' := ![![[73, 106], [85, 20], [25, 29], [67, 36], [69, 15], [22, 35], [0, 1]], ![[0, 1], [47, 87], [2, 78], [20, 71], [94, 92], [9, 72], [73, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [42, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [51, 34, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3073, -840, 399]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-245, -336, 399]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2429231941799107, 1493002360518121, 114184509824713]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![2429231941799107, 1493002360518121, 114184509824713]] 
 ![![107, 0, 0], ![18, 1, 0], ![104, 0, 1]] where
  M :=![![![2429231941799107, 1493002360518121, 114184509824713], ![-9248945295801753, -1795594921715274, 1607186870342834], ![-130182136497769554, -68714859498486611, -188408051372440]]]
  hmulB := by decide  
  f := ![![![-110775924523674879935216339444134, 7564878884069045514740847432403, -2604562917195384913700174261276]], ![![-16663523786292725802095140138608, 1137950685287824122775937962676, -391792677968628671453854799363]], ![![-111425063025971532915390596533189, 7609208499641882890693993839267, -2619825458027028117309227493257]]]
  g := ![![![-339439248311189, 1493002360518121, 114184509824713], ![-1346501600192351, -1795594921715274, 1607186870342834], ![10525979175866572, -68714859498486611, -188408051372440]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-110775924523674879935216339444134, 7564878884069045514740847432403, -2604562917195384913700174261276]] ![![2429231941799107, 1493002360518121, 114184509824713]]
  ![![107, 0, 0]] where
 M := ![![![107, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [83, 3, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 39, 24], [18, 69, 85], [0, 1]]
 g := ![![[65, 96, 73], [20, 28], [36, 31, 73], [51, 65, 31], [103, 97], [1]], ![[28, 65, 9, 101], [31, 16], [27, 69, 105, 85], [6, 41, 93, 77], [0, 3], [98, 36, 60, 90]], ![[19, 47, 77, 17], [52, 22], [30, 88, 84, 86], [77, 54, 103, 70], [4, 31], [30, 53, 65, 19]]]
 h' := ![![[55, 39, 24], [38, 30, 89], [64, 41, 79], [18, 91, 20], [84, 95, 24], [26, 106, 73], [0, 1]], ![[18, 69, 85], [91, 91, 103], [87, 35, 4], [80, 50, 76], [75, 73, 12], [82, 99, 60], [55, 39, 24]], ![[0, 1], [28, 97, 26], [86, 33, 26], [26, 77, 13], [56, 50, 73], [72, 13, 85], [18, 69, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 58], []]
 b := ![[], [84, 77, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [83, 3, 36, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27250, 8066, -2507]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![250, 74, -23]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def PBC109 : ContainsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![109, 0, 0]]) timesTableT_eq_Table B_one_repr 109 (by decide) 𝕀

instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2941767541442195467, 3517143292628061147, 1035709812234825517]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![2941767541442195467, 3517143292628061147, 1035709812234825517]] 
 ![![113, 0, 0], ![8, 1, 0], ![49, 0, 1]] where
  M :=![![![2941767541442195467, 3517143292628061147, 1035709812234825517], ![-83892494791020866877, -35379495511246348662, 4552853104862886664], ![-368781101493893819784, -252348059670947673445, -30826642406383461998]]]
  hmulB := by decide  
  f := ![![![-2239534703622439142655628716037652584156, 152937642925764412567820824956374504359, -52655927413005152536240628446839251862]], ![![-120806615119699962706279104638117179402, 8249873929777582316175585275631820970, -2840404458329928851843759566948484623]], ![![-1043009021540115204006051354009887894477, 71227001326051158850356142090296688248, -24523222274918068257158726202568038531]]]
  g := ![![![-672081058399015434, 3517143292628061147, 1035709812234825517], ![-211914449905588709, -35379495511246348662, 4552853104862886664], ![27969104900765285006, -252348059670947673445, -30826642406383461998]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![121155074542994678778814667, -8273670195478562326076294, 2848597434339501576606528]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![121155074542994678778814667, -8273670195478562326076294, 2848597434339501576606528]] 
 ![![113, 0, 0], ![22, 1, 0], ![81, 0, 1]] where
  M :=![![![121155074542994678778814667, -8273670195478562326076294, 2848597434339501576606528], ![-230736392181499627705128768, 15756969472433120444373131, -5425072761139060749469766], ![439430893652263920707051046, -30008700019354379974747426, 10331896711294059694903365]]]
  hmulB := by decide  
  f := ![![![-34686225836501, -16277035467618, 1016559928036]], ![![-7481755067026, -3808794012933, 62865866170]], ![![-13924652867703, -7399501168880, -46177562323]]]
  g := ![![![641056873115251524312959, -8273670195478562326076294, 2848597434339501576606528], ![-1220874574537737670568908, 15756969472433120444373131, -5425072761139060749469766], ![2325120889055234025347981, -30008700019354379974747426, 10331896711294059694903365]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15209690073284, 1038668499165, -357610147848]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-15209690073284, 1038668499165, -357610147848]] 
 ![![113, 0, 0], ![82, 1, 0], ![56, 0, 1]] where
  M :=![![![-15209690073284, 1038668499165, -357610147848], ![28966421975688, -1978114602908, 681058351317], ![-55165726456677, 3767262976959, -1297056251591]]]
  hmulB := by decide  
  f := ![![![-9921625, -5987283, -408321]], ![![-6907073, -4298858, -352902]], ![![-332452, -580323, -213056]]]
  g := ![![![-711100342702, 1038668499165, -357610147848], ![1354270369384, -1978114602908, 681058351317], ![-2579169384763, 3767262976959, -1297056251591]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![2941767541442195467, 3517143292628061147, 1035709812234825517]] ![![121155074542994678778814667, -8273670195478562326076294, 2848597434339501576606528]]
  ![![-9921625, -5987283, -408321]] where
 M := ![![![-9921625, -5987283, -408321]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![-9921625, -5987283, -408321]] ![![-15209690073284, 1038668499165, -357610147848]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-266385023695, 72362249854, 111440735214]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-266385023695, 72362249854, 111440735214]] 
 ![![127, 0, 0], ![5, 1, 0], ![102, 0, 1]] where
  M :=![![![-266385023695, 72362249854, 111440735214], ![-9026699552334, -4389692226613, 183802985068], ![-14888041790508, -15827409999850, -4205889241545]]]
  hmulB := by decide  
  f := ![![![-21371684513472876266476885, 1459470598761769782733470, -502490926626335064230254]], ![![-520918563075836544328613, 35573486342601338769369, -12247834338553075611402]], ![![-17775017116670894420310258, 1213854474499390342179886, -417926102929521423015277]]]
  g := ![![![-94450009959, 72362249854, 111440735214], ![-45875140915, -4389692226613, 183802985068], ![3883855990916, -15827409999850, -4205889241545]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4288361264, -2541085785, -151933418]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-4288361264, -2541085785, -151933418]] 
 ![![127, 0, 0], ![11, 1, 0], ![6, 0, 1]] where
  M :=![![![-4288361264, -2541085785, -151933418], ![12306606858, 1333175202, -2693019203], ![218134555443, 111948317369, -1359844001]]]
  hmulB := by decide  
  f := ![![![299666058117533773705, -20464170757979563027, 7045746680708029791]], ![![21461583922484418092, -1465609822097941117, 504604641027691295]], ![![22715659046962179798, -1551250510442370563, 534090448333175724]]]
  g := ![![![193505377, -2541085785, -151933418], ![108659802, 1333175202, -2693019203], ![-7914471430, 111948317369, -1359844001]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-104473724026736, -61919536892550, -3708361768443]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![-104473724026736, -61919536892550, -3708361768443]] 
 ![![127, 0, 0], ![110, 1, 0], ![92, 0, 1]] where
  M :=![![![-104473724026736, -61919536892550, -3708361768443], ![300377303243883, 32735661405655, -65627898660993], ![5315859791540433, 2728609553700624, -32892237255338]]]
  hmulB := by decide  
  f := ![![![177996162134016673425356423242, -12155343448162119837052540332, 4185044767541314848118047315]], ![![151500702429692815544028698615, -10345970657975158724651895779, 3562083667314360852787800879]], ![![134025520546927709915247912383, -9152591907234580654455270090, 3151207288725733740810350650]]]
  g := ![![![55494839502760, -61919536892550, -3708361768443], ![21552923034907, 32735661405655, -65627898660993], ![-2297677994393993, 2728609553700624, -32892237255338]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-266385023695, 72362249854, 111440735214]] ![![-4288361264, -2541085785, -151933418]]
  ![![26341964211383871519014, 13248981547686099728049, -305942156522900958066]] where
 M := ![![![26341964211383871519014, 13248981547686099728049, -305942156522900958066]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![26341964211383871519014, 13248981547686099728049, -305942156522900958066]] ![![-104473724026736, -61919536892550, -3708361768443]]
  ![![127, 0, 0]] where
 M := ![![![-398695359717615923724334902922066615, -2032164742062351529298868506571261789, -957125229361338246176005867811311551]]]
 hmul := by decide  
 g := ![![![![-3139333541083589950585314196236745, -16001297181593319128337547295836707, -7536419128829435009259888722923713]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4432259974, 2279394229, -25149772]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![4432259974, 2279394229, -25149772]] 
 ![![131, 0, 0], ![0, 131, 0], ![79, 124, 1]] where
  M :=![![![4432259974, 2279394229, -25149772], ![2037131532, 5362801538, 2254244457], ![-182593801017, -81369913377, 7617045995]]]
  hmulB := by decide  
  f := ![![![1712033451707443829, -116914625297246281, 40253320931320519]], ![![-3260518995436962039, 222660577248584626, -76661304365925762]], ![![-2006443870959200333, 137019888904155180, -47175497060441333]]]
  g := ![![![49000702, 41205847, -25149772], ![-1343879241, -2092851230, 2254244457], ![-5987331562, -7831172647, 7617045995]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [80, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 130], [0, 1]]
 g := ![![[1, 113], [84, 60], [89], [1], [109], [112], [1]], ![[0, 18], [0, 71], [89], [1], [109], [112], [1]]]
 h' := ![![[51, 130], [92, 47], [63, 45], [41, 73], [120, 130], [60, 41], [51, 51], [0, 1]], ![[0, 1], [0, 84], [0, 86], [96, 58], [69, 1], [55, 90], [32, 80], [51, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [81, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [80, 80, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-568, -540, 21]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17, -24, 21]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1712033451707443829, -116914625297246281, 40253320931320519]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![1712033451707443829, -116914625297246281, 40253320931320519]] 
 ![![131, 0, 0], ![6, 1, 0], ![95, 0, 1]] where
  M :=![![![1712033451707443829, -116914625297246281, 40253320931320519], ![-3260518995436962039, 222660577248584626, -76661304365925762], ![6209565653639986722, -424050733897708845, 145999272882658864]]]
  hmulB := by decide  
  f := ![![![4432259974, 2279394229, -25149772]], ![![218554896, 145337152, 16056075]], ![![1820388523, 1031851438, 39907005]]]
  g := ![![![-10767513625836090, -116914625297246281, 40253320931320519], ![20506423326980745, 222660577248584626, -76661304365925762], ![-39053899746766048, -424050733897708845, 145999272882658864]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![4432259974, 2279394229, -25149772]] ![![1712033451707443829, -116914625297246281, 40253320931320519]]
  ![![131, 0, 0]] where
 M := ![![![131, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22930, -11663, 198]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-22930, -11663, 198]] 
 ![![137, 0, 0], ![0, 137, 0], ![89, 112, 1]] where
  M :=![![![-22930, -11663, 198], ![-16038, -30256, -11465], ![928665, 408167, -41721]]]
  hmulB := by decide  
  f := ![![![-43371863, 2961861, -1019759]], ![![82600479, -5640780, 1942102]], ![![38203267, -2608898, 898235]]]
  g := ![![![-296, -247, 198], ![7331, 9152, -11465], ![33882, 37087, -41721]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [116, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 136], [0, 1]]
 g := ![![[70, 18], [129], [121], [28, 18], [100], [136], [1]], ![[89, 119], [129], [121], [47, 119], [100], [136], [1]]]
 h' := ![![[100, 136], [108, 44], [31, 102], [40, 11], [126, 93], [9, 127], [21, 100], [0, 1]], ![[0, 1], [124, 93], [93, 35], [44, 126], [110, 44], [105, 10], [20, 37], [100, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132]]
 b := ![[], [125, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [116, 37, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3110, 598, -2]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![24, 6, -2]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43371863, 2961861, -1019759]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-43371863, 2961861, -1019759]] 
 ![![137, 0, 0], ![24, 1, 0], ![109, 0, 1]] where
  M :=![![![-43371863, 2961861, -1019759], ![82600479, -5640780, 1942102], ![-157310262, 10742705, -3698678]]]
  hmulB := by decide  
  f := ![![![-22930, -11663, 198]], ![![-4134, -2264, -49]], ![![-11465, -6300, -147]]]
  g := ![![![-24108, 2961861, -1019759], ![45913, -5640780, 1942102], ![-87440, 10742705, -3698678]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-22930, -11663, 198]] ![![-43371863, 2961861, -1019759]]
  ![![137, 0, 0]] where
 M := ![![![137, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB186I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB186I2 : PrimesBelowBoundCertificateInterval O 79 137 186 where
  m := 11
  g := ![1, 2, 2, 2, 2, 2, 1, 3, 3, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB186I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1]
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
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![113, 113, 113]
    · exact ![127, 127, 127]
    · exact ![17161, 131]
    · exact ![18769, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
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
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I89N1, I97N1, I101N1, I103N1, I107N1, I113N0, I113N1, I113N2, I127N0, I127N1, I127N2, I131N1, I137N1]
  Il := ![[], [I89N1], [I97N1], [I101N1], [I103N1], [I107N1], [], [I113N0, I113N1, I113N2], [I127N0, I127N1, I127N2], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
