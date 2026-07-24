
import IdealArithmetic.Examples.NF3_1_304556_1.RI3_1_304556_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-125777380183336870418811702732726486871, -30885948014509370339548590744354402838, -10733453944714271516501117401834815044]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-125777380183336870418811702732726486871, -30885948014509370339548590744354402838, -10733453944714271516501117401834815044]] 
 ![![83, 0, 0], ![0, 83, 0], ![18, 8, 1]] where
  M :=![![![-125777380183336870418811702732726486871, -30885948014509370339548590744354402838, -10733453944714271516501117401834815044], ![-1211565881933079237154671504946184057678, -297512643298765214682829581162083527575, -103391297988242382535146889634898023558], ![-3848259347274030141043391912756046544028, -944980233910149329125824382786732677256, -328398591313274585022378171906437930413]]]
  hmulB := by decide  
  f := ![![![26507229291649182631, 220527181271184010, -935797912799364088]], ![![-102717243226658865670, 11534462686859357223, -274216368985812058]], ![![-4333172782666610706, 728555582174961716, -87748235110174805]]]
  g := ![![![812346877367711046725402536148194987, 662429922207286768583859620124386958, -10733453944714271516501117401834815044], ![7825029901870887331059909740746751402, 6380936633821371633715006456832538083, -103391297988242382535146889634898023558], ![24854401161023040835655604597106460282, 20267572248145148807869891475479165856, -328398591313274585022378171906437930413]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [13, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 82], [0, 1]]
 g := ![![[79, 31], [27, 7], [48], [68], [65, 48], [1]], ![[31, 52], [59, 76], [48], [68], [71, 35], [1]]]
 h' := ![![[52, 82], [64, 60], [65, 67], [5, 31], [68, 20], [70, 52], [0, 1]], ![[0, 1], [30, 23], [63, 16], [40, 52], [29, 63], [35, 31], [52, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [70, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [13, 31, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1022, 445, 66]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, -1, 66]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![48692235383399115479406949979413226, 11956886433552524954013995079305751, 4155245284892175354765910705861341]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![48692235383399115479406949979413226, 11956886433552524954013995079305751, 4155245284892175354765910705861341]] 
 ![![83, 0, 0], ![58, 1, 0], ![41, 0, 1]] where
  M :=![![![48692235383399115479406949979413226, 11956886433552524954013995079305751, 4155245284892175354765910705861341], ![469033867771691813978264172724053261, 115176159941673921155661521273194682, 40025904585549750216807895943778594], ![1489777809656249109841707708369808932, 365830484902311764164392170915068338, 127133046375226446109675516352500433]]]
  hmulB := by decide  
  f := ![![![4293286349246740534, 338561251600431075, -246913600415694468]], ![![2676971969423915549, 240713510065308812, -163279743008731089]], ![![2444531406960296536, 107561688238137393, -113761778588523049]]]
  g := ![![![-9821352222207548450588037392296811, 11956886433552524954013995079305751, 4155245284892175354765910705861341], ![-94605367431963076770352142106218803, 115176159941673921155661521273194682, 40025904585549750216807895943778594], ![-300492111036892981954093185242851475, 365830484902311764164392170915068338, 127133046375226446109675516352500433]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-125777380183336870418811702732726486871, -30885948014509370339548590744354402838, -10733453944714271516501117401834815044]] ![![48692235383399115479406949979413226, 11956886433552524954013995079305751, 4155245284892175354765910705861341]]
  ![![83, 0, 0]] where
 M := ![![![-36601398966637707763684302056944037715468361113129742369070380655373483572, -8987855400502729095453263814348223131460842556171379496358894773374079509, -3123450572335619590115016714619480845384122249050093558831937978625117835]]]
 hmul := by decide  
 g := ![![![![-440980710441418165827521711529446237535763386905177618904462417534620284, -108287414463888302354858600172870158210371597062305777064564997269567223, -37631934606453248073674900176138323438362918663254139263035397332832745]]]]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [19, 3, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 59, 68], [83, 29, 21], [0, 1]]
 g := ![![[72, 36, 45], [49, 32], [48, 78], [3, 39, 64], [5, 50, 1], []], ![[3, 58, 25, 4], [88, 2], [27, 84], [18, 48, 59, 80], [40, 20, 88, 50], [81, 85]], ![[57, 81, 27, 81], [62, 18], [53, 49], [69, 20], [25, 55, 38, 32], [39, 85]]]
 h' := ![![[56, 59, 68], [43, 85, 32], [23, 26, 78], [32, 87, 73], [83, 14, 81], [0, 0, 1], [0, 1]], ![[83, 29, 21], [15, 19, 33], [21, 14, 25], [0, 66, 23], [17, 28, 8], [84, 33, 29], [56, 59, 68]], ![[0, 1], [24, 74, 24], [57, 49, 75], [21, 25, 82], [32, 47], [7, 56, 59], [83, 29, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76, 51], []]
 b := ![[], [68, 56, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [19, 3, 39, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1247691, 455680, 114721]
  a := ![2, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14019, 5120, 1289]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-30094615275040, -3651816401347, 2133338032867]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-30094615275040, -3651816401347, 2133338032867]] 
 ![![97, 0, 0], ![55, 1, 0], ![59, 0, 1]] where
  M :=![![![-30094615275040, -3651816401347, 2133338032867], ![231015367214023, 4038793250832, -8822111171174], ![-312099606767756, 31171134958862, 386976849485]]]
  hmulB := by decide  
  f := ![![![-276558137426677101845265508, -67911736141261346419173649, -23600619020513349210076034]], ![![-184275024606855364546568457, -45250654943549121054237451, -15725462614149810257956483]], ![![-255447908067775853420649070, -62727899066558367507847599, -21799137114499377721857131]]]
  g := ![![![462766421236, -3651816401347, 2133338032867], ![5457590696057, 4038793250832, -8822111171174], ![-21127254264173, 31171134958862, 386976849485]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-85, 12, -1]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-85, 12, -1]] 
 ![![97, 0, 0], ![60, 1, 0], ![29, 0, 1]] where
  M :=![![![-85, 12, -1], ![-98, -101, 35], ![1278, 150, -89]]]
  hmulB := by decide  
  f := ![![![-3739, -918, -319]], ![![-2684, -659, -229]], ![![-2297, -564, -196]]]
  g := ![![![-8, 12, -1], ![51, -101, 35], ![-53, 150, -89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63699054362280001047537413448, 15641967408917542183431977375, 5435880961447803244065077199]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![63699054362280001047537413448, 15641967408917542183431977375, 5435880961447803244065077199]] 
 ![![97, 0, 0], ![78, 1, 0], ![74, 0, 1]] where
  M :=![![![63699054362280001047537413448, 15641967408917542183431977375, 5435880961447803244065077199], ![613588873168175899030590469265, 150673149745444852952578648632, 52361783188200429794361009324], ![1948923415361737376428250753608, 478578478923488411185644880358, 166315117154362395136010626007]]]
  hmulB := by decide  
  f := ![![![5642326311714432, 327698778165617, -287586043697268]], ![![4214378209125689, 274241797004910, -224084547603993]], ![![4551550503400006, 179528620614642, -205285761266743]]]
  g := ![![![-16068346336911605456917242624, 15641967408917542183431977375, 5435880961447803244065077199], ![-154780296524776849856219163031, 150673149745444852952578648632, 52361783188200429794361009324], ![-491623882578280164289864291122, 478578478923488411185644880358, 166315117154362395136010626007]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-30094615275040, -3651816401347, 2133338032867]] ![![-85, 12, -1]]
  ![![5642326311714432, 327698778165617, -287586043697268]] where
 M := ![![![5642326311714432, 327698778165617, -287586043697268]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![5642326311714432, 327698778165617, -287586043697268]] ![![63699054362280001047537413448, 15641967408917542183431977375, 5435880961447803244065077199]]
  ![![97, 0, 0]] where
 M := ![![![97, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1459184956683429751243208647, -358318090661338321188395886, -124522346598028557696981186]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-1459184956683429751243208647, -358318090661338321188395886, -124522346598028557696981186]] 
 ![![101, 0, 0], ![0, 101, 0], ![64, 5, 1]] where
  M :=![![![-1459184956683429751243208647, -358318090661338321188395886, -124522346598028557696981186], ![-14055776216444479667856326346, -3451542502251886674394907623, -1199476618582043521262168844], ![-44644928529864414753996757272, -10963028007698612562287543988, -3809860592913224995583303509]]]
  hmulB := by decide  
  f := ![![![-77443587065735, 3904382193606, 1301948435694]], ![![147118710119946, -56612412094631, 13015095016512]], ![![-36996357881302, 831389597173, 947446980851]]]
  g := ![![![64457873520697009320431557, 2616768735928757101945644, -124522346598028557696981186], ![620898290819864412801212670, 25206342481765652791246897, -1199476618582043521262168844], ![1972140093233484999636976904, 80062128285816954610187857, -3809860592913224995583303509]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [53, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 100], [0, 1]]
 g := ![![[28, 13], [13], [35, 85], [54], [1], [31, 1]], ![[27, 88], [13], [44, 16], [54], [1], [62, 100]]]
 h' := ![![[31, 100], [74, 35], [64, 35], [18, 40], [70, 85], [74, 100], [0, 1]], ![[0, 1], [48, 66], [38, 66], [46, 61], [79, 16], [43, 1], [31, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [32, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [53, 70, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![691671, 716510, 282177]
  a := ![-65, 1, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-171957, -6875, 282177]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![77443587065735, -3904382193606, -1301948435694]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![77443587065735, -3904382193606, -1301948435694]] 
 ![![101, 0, 0], ![85, 1, 0], ![16, 0, 1]] where
  M :=![![![77443587065735, -3904382193606, -1301948435694], ![-147118710119946, 56612412094631, -13015095016512], ![-484163875595808, -117151949396844, 52708029901025]]]
  hmulB := by decide  
  f := ![![![1459184956683429751243208647, 358318090661338321188395886, 124522346598028557696981186]], ![![1367193044896396123995337241, 335728516915501425499094633, 116672040390242286391144254]], ![![673187008285141492810773224, 165308093646336888131701764, 57447704341402791274603985]]]
  g := ![![![4258883648449, -3904382193606, -1301948435694], ![-47038932850489, 56612412094631, -13015095016512], ![85449736086332, -117151949396844, 52708029901025]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-1459184956683429751243208647, -358318090661338321188395886, -124522346598028557696981186]] ![![77443587065735, -3904382193606, -1301948435694]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12726, 3125, 1086]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![12726, 3125, 1086]] 
 ![![103, 0, 0], ![61, 1, 0], ![99, 0, 1]] where
  M :=![![![12726, 3125, 1086], ![122585, 30102, 10461], ![389362, 95612, 33227]]]
  hmulB := by decide  
  f := ![![![2022, 257, -147]], ![![1043, 149, -81]], ![![2158, 227, -142]]]
  g := ![![![-2771, 3125, 1086], ![-26692, 30102, 10461], ![-84781, 95612, 33227]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3333752286036427968847524681962597955, -818637656863948198583594404541065268, -284492144558107497300906395868431745]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-3333752286036427968847524681962597955, -818637656863948198583594404541065268, -284492144558107497300906395868431745]] 
 ![![103, 0, 0], ![69, 1, 0], ![27, 0, 1]] where
  M :=![![![-3333752286036427968847524681962597955, -818637656863948198583594404541065268, -284492144558107497300906395868431745], ![-32112773558255772901683297950068557218, -7885626598966147925662027015857505875, -2740405115149952093051689609491627549], ![-101998812326474816730833453125991312770, -25046872581263686063975579099131177578, -8704264255830096124245621420398571143]]]
  hmulB := by decide  
  f := ![![![-39005171877572068803, -3239650503663052286, 2294808523818133743]], ![![-23710364780933408621, -2192467186885752783, 1465219855886215584]], ![![-12748730466961359145, -416728287933491564, 547882952844122620]]]
  g := ![![![590616834375193205442184096308918084, -818637656863948198583594404541065268, -284492144558107497300906395868431745], ![5689188348344244082343613452430808660, -7885626598966147925662027015857505875, -2740405115149952093051689609491627549], ![18070393501826525408137022165677877291, -25046872581263686063975579099131177578, -8704264255830096124245621420398571143]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29975084362026316166108992889827, 7360694713044514386513525849628, 2557981308083871268709141753924]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![29975084362026316166108992889827, 7360694713044514386513525849628, 2557981308083871268709141753924]] 
 ![![103, 0, 0], ![75, 1, 0], ![48, 0, 1]] where
  M :=![![![29975084362026316166108992889827, 7360694713044514386513525849628, 2557981308083871268709141753924], ![288738638602270353944519118781268, 70902785291368256465455260952611, 24640065447217414428249719302808], ![917111633374419175802271797123888, 225206330348234823470000367258856, 78263480004412770851968786802239]]]
  hmulB := by decide  
  f := ![![![-20193178775971619, 14867112274033852, -4020685581140140]], ![![-18853366115041291, 10004944392993447, -2533696770335428]], ![![4827582276594176, 7598314476993016, -2549999453348609]]]
  g := ![![![-6260777882566389162334410194375, 7360694713044514386513525849628, 2557981308083871268709141753924], ![-60307702909871696830297203681547, 70902785291368256465455260952611, 24640065447217414428249719302808], ![-191553496921893258110119004988328, 225206330348234823470000367258856, 78263480004412770851968786802239]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![12726, 3125, 1086]] ![![-3333752286036427968847524681962597955, -818637656863948198583594404541065268, -284492144558107497300906395868431745]]
  ![![-253548459148200523618999035291446828549800, -62261469566272180108346135718400761309651, -21637043998321560692368609686035846738793]] where
 M := ![![![-253548459148200523618999035291446828549800, -62261469566272180108346135718400761309651, -21637043998321560692368609686035846738793]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![-253548459148200523618999035291446828549800, -62261469566272180108346135718400761309651, -21637043998321560692368609686035846738793]] ![![29975084362026316166108992889827, 7360694713044514386513525849628, 2557981308083871268709141753924]]
  ![![103, 0, 0]] where
 M := ![![![-45421013175466071080234736287532962466183628851233294747159629006065889252, -11153603689780495142550435817805626295668274497417495037650194718765423969, -3876089264464684551588514718142247314151380622315176344092645925281772735]]]
 hmul := by decide  
 g := ![![![![-440980710441418165827521711529446237535763386905177618904462417534620284, -108287414463888302354858600172870158210371597062305777064564997269567223, -37631934606453248073674900176138323438362918663254139263035397332832745]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![214298518, 52623237, 18287575]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![214298518, 52623237, 18287575]] 
 ![![107, 0, 0], ![0, 107, 0], ![37, 60, 1]] where
  M :=![![![214298518, 52623237, 18287575], ![2064256487, 506899718, 176157286], ![6556634220, 1610049942, 559522955]]]
  hmulB := by decide  
  f := ![![![-29446, 1545, 476]], ![![53905, -21830, 5111]], ![![21820, -11289, 2841]]]
  g := ![![![-4320951, -9762909, 18287575], ![-41622085, -94042406, 176157286], ![-132202945, -298703994, 559522955]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [1, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 106], [0, 1]]
 g := ![![[45, 1], [45, 1], [102], [48, 23], [81], [62, 1]], ![[0, 106], [0, 106], [102], [83, 84], [81], [17, 106]]]
 h' := ![![[62, 106], [62, 106], [62, 106], [59, 67], [18, 39], [45, 98], [0, 1]], ![[0, 1], [0, 1], [0, 1], [40, 40], [82, 68], [22, 9], [62, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [84, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [1, 45, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![434, 1875, 486]
  a := ![-2, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-164, -255, 486]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29446, 1545, 476]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-29446, 1545, 476]] 
 ![![107, 0, 0], ![33, 1, 0], ![101, 0, 1]] where
  M :=![![![-29446, 1545, 476], ![53905, -21830, 5111], ![189942, 44712, -20285]]]
  hmulB := by decide  
  f := ![![![214298518, 52623237, 18287575]], ![![85384183, 20966977, 7286423]], ![![263558734, 64719597, 22491290]]]
  g := ![![![-1201, 1545, 476], ![2412, -21830, 5111], ![7133, 44712, -20285]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![214298518, 52623237, 18287575]] ![![-29446, 1545, 476]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2512614888861735747263242, -616998801571054986919569, -214418810052252121011691]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-2512614888861735747263242, -616998801571054986919569, -214418810052252121011691]] 
 ![![109, 0, 0], ![0, 109, 0], ![97, 35, 1]] where
  M :=![![![-2512614888861735747263242, -616998801571054986919569, -214418810052252121011691], ![-24203067907318788298205579, -5943315849697769683450298, -2065415214765417081770398], ![-76875458195010637643643612, -18877570847331468873204126, -6560314651268824670369867]]]
  hmulB := by decide  
  f := ![![![3635729787998, -38840965227, -106602529216]], ![![-11765119178987, 1930089320542, -223125424897]], ![![-622598112209, 538410925883, -149161347248]]]
  g := ![![![167761556754190091659365, 63189537158328158243024, -214418810052252121011691], ![1615983558944281363610303, 608680886854053469527648, -2065415214765417081770398], ![5132798742918030783323243, 1933334329789700867795791, -6560314651268824670369867]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [94, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 108], [0, 1]]
 g := ![![[1, 29], [74], [67, 48], [18, 29], [48], [15, 1]], ![[0, 80], [74], [24, 61], [17, 80], [48], [30, 108]]]
 h' := ![![[15, 108], [51, 62], [24, 69], [52, 87], [6, 47], [7, 22], [0, 1]], ![[0, 1], [0, 47], [78, 40], [49, 22], [57, 62], [10, 87], [15, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [23, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [94, 94, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1040, 382, -123]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![119, 43, -123]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3200993070523076623220345346843990221090497456959, 786037246338497928029877145564820207314227472082, 273162882306247253223919429815906714364528778700]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![3200993070523076623220345346843990221090497456959, 786037246338497928029877145564820207314227472082, 273162882306247253223919429815906714364528778700]] 
 ![![109, 0, 0], ![3, 1, 0], ![70, 0, 1]] where
  M :=![![![3200993070523076623220345346843990221090497456959, 786037246338497928029877145564820207314227472082, 273162882306247253223919429815906714364528778700], ![30833954300025695782661014425314558787412393129082, 7571599187423032674803056223898497650922957916159, 2631274621321741037313550866510367336307211194946], ![97936938154097156718691102064398304807875230634420, 24049436998278351483882650381305205320337848258712, 8357636433761530602832933369463317858237185388241]]]
  hmulB := by decide  
  f := ![![![36366770421524937867616767, 3768853698297449836446638, -2375185983937765190515728]], ![![-1361479754773228509334249, 88718860306541691089037, 16567129900378795846578]], ![![26243027752239256832482966, 2058381713102702274612388, -1505783215585554299819167]]]
  g := ![![![-167692847981006650335262808962971930333662380443, 786037246338497928029877145564820207314227472082, 273162882306247253223919429815906714364528778700], ![-1615321713346470411501804723872538052356525360235, 7571599187423032674803056223898497650922957916159, 2631274621321741037313550866510367336307211194946], ![-5130696543156376513130845733412381295685699920354, 24049436998278351483882650381305205320337848258712, 8357636433761530602832933369463317858237185388241]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-2512614888861735747263242, -616998801571054986919569, -214418810052252121011691]] ![![3200993070523076623220345346843990221090497456959, 786037246338497928029877145564820207314227472082, 273162882306247253223919429815906714364528778700]]
  ![![109, 0, 0]] where
 M := ![![![-48066897438114580075199866556709639891398209172664360460586403511273610956, -11803328176563824956679587418842847244930504079791329700037584702382827307, -4101880872103404040030564119199077254781558134294701179670858309278769205]]]
 hmul := by decide  
 g := ![![![![-440980710441418165827521711529446237535763386905177618904462417534620284, -108287414463888302354858600172870158210371597062305777064564997269567223, -37631934606453248073674900176138323438362918663254139263035397332832745]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-163363, -2562, 6146]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-163363, -2562, 6146]] 
 ![![113, 0, 0], ![0, 113, 0], ![65, 101, 1]] where
  M :=![![![-163363, -2562, 6146], ![673498, -65027, -1540], ![-23688, 217140, -67589]]]
  hmulB := by decide  
  f := ![![![-41854031, -10277694, -3571694]], ![![-403164034, -99001135, -34404776]], ![![-395757849, -97182469, -33772755]]]
  g := ![![![-4981, -5516, 6146], ![6846, 801, -1540], ![38669, 62333, -67589]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [67, 62, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 112], [0, 1]]
 g := ![![[92, 106], [7], [104], [26], [104, 44], [51, 1]], ![[74, 7], [7], [104], [26], [88, 69], [102, 112]]]
 h' := ![![[51, 112], [107, 85], [24, 32], [41, 68], [38, 34], [86, 48], [0, 1]], ![[0, 1], [35, 28], [74, 81], [6, 45], [77, 79], [48, 65], [51, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [75, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [67, 62, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![22506, 5344, 2003]
  a := ![2, 19, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-953, -1743, 2003]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41854031, -10277694, -3571694]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-41854031, -10277694, -3571694]] 
 ![![113, 0, 0], ![35, 1, 0], ![44, 0, 1]] where
  M :=![![![-41854031, -10277694, -3571694], ![-403164034, -99001135, -34404776], ![-1280557488, -314454252, -109278829]]]
  hmulB := by decide  
  f := ![![![-163363, -2562, 6146]], ![![-44639, -1369, 1890]], ![![-63820, 924, 1795]]]
  g := ![![![4203715, -10277694, -3571694], ![40492795, -99001135, -34404776], ![128616016, -314454252, -109278829]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-163363, -2562, 6146]] ![![-41854031, -10277694, -3571694]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [102, 37, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 53, 115], [40, 73, 12], [0, 1]]
 g := ![![[63, 1, 15], [108, 116, 44], [56, 80, 50], [9, 61, 8], [26, 77, 26], [1]], ![[22, 15, 118, 25], [3, 67, 124, 113], [125, 116, 59, 103], [8, 53, 37, 87], [114, 87, 37, 120], [85, 88, 14, 50]], ![[117, 10, 78, 93], [126, 47, 58, 89], [51, 101, 122, 3], [125, 105, 48, 91], [117, 82, 108, 75], [88, 81, 62, 77]]]
 h' := ![![[51, 53, 115], [33, 56, 74], [3, 7, 67], [98, 20, 47], [15, 64, 95], [25, 90, 91], [0, 1]], ![[40, 73, 12], [25, 28, 31], [125, 26, 108], [85, 92, 16], [21, 33, 71], [29, 118, 102], [51, 53, 115]], ![[0, 1], [61, 43, 22], [96, 94, 79], [56, 15, 64], [3, 30, 88], [33, 46, 61], [40, 73, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 24], []]
 b := ![[], [36, 0, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [102, 37, 36, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-331216, -99822, -4699]
  a := ![-2, 3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2608, -786, -37]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![844776400982888572634607832, 207443659317833999345515053, 72090614229000818336150742]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![844776400982888572634607832, 207443659317833999345515053, 72090614229000818336150742]] 
 ![![131, 0, 0], ![0, 131, 0], ![18, 66, 1]] where
  M :=![![![844776400982888572634607832, 207443659317833999345515053, 72090614229000818336150742], ![8137411224507924016322096673, 1998226228646901666013019704, 694421592182502816372695901], ![25846608322579774298124986994, 6346904346703378359646572012, 2205669887964735665358534757]]]
  hmulB := by decide  
  f := ![![![-43898100487564, 5314595595693, -238444071165]], ![![-20914252232457, -47713205626204, 15705342715914]], ![![-12182561767794, -22735801313472, 7556198594953]]]
  g := ![![![-3456905764420810361955004, -34736922746536030617102549, 72090614229000818336150742], ![-33299064387611654033484195, -334607624850368581790724502, 694421592182502816372695901], ![-105766791303705860139913272, -1062803879839459355374173450, 2205669887964735665358534757]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [126, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 130], [0, 1]]
 g := ![![[63, 63], [81, 84], [80], [43], [35], [58], [1]], ![[127, 68], [79, 47], [80], [43], [35], [58], [1]]]
 h' := ![![[53, 130], [12, 60], [71, 79], [8, 92], [102, 49], [53, 67], [5, 53], [0, 1]], ![[0, 1], [48, 71], [66, 52], [37, 39], [79, 82], [67, 64], [63, 78], [53, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [130, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [126, 78, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3119, 1786, 1083]
  a := ![2, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-125, -532, 1083]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43898100487564, 5314595595693, -238444071165]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-43898100487564, 5314595595693, -238444071165]] 
 ![![131, 0, 0], ![63, 1, 0], ![31, 0, 1]] where
  M :=![![![-43898100487564, 5314595595693, -238444071165], ![-20914252232457, -47713205626204, 15705342715914], ![574590864537300, 75018878542158, -42398610030511]]]
  hmulB := by decide  
  f := ![![![844776400982888572634607832, 207443659317833999345515053, 72090614229000818336150742]], ![![468384156384961099941239619, 115016616531835447517408153, 39970460218393544820993837]], ![![397211272924040611067159006, 97539372408826201063798005, 33896785718043977357093189]]]
  g := ![![![-2834548525268, 5314595595693, -238444071165], ![19069863191031, -47713205626204, 15705342715914], ![-21658332615823, 75018878542158, -42398610030511]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![844776400982888572634607832, 207443659317833999345515053, 72090614229000818336150742]] ![![-43898100487564, 5314595595693, -238444071165]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-103348902293999360226, -25378401259083913073, -8819476772313765699]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-103348902293999360226, -25378401259083913073, -8819476772313765699]] 
 ![![137, 0, 0], ![0, 137, 0], ![95, 70, 1]] where
  M :=![![![-103348902293999360226, -25378401259083913073, -8819476772313765699], ![-995520846213598139963, -244460530651019611410, -84954680549565504918], ![-3162042162936408597388, -776472444582520768526, -269838931910103524483]]]
  hmulB := by decide  
  f := ![![![3054828174, 2875340705, -1005101952]], ![![-107685874015, -13026803058, 7620920163]], ![![-50903133642, -4634508597, 3122834041]]]
  g := ![![![5361324022451156067, 4321058195641457561, -8819476772313765699], ![51643604423322079031, 41623117575317998050, -84954680549565504918], ![164033988091411870281, 132206224738136685732, -269838931910103524483]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [103, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 136], [0, 1]]
 g := ![![[108, 4], [49], [107], [122, 87], [100], [44], [1]], ![[0, 133], [49], [107], [102, 50], [100], [44], [1]]]
 h' := ![![[110, 136], [54, 2], [13, 130], [38, 92], [47, 19], [49, 127], [34, 110], [0, 1]], ![[0, 1], [0, 135], [65, 7], [20, 45], [82, 118], [45, 10], [78, 27], [110, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [130, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [103, 27, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4193, 4200, 1430]
  a := ![-5, 0, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-961, -700, 1430]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3054828174, -2875340705, 1005101952]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-3054828174, -2875340705, 1005101952]] 
 ![![137, 0, 0], ![63, 1, 0], ![93, 0, 1]] where
  M :=![![![-3054828174, -2875340705, 1005101952], ![107685874015, 13026803058, -7620920163], ![-274073195566, -3791169296, 10151462353]]]
  hmulB := by decide  
  f := ![![![103348902293999360226, 25378401259083913073, 8819476772313765699]], ![![54791983144055166673, 13454743138491285657, 4675778957703158715]], ![![93237153841447803638, 22895355924652004995, 7956571326534917770]]]
  g := ![![![617643465, -2875340705, 1005101952], ![-31074040, 13026803058, -7620920163], ![-7148288531, -3791169296, 10151462353]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-103348902293999360226, -25378401259083913073, -8819476772313765699]] ![![-3054828174, -2875340705, 1005101952]]
  ![![137, 0, 0]] where
 M := ![![![-137, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB157I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB157I2 : PrimesBelowBoundCertificateInterval O 79 137 157 where
  m := 11
  g := ![2, 1, 3, 2, 3, 2, 2, 2, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB157I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
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
    · exact ![6889, 83]
    · exact ![704969]
    · exact ![97, 97, 97]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![2048383]
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
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I97N0, I97N1, I97N2, I101N1, I103N0, I103N1, I103N2, I107N1, I109N1, I113N1, I131N1, I137N1]
  Il := ![[I83N1], [], [I97N0, I97N1, I97N2], [I101N1], [I103N0, I103N1, I103N2], [I107N1], [I109N1], [I113N1], [], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
