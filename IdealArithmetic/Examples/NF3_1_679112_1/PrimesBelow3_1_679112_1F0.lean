
import IdealArithmetic.Examples.NF3_1_679112_1.RI3_1_679112_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45844278909695895742098, -8215199935318871533441, 200161676099540801912]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-45844278909695895742098, -8215199935318871533441, 200161676099540801912]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-45844278909695895742098, -8215199935318871533441, 200161676099540801912], ![-31625544823727446702096, -46244602261894977345922, -8015038259219330731529], ![1266376044956654255581582, -15595468305288785239038, -54259640521114308077451]]]
  hmulB := by decide  
  f := ![![![-2384217219634999027415749412640927560726775720, 448875410375027352961122101941509684091979547, -75101538888014440911498388867537537819564153]], ![![5933021572153140832008372720535465487745568087, -1117007070929485072796376317452926242543823707, 186886935743506456024811856536986073136207697]], ![![-29528135847474020051920273332843799555520816126, 5559247700666127919958749007461493341473152693, -930120135185978616771564460915940169407616010]]]
  g := ![![![-22922139454847947871049, -8215199935318871533441, 200161676099540801912], ![-15812772411863723351048, -46244602261894977345922, -8015038259219330731529], ![633188022478327127790791, -15595468305288785239038, -54259640521114308077451]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -1, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-5, -1, 0]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-5, -1, 0], ![0, -5, -1], ![158, 2, -6]]]
  hmulB := by decide  
  f := ![![![-32, 6, -1]], ![![63, -12, 2]], ![![-411, 77, -13]]]
  g := ![![![-2, -1, 0], ![3, -5, -1], ![81, 2, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-45844278909695895742098, -8215199935318871533441, 200161676099540801912]] ![![-45844278909695895742098, -8215199935318871533441, 200161676099540801912]]
  ![![2614988034271129050031634970773681150175818724, 753406955568896718852594835604634765239036164, 45808173491312565667606478804333315714383601]] where
 M := ![![![2614988034271129050031634970773681150175818724, 753406955568896718852594835604634765239036164, 45808173491312565667606478804333315714383601]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2614988034271129050031634970773681150175818724, 753406955568896718852594835604634765239036164, 45808173491312565667606478804333315714383601]] ![![-5, -1, 0]]
  ![![2, 0, 0]] where
 M := ![![![-5837248759728259874676351202783741868006484662, -6290406465132987512959396191188188344942232342, -1028255996516772112858233708430634659525337770]]]
 hmul := by decide  
 g := ![![![![-2918624379864129937338175601391870934003242331, -3145203232566493756479698095594094172471116171, -514127998258386056429116854215317329762668885]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [2, 0, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 0, 2], [1, 2, 1], [0, 1]]
 g := ![![[1]], ![[0, 2, 1, 2]], ![[2, 1, 2, 1]]]
 h' := ![![[1, 0, 2], [0, 1]], ![[1, 2, 1], [1, 0, 2]], ![[0, 1], [1, 2, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 2], []]
 b := ![[], [2, 1, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [2, 0, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-25752, 306, 804]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8584, 102, 268]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 27 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def PBC3 : ContainsPrimesAboveP 3 ![I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![3, 0, 0]]) timesTableT_eq_Table B_one_repr 3 (by decide) 𝕀

instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1439, 6570, 1262]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![1439, 6570, 1262]] 
 ![![5, 0, 0], ![0, 5, 0], ![2, 0, 1]] where
  M :=![![![1439, 6570, 1262], ![-199396, -1085, 7832], ![-1237456, -215060, 6747]]]
  hmulB := by decide  
  f := ![![![-335405885, 63146702, -10565102]], ![![1669286116, -314275681, 52581600]], ![![-1795740914, 338083264, -56564857]]]
  g := ![![![-217, 1314, 1262], ![-43012, -217, 7832], ![-250190, -43012, 6747]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [2, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 4], [0, 1]]
 g := ![![[2, 1], [1]], ![[3, 4], [1]]]
 h' := ![![[1, 4], [3, 1], [0, 1]], ![[0, 1], [4, 4], [1, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [2, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [2, 4, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![473, -1420, -11]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![99, -284, -11]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-335405885, 63146702, -10565102]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-335405885, 63146702, -10565102]] 
 ![![5, 0, 0], ![4, 1, 0], ![4, 0, 1]] where
  M :=![![![-335405885, 63146702, -10565102], ![1669286116, -314275681, 52581600], ![-8307892800, 1564122916, -261694081]]]
  hmulB := by decide  
  f := ![![![1439, 6570, 1262]], ![![-38728, 5039, 2576]], ![![-246340, -37756, 2359]]]
  g := ![![![-109146457, 63146702, -10565102], ![543212488, -314275681, 52581600], ![-2703521628, 1564122916, -261694081]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![1439, 6570, 1262]] ![![-335405885, 63146702, -10565102]]
  ![![5, 0, 0]] where
 M := ![![![5, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0)

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15754376932398401518788687375, -2966068843264128029468422344, 496254259931102038537943968]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![15754376932398401518788687375, -2966068843264128029468422344, 496254259931102038537943968]] 
 ![![7, 0, 0], ![1, 1, 0], ![6, 0, 1]] where
  M :=![![![15754376932398401518788687375, -2966068843264128029468422344, 496254259931102038537943968], ![-78408173069114122088995146944, 14761868412536197441712799439, -2469814583333025990930478376], ![390230704166618106567015583408, -73468543902448070107134190192, 12292053829203171450782321063]]]
  hmulB := by decide  
  f := ![![![-3036103004535, -52383260130184, -10402676600608]], ![![234369542841647, -4944858561929, -10455516190200]], ![![1414565912205418, 207842173653792, -15347535162537]]]
  g := ![![![2248988602296559616718492273, -2966068843264128029468422344, 496254259931102038537943968], ![-11193021997378880512160725161, 14761868412536197441712799439, -2469814583333025990930478376], ![55706703584835306852779406746, -73468543902448070107134190192, 12292053829203171450782321063]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1277834377862340248495776358419708103, 240577253628797580117988699421729487, -40251084268304198592171522627997885]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-1277834377862340248495776358419708103, 240577253628797580117988699421729487, -40251084268304198592171522627997885]] 
 ![![7, 0, 0], ![4, 1, 0], ![5, 0, 1]] where
  M :=![![![-1277834377862340248495776358419708103, 240577253628797580117988699421729487, -40251084268304198592171522627997885], ![6359671314392063377563100575223665830, -1197332209325731851311433313163712333, 200326169360493381525817176793731602], ![-31651534758957954281079113933409593116, 5959018975671076614511466221636202626, -997006039965238469785616136369980731]]]
  hmulB := by decide  
  f := ![![![306226847894531429, 499300275674931013, 87960298545267531]], ![![-1810402825510592026, 303929621929102917, 134157395485895524]], ![![-13036576641045530401, -1796535277174001703, 165338331107218938]]]
  g := ![![![-291269710148001368000981934709519518, 240577253628797580117988699421729487, -40251084268304198592171522627997885], ![1449624186413217696454249706272836736, -1197332209325731851311433313163712333, 200326169360493381525817176793731602], ![-7214654351688009770028128305443499995, 5959018975671076614511466221636202626, -997006039965238469785616136369980731]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![15754376932398401518788687375, -2966068843264128029468422344, 496254259931102038537943968]] ![![15754376932398401518788687375, -2966068843264128029468422344, 496254259931102038537943968]]
  ![![674418081024245632565178774499385032785045281347951790305, -126972362413539543912155899089357466440154142151250133872, 21243800825570945846745632560488245047394146506826435328]] where
 M := ![![![674418081024245632565178774499385032785045281347951790305, -126972362413539543912155899089357466440154142151250133872, 21243800825570945846745632560488245047394146506826435328]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![674418081024245632565178774499385032785045281347951790305, -126972362413539543912155899089357466440154142151250133872, 21243800825570945846745632560488245047394146506826435328]] ![![-1277834377862340248495776358419708103, 240577253628797580117988699421729487, -40251084268304198592171522627997885]]
  ![![7, 0, 0]] where
 M := ![![![-2341696000189649228862641178684083615861049138852394416046910823026922267392050041105625337223, 440869961177281863758018659491372975245621616816532129515150181558803298010880177009699438239, -73762143723244339020454347254380192640908834105035855380717300811922846370878841777218192637]]]
 hmul := by decide  
 g := ![![![![-334528000027092746980377311240583373694435591264627773720987260432417466770292863015089333889, 62981423025325980536859808498767567892231659545218875645021454508400471144411453858528491177, -10537449103320619860064906750625741805844119157862265054388185830274692338696977396745456091]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1006013182028999527656046531, 189401609973727992542633772, -31688865213200886595488834]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-1006013182028999527656046531, 189401609973727992542633772, -31688865213200886595488834]] 
 ![![11, 0, 0], ![0, 11, 0], ![4, 9, 1]] where
  M :=![![![-1006013182028999527656046531, 189401609973727992542633772, -31688865213200886595488834], ![5006840703685740082087235772, -942635451602597754465068863, 157712744760527105947144938], ![-24918613672163282739648900204, 4691415214164685870192945896, -784922706842070648517923925]]]
  hmulB := by decide  
  f := ![![![10627616729743, -3573308879076, -1147034551854]], ![![181231459192932, 12921685833451, -4720343430930]], ![![219946169249300, 26606734821777, -3533626062115]]]
  g := ![![![-79932520106926907388553745, 43145581535685088354730298, -31688865213200886595488834], ![397817247694875605299877820, -214731832222485609817215755, 157712744760527105947144938], ![-1979902076799545467779745864, 1068701779613029246077660111, -784922706842070648517923925]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [6, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 10], [0, 1]]
 g := ![![[2, 9], [0, 1], [1]], ![[4, 2], [10, 10], [1]]]
 h' := ![![[10, 10], [0, 8], [5, 10], [0, 1]], ![[0, 1], [3, 3], [6, 1], [10, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [6, 1, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4196, -283, 125]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![336, -128, 125]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10627616729743, -3573308879076, -1147034551854]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![10627616729743, -3573308879076, -1147034551854]] 
 ![![11, 0, 0], ![1, 1, 0], ![10, 0, 1]] where
  M :=![![![10627616729743, -3573308879076, -1147034551854], ![181231459192932, 12921685833451, -4720343430930], ![745814262086940, 190672146054792, 8201342402521]]]
  hmulB := by decide  
  f := ![![![-1006013182028999527656046531, 189401609973727992542633772, -31688865213200886595488834]], ![![363711592877885504948289931, -68475803784442705629312281, 11456716322484201759241464]], ![![-3179885953859388910564487774, 598675573991087799601753056, -100164668997643592224801115]]]
  g := ![![![2333751920669, -3573308879076, -1147034551854], ![19592109788071, 12921685833451, -4720343430930], ![43011699273358, 190672146054792, 8201342402521]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-1006013182028999527656046531, 189401609973727992542633772, -31688865213200886595488834]] ![![10627616729743, -3573308879076, -1147034551854]]
  ![![11, 0, 0]] where
 M := ![![![11, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![48077175259605063222977997869466821, -9051466282770631513295016479010301, 1514404735294158571115328011170699]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![48077175259605063222977997869466821, -9051466282770631513295016479010301, 1514404735294158571115328011170699]] 
 ![![13, 0, 0], ![0, 13, 0], ![8, 2, 1]] where
  M :=![![![48077175259605063222977997869466821, -9051466282770631513295016479010301, 1514404735294158571115328011170699], ![-239275948176477054236221825764970442, 45048365789016746080747341847125423, -7537061547476472942179688467839602], ![1190855724501282724864390777918657116, -224201825081524108351862448829291238, 37511304241540273138567653379285821]]]
  hmulB := by decide  
  f := ![![![-183939837013498461, 744040421477443, 7575509419858425]], ![![-1196930488337631150, -199090855853215311, 8319549841335868]], ![![-398451426747255164, -123522998181147228, -8732933151564639]]]
  g := ![![![2766302875173214973388874906161633, -929251981027611435040436346257823, 1514404735294158571115328011170699], ![-13767650445897328515291101386327202, 4624806837228437843469747598677279, -7537061547476472942179688467839602], ![68520406966843118442757657760336196, -23017264120354204202230596583681760, 37511304241540273138567653379285821]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [4, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 12], [0, 1]]
 g := ![![[4, 10], [12], [10, 1]], ![[0, 3], [12], [7, 12]]]
 h' := ![![[10, 12], [5, 6], [12, 5], [0, 1]], ![[0, 1], [0, 7], [10, 8], [10, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [6, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [4, 3, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-466, -1423, -29]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, -105, -29]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![183939837013498461, -744040421477443, -7575509419858425]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![183939837013498461, -744040421477443, -7575509419858425]] 
 ![![13, 0, 0], ![10, 1, 0], ![4, 0, 1]] where
  M :=![![![183939837013498461, -744040421477443, -7575509419858425], ![1196930488337631150, 199090855853215311, -8319549841335868], ![1314488874931067144, 1213569588020302886, 190771306011879443]]]
  hmulB := by decide  
  f := ![![![-48077175259605063222977997869466821, 9051466282770631513295016479010301, -1514404735294158571115328011170699]], ![![-18576600339967198307196780994592136, 3497407464514582234784832534075199, -585152754266547136074891664912876]], ![![-106397263503054075212023289953578800, 20031360785585125723464808826564034, -3351455629439762109463766571074509]]]
  g := ![![![17052482992900507, -744040421477443, -7575509419858425], ![-58515374679167576, 199090855853215311, -8319549841335868], ![-891099402255344576, 1213569588020302886, 190771306011879443]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![48077175259605063222977997869466821, -9051466282770631513295016479010301, 1514404735294158571115328011170699]] ![![183939837013498461, -744040421477443, -7575509419858425]]
  ![![13, 0, 0]] where
 M := ![![![-13, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [5, 16, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 6, 14], [5, 10, 3], [0, 1]]
 g := ![![[4, 3, 13], [3, 8], [2, 1], []], ![[15, 1, 1, 11], [12, 13], [5, 15], [16, 9]], ![[0, 10, 6, 12], [12, 16], [2, 2], [10, 9]]]
 h' := ![![[14, 6, 14], [0, 6, 8], [7, 14, 5], [0, 0, 1], [0, 1]], ![[5, 10, 3], [9, 9, 11], [1, 14, 8], [14, 3, 10], [14, 6, 14]], ![[0, 1], [0, 2, 15], [3, 6, 4], [9, 14, 6], [5, 10, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 15], []]
 b := ![[], [5, 13, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [5, 16, 15, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-32385, -2006, 816]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1905, -118, 48]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0]] 
 ![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [7, 13, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 13, 5], [1, 5, 14], [0, 1]]
 g := ![![[11, 1, 16], [18, 11, 17], [0, 1], []], ![[1, 3, 3, 4], [2, 15, 9, 11], [14, 6], [16, 6]], ![[6, 5, 17, 3], [1, 11, 8, 14], [13, 17], [7, 6]]]
 h' := ![![[18, 13, 5], [7, 12, 4], [0, 12, 6], [0, 0, 1], [0, 1]], ![[1, 5, 14], [7, 2, 4], [6, 1, 14], [3, 9, 5], [18, 13, 5]], ![[0, 1], [17, 5, 11], [9, 6, 18], [9, 10, 13], [1, 5, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 13], []]
 b := ![[], [10, 17, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [7, 13, 0, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1238857, -195814, -2508]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-65203, -10306, -132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [15, 5, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 9, 12], [7, 13, 11], [0, 1]]
 g := ![![[11, 18, 18], [4, 0, 2], [4, 3, 1], []], ![[1, 12, 17, 9], [3, 2, 19, 2], [11, 15, 18, 4], [4, 6]], ![[8, 7, 12, 10], [19, 17, 11, 7], [15, 1, 18, 17], [5, 6]]]
 h' := ![![[19, 9, 12], [9, 15, 8], [9, 4, 5], [0, 0, 1], [0, 1]], ![[7, 13, 11], [11, 13, 8], [3, 0, 21], [2, 2, 13], [19, 9, 12]], ![[0, 1], [21, 18, 7], [22, 19, 20], [20, 21, 9], [7, 13, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 16], []]
 b := ![[], [0, 16, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [15, 5, 20, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10557, -230, -1012]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-459, -10, -44]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀

instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-189, -33, 1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-189, -33, 1]] 
 ![![29, 0, 0], ![0, 29, 0], ![14, 25, 1]] where
  M :=![![![-189, -33, 1], ![-158, -191, -32], ![5056, -94, -223]]]
  hmulB := by decide  
  f := ![![![1365, -257, 43]], ![![-6794, 1279, -214]], ![![-4032, 759, -127]]]
  g := ![![![-7, -2, 1], ![10, 21, -32], ![282, 189, -223]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [11, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 28], [0, 1]]
 g := ![![[15, 23], [25], [22, 28], [9, 1]], ![[19, 6], [25], [13, 1], [18, 28]]]
 h' := ![![[9, 28], [28, 9], [19, 5], [17, 12], [0, 1]], ![[0, 1], [22, 20], [6, 24], [9, 17], [9, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [12, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [11, 20, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1253, -628, 41]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-63, -57, 41]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1365, 257, -43]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-1365, 257, -43]] 
 ![![29, 0, 0], ![3, 1, 0], ![20, 0, 1]] where
  M :=![![![-1365, 257, -43], ![6794, -1279, 214], ![-33812, 6366, -1065]]]
  hmulB := by decide  
  f := ![![![189, 33, -1]], ![![25, 10, 1]], ![![-44, 26, 7]]]
  g := ![![![-44, 257, -43], ![219, -1279, 214], ![-1090, 6366, -1065]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-189, -33, 1]] ![![-1365, 257, -43]]
  ![![29, 0, 0]] where
 M := ![![![-29, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-60509, 11392, -1906]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-60509, 11392, -1906]] 
 ![![31, 0, 0], ![7, 1, 0], ![13, 0, 1]] where
  M :=![![![-60509, 11392, -1906], ![301148, -56697, 9486], ![-1498788, 282176, -47211]]]
  hmulB := by decide  
  f := ![![![-531, -256, -30]], ![![33, -73, -16]], ![![1235, 64, -37]]]
  g := ![![![-3725, 11392, -1906], ![18539, -56697, 9486], ![-92267, 282176, -47211]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-84185715758688343, 15849603550251079, -2651804019280749]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-84185715758688343, 15849603550251079, -2651804019280749]] 
 ![![31, 0, 0], ![8, 1, 0], ![29, 0, 1]] where
  M :=![![![-84185715758688343, 15849603550251079, -2651804019280749], ![418985035046358342, -78882107720126845, 13197799530970330], ![-2085252325893312140, 392589435984417682, -65684308189156515]]]
  hmulB := by decide  
  f := ![![![111229885, -240825867, -52879165]], ![![298217650, -55148991, -23120592]], ![![1601001991, 63173161, -51942342]]]
  g := ![![![-4325168632308234, 15849603550251079, -2651804019280749], ![21525990658362372, -78882107720126845, 13197799530970330], ![-107132996009132731, 392589435984417682, -65684308189156515]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-115809076985, -6320644893, 3405446107]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![-115809076985, -6320644893, 3405446107]] 
 ![![31, 0, 0], ![15, 1, 0], ![23, 0, 1]] where
  M :=![![![-115809076985, -6320644893, 3405446107], ![-538060484906, -122619969199, -2915198786], ![460601408188, -532230087334, -125535167985]]]
  hmulB := by decide  
  f := ![![![13841561927243240117491, -2605944097356127659343, 436001633068005158191]], ![![4475328093029154411877, -842567832233376938356, 140970388120385641023]], ![![21329252699487673480139, -4015647978559984069573, 671859798625265352850]]]
  g := ![![![-3204021421, -6320644893, 3405446107], ![44138342747, -122619969199, -2915198786], ![365527792963, -532230087334, -125535167985]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-60509, 11392, -1906]] ![![-84185715758688343, 15849603550251079, -2651804019280749]]
  ![![13841561927243240117491, -2605944097356127659343, 436001633068005158191]] where
 M := ![![![13841561927243240117491, -2605944097356127659343, 436001633068005158191]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![13841561927243240117491, -2605944097356127659343, 436001633068005158191]] ![![-115809076985, -6320644893, 3405446107]]
  ![![31, 0, 0]] where
 M := ![![![31, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)


lemma PB234I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB234I0 : PrimesBelowBoundCertificateInterval O 1 31 234 where
  m := 11
  g := ![3, 1, 2, 3, 2, 2, 1, 1, 1, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB234I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1]
    · exact ![I3N0]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0]
    · exact ![I23N0]
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1, I31N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2]
    · exact ![27]
    · exact ![25, 5]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![169, 13]
    · exact ![4913]
    · exact ![6859]
    · exact ![12167]
    · exact ![841, 29]
    · exact ![31, 31, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
  β := ![I2N0, I2N1, I3N0, I5N0, I5N1, I7N0, I7N1, I11N0, I11N1, I13N0, I13N1, I29N1, I31N0, I31N1, I31N2]
  Il := ![[I2N0, I2N0, I2N1], [I3N0], [I5N0, I5N1], [I7N0, I7N0, I7N1], [I11N0, I11N1], [I13N0, I13N1], [], [], [], [I29N1], [I31N0, I31N1, I31N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
