
import IdealArithmetic.Examples.NF3_1_664563_1.RI3_1_664563_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1134126254851193265847172239225879275868, -60936993165164367140297974051597256031, -38346195639285995294165533356165144086]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-1134126254851193265847172239225879275868, -60936993165164367140297974051597256031, -38346195639285995294165533356165144086]] 
 ![![37, 0, 0], ![0, 37, 0], ![29, 8, 1]] where
  M :=![![![-1134126254851193265847172239225879275868, -60936993165164367140297974051597256031, -38346195639285995294165533356165144086], ![-5406813585139325336477340203219285316126, -290509950786901369375530505390246105976, -182810979495493101420893922154791768093], ![-8592116036288175766782014341275213100371, -461657345412825701739224638604622139360, -290509950786901369375530505390246105976]]]
  hmulB := by decide  
  f := ![![![15831249845276338592, -2101475853933531992, -767255455222485431]], ![![-108183019186370445771, 32710869860171018074, -6304427561800595976]], ![![-18990973064393993456, 5700422202929097443, -1080404292856373709]]]
  g := ![![![-596934630051335197739777618840272902, 6644123566192529600352061967506051261, -38346195639285995294165533356165144086], ![-2845815669460145818146390830549298417, 31675077977757930864638401941840217264, -182810979495493101420893922154791768093], ![-4522363877514487970044045539407460191, 50335736780605006845000524446414775904, -290509950786901369375530505390246105976]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [10, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 36], [0, 1]]
 g := ![![[11, 26], [33], [12, 28], [1], [1]], ![[0, 11], [33], [3, 9], [1], [1]]]
 h' := ![![[1, 36], [10, 27], [28, 25], [16, 18], [27, 1], [0, 1]], ![[0, 1], [0, 10], [16, 12], [34, 19], [28, 36], [1, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [18, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [10, 36, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![292, -33, -55]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![51, 11, -55]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2175564539448815049733816020948408303916133939404530964509003231479923246, -116893829856853984866505285068591740994409192797576372956082393613661455, -73558497652929652130465049959261874660058056533911286392118534985297764]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-2175564539448815049733816020948408303916133939404530964509003231479923246, -116893829856853984866505285068591740994409192797576372956082393613661455, -73558497652929652130465049959261874660058056533911286392118534985297764]] 
 ![![37, 0, 0], ![13, 1, 0], ![30, 0, 1]] where
  M :=![![![-2175564539448815049733816020948408303916133939404530964509003231479923246, -116893829856853984866505285068591740994409192797576372956082393613661455, -73558497652929652130465049959261874660058056533911286392118534985297764], ![-10371748169063080950395572044255924327068185971281491381288713432926984724, -557277591084362702863584921844647061394856695658482663882395461803372438, -350681489570561954599515855205775222983227578392729118868247180840984365], ![-16482030009816411866177245194671435480211696184458268586807617499526265155, -885585132836905983068741076576289807145726415547150255395758484808442898, -557277591084362702863584921844647061394856695658482663882395461803372438]]]
  hmulB := by decide  
  f := ![![![-4680994905946774571793296972924774074, 820794551345125601816680300488897218, 101366891131282089663864128762477557]], ![![-1258383841291818778127243743040884525, 101601693423017629168068543260983338, 102166303749784972191358772307537835]], ![![-667508525371365602639107751859694986, 306232440376520622398244769074260079, -104596210186392374445469836292566314]]]
  g := ![![![41913788602112873444451464424895691048998034134629742586043890136665097, -116893829856853984866505285068591740994409192797576372956082393613661455, -73558497652929652130465049959261874660058056533911286392118534985297764], ![199819059517580887157202907997236328663831849298936670681887648533686160, -557277591084362702863584921844647061394856695658482663882395461803372438, -350681489570561954599515855205775222983227578392729118868247180840984365], ![317537958097141810800646931247560644716985083443490936481327206948234207, -885585132836905983068741076576289807145726415547150255395758484808442898, -557277591084362702863584921844647061394856695658482663882395461803372438]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-1134126254851193265847172239225879275868, -60936993165164367140297974051597256031, -38346195639285995294165533356165144086]] ![![-2175564539448815049733816020948408303916133939404530964509003231479923246, -116893829856853984866505285068591740994409192797576372956082393613661455, -73558497652929652130465049959261874660058056533911286392118534985297764]]
  ![![37, 0, 0]] where
 M := ![![![3731411157890151728317245175245890468170385119592438773138436697667419138589492339731639399691646471991770021302, 200490002988780553048417324159778122254247270684708408360111312074712678316761003982933938676338183745711342746, 126163574521819382596727961095031848702129712635449852931234841646410700577666033200038248349506524918643616135]]]
 hmul := by decide  
 g := ![![![![100848950213247344008574193925564607247848246475471318192930721558578895637553847019774037829503958702480270846, 5418648729426501433741008761075084385249926234721848874597603029046288603155702810349565910171302263397603858, 3409826338427550880992647597163022937895397638795941971114455179632721637234217113514547252689365538341719355]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10605136532544498992037129097015765, 569817628006585361509694251112990, 358572635558682565565193122875022]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![10605136532544498992037129097015765, 569817628006585361509694251112990, 358572635558682565565193122875022]] 
 ![![41, 0, 0], ![0, 41, 0], ![5, 34, 1]] where
  M :=![![![10605136532544498992037129097015765, 569817628006585361509694251112990, 358572635558682565565193122875022], ![50558741613774241744692230325378102, 2716538550253482549602880393765281, 1709452884019756084529082753338970], ![80344285548928535972866889406931590, 4316926055113202628350803250640254, 2716538550253482549602880393765281]]]
  hmulB := by decide  
  f := ![![![39412020676392941, -10980626252335722, 1707610992061198]], ![![240773149880628918, 1844578851046585, -32941878757007166]], ![![166709241408390515, 8040098630540670, -27064420583582709]]]
  g := ![![![214933496457343564980760084942455, -283454926365576143114801754308238, 358572635558682565565193122875022], ![1024670175455499056635288208748372, -1351338036741907910350876419994139, 1709452884019756084529082753338970], ![1628331531650271298167133839953785, -2147448406183053757515783661887300, 2716538550253482549602880393765281]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [25, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 40], [0, 1]]
 g := ![![[5, 23], [40], [5], [10, 4], [1]], ![[0, 18], [40], [5], [2, 37], [1]]]
 h' := ![![[39, 40], [16, 8], [14, 9], [37, 13], [16, 39], [0, 1]], ![[0, 1], [0, 33], [37, 32], [11, 28], [20, 2], [39, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [6, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [25, 2, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1668, 687, -186]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, 171, -186]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257809694604775262548412284317420828376451146135769370446195336569113958461020, 13852203430477503711283815936665244947884739683655115061047133001484440451568, 8716861059103525459804632713034500891586064402587832403417924684185213139755]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![257809694604775262548412284317420828376451146135769370446195336569113958461020, 13852203430477503711283815936665244947884739683655115061047133001484440451568, 8716861059103525459804632713034500891586064402587832403417924684185213139755]] 
 ![![41, 0, 0], ![21, 1, 0], ![17, 0, 1]] where
  M :=![![![257809694604775262548412284317420828376451146135769370446195336569113958461020, 13852203430477503711283815936665244947884739683655115061047133001484440451568, 8716861059103525459804632713034500891586064402587832403417924684185213139755], ![1229077409333597089832453212537864625713635080764884368881927380470115052705455, 66038751304497702432710364630661808761557729278837057571000993517039269386410, 41556610291432511133851447809995734843654219050965345183141399004453321354704], ![1953160683697328023291018047069799537651748295395371223607645753209306103671088, 104943994307360614962573786905986153051080753881215591617605534124047327633989, 66038751304497702432710364630661808761557729278837057571000993517039269386410]]]
  hmulB := by decide  
  f := ![![![-491266910002928267857800757810662746156, -77392136824784985156396566980537258185, 113546366625026669701307625974833246322]], ![![138864209367494312265135593864087074686, -112549313392048772916363327703616502125, 52495055820761100201421230354387473127]], ![![-469849482008401547820354361635049270457, 139600973548784839066913201359020704099, -25829237637269795521081436284995828726]]]
  g := ![![![-4421297937561274346468941621320386114294914196706858455948760392517266204823, 13852203430477503711283815936665244947884739683655115061047133001484440451568, 8716861059103525459804632713034500891586064402587832403417924684185213139755], ![-21078018122322130500730220914047825624907291657490358737134079669839416279003, 66038751304497702432710364630661808761557729278837057571000993517039269386410, 41556610291432511133851447809995734843654219050965345183141399004453321354704], ![-33495657778870873958027016504320985984571437410985028757782618370374520883211, 104943994307360614962573786905986153051080753881215591617605534124047327633989, 66038751304497702432710364630661808761557729278837057571000993517039269386410]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![10605136532544498992037129097015765, 569817628006585361509694251112990, 358572635558682565565193122875022]] ![![257809694604775262548412284317420828376451146135769370446195336569113958461020, 13852203430477503711283815936665244947884739683655115061047133001484440451568, 8716861059103525459804632713034500891586064402587832403417924684185213139755]]
  ![![41, 0, 0]] where
 M := ![![![4134806958743141104351541950948148897161778105494324045910159583901734721139707727810735551009662306801691104686, 222164597906486558783381359204078459795246975623595803858501724190897832729383815224332202317023392799301758178, 139802879875529586120698551483683940453711303190633620815692662364941587126602901654096437360263987072010493555]]]
 hmul := by decide  
 g := ![![![![100848950213247344008574193925564607247848246475471318192930721558578895637553847019774037829503958702480270846, 5418648729426501433741008761075084385249926234721848874597603029046288603155702810349565910171302263397603858, 3409826338427550880992647597163022937895397638795941971114455179632721637234217113514547252689365538341719355]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2126128167637015374310744938868924, -114237596621515096961502774242599, -71886993464500044801119201392488]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-2126128167637015374310744938868924, -114237596621515096961502774242599, -71886993464500044801119201392488]] 
 ![![43, 0, 0], ![0, 43, 0], ![5, 18, 1]] where
  M :=![![![-2126128167637015374310744938868924, -114237596621515096961502774242599, -71886993464500044801119201392488], ![-10136066078494506316957807396340808, -544614311418014388686122508234188, -342712789864545290884508322727797], ![-16107501123633628671571891168206459, -865461567158169972499541432109758, -544614311418014388686122508234188]]]
  hmulB := by decide  
  f := ![![![11310330451384274, 119701008490156, -1568245086298713]], ![![-221122557168118533, 45811722349955960, 359103025470468]], ![![-90855268245862796, 17415548048810119, 1033357008765833]]]
  g := ![![![-41085888379407329076863928648988, 27435541528825249057177740716795, -71886993464500044801119201392488], ![-195872142538878601454308506574461, 130795718747530252261279704671306, -342712789864545290884508322727797], ![-311265803873105970421890200628733, 207851070659676488926759621304782, -544614311418014388686122508234188]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [28, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 42], [0, 1]]
 g := ![![[4, 38], [11, 25], [1], [5, 31], [1]], ![[5, 5], [6, 18], [1], [16, 12], [1]]]
 h' := ![![[17, 42], [36, 9], [7, 38], [32, 1], [15, 17], [0, 1]], ![[0, 1], [17, 34], [8, 5], [6, 42], [3, 26], [17, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [12, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [28, 26, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2178, -11, 83]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![41, -35, 83]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11310330451384274, -119701008490156, 1568245086298713]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-11310330451384274, -119701008490156, 1568245086298713]] 
 ![![43, 0, 0], ![32, 1, 0], ![17, 0, 1]] where
  M :=![![![-11310330451384274, -119701008490156, 1568245086298713], ![221122557168118533, -45811722349955960, -359103025470468], ![-16877842197111996, 76340941242822943, -45811722349955960]]]
  hmulB := by decide  
  f := ![![![2126128167637015374310744938868924, 114237596621515096961502774242599, 71886993464500044801119201392488]], ![![1817957382392534844067480126515032, 97679474495499941661725843813892, 61467362342524342430705180634591]], ![![1215155348220067210112896630906469, 65290714179626200484769502191487, 41085888379407329076863928648988]]]
  g := ![![![-793954991785521, -119701008490156, 1568245086298713], ![39376800553481563, -45811722349955960, -359103025470468], ![-39092760046934764, 76340941242822943, -45811722349955960]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-2126128167637015374310744938868924, -114237596621515096961502774242599, -71886993464500044801119201392488]] ![![-11310330451384274, -119701008490156, 1568245086298713]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-738582158, -39684273, -24972366]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-738582158, -39684273, -24972366]] 
 ![![47, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-738582158, -39684273, -24972366], ![-3521103606, -189190106, -119052819], ![-5595482493, -300647196, -189190106]]]
  hmulB := by decide  
  f := ![![![-45712, 17202, -4791]], ![![-14373, 1270, 1098]], ![![51606, -12843, 1270]]]
  g := ![![![-15714514, -39684273, -24972366], ![-74917098, -189190106, -119052819], ![-119052819, -300647196, -189190106]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1785016402457521407403888, 1378626511066457411379753, -631921468305243547740380]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-1785016402457521407403888, 1378626511066457411379753, -631921468305243547740380]] 
 ![![47, 0, 0], ![13, 1, 0], ![22, 0, 1]] where
  M :=![![![-1785016402457521407403888, 1378626511066457411379753, -631921468305243547740380], ![-89100927031039340231393580, 12117255900257836642884472, 4135879533199372234139259], ![194386338060370495004545173, -60030092253808509794152426, 12117255900257836642884472]]]
  hmulB := by decide  
  f := ![![![395105120480930145731615292453924761319191895411118, 21229133814053993639203045399832599032422296266464, 13358987311367126947845114704671012808790524402387]], ![![149361356960741633918237446282119887301892735767683, 8025237004543729152950262960616729083984898085588, 5050090138083715558289268667238743906628589490009]], ![![248630223794937793813258847560909387501995010055660, 13358987311367126947845114704671012808790524402387, 8406491925126173313438623243700526836578550966194]]]
  g := ![![![-123508271140555525639411, 1378626511066457411379753, -631921468305243547740380], ![-7183289435420795866807562, 12117255900257836642884472, 4135879533199372234139259], ![15068040586259759918831241, -60030092253808509794152426, 12117255900257836642884472]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![353731809676727798580141636240583694963678, 19006131615743456165954089296154920977773, 11960105076204436620844069284190387426492]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![353731809676727798580141636240583694963678, 19006131615743456165954089296154920977773, 11960105076204436620844069284190387426492]] 
 ![![47, 0, 0], ![34, 1, 0], ![22, 0, 1]] where
  M :=![![![353731809676727798580141636240583694963678, 19006131615743456165954089296154920977773, 11960105076204436620844069284190387426492], ![1686374815744825563539013769070844627135372, 90609498000230192921572111988395171580854, 57018394847230368497862267888464762933319], ![2679864557819827319399526590757843857865993, 143990043035252485528681291841539947534118, 90609498000230192921572111988395171580854]]]
  hmulB := by decide  
  f := ![![![-2015219039393052108326, 296755543423580695914, 79259976858720534419]], ![![-1220038097920939921915, 134696807364188080756, 76278847733345537404]], ![![-53027388168558899134, 79259976858720534419, -42877000838150044858]]]
  g := ![![![-11821254828405262057890785618741960460924, 19006131615743456165954089296154920977773, 11960105076204436620844069284190387426492], ![-56356442614937640483987402810230127471206, 90609498000230192921572111988395171580854, 57018394847230368497862267888464762933319], ![-89557571518804711337238804161685279427081, 143990043035252485528681291841539947534118, 90609498000230192921572111988395171580854]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-738582158, -39684273, -24972366]] ![![-1785016402457521407403888, 1378626511066457411379753, -631921468305243547740380]]
  ![![2015219039393052108326, -296755543423580695914, -79259976858720534419]] where
 M := ![![![2015219039393052108326, -296755543423580695914, -79259976858720534419]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![2015219039393052108326, -296755543423580695914, -79259976858720534419]] ![![353731809676727798580141636240583694963678, 19006131615743456165954089296154920977773, 11960105076204436620844069284190387426492]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [21, 22, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 35, 31], [25, 17, 22], [0, 1]]
 g := ![![[20, 8, 44], [17, 29], [52, 16, 15], [5, 46], [1]], ![[19, 2, 45, 20], [48, 52], [17, 26, 27, 22], [30, 52], [47, 29, 32, 5]], ![[18, 13, 12, 18], [43, 9], [27, 27, 6, 45], [52, 1], [18, 46, 0, 48]]]
 h' := ![![[4, 35, 31], [31, 20, 16], [21, 10, 33], [18, 7, 42], [32, 31, 29], [0, 1]], ![[25, 17, 22], [0, 3, 44], [1, 42, 23], [13, 12, 30], [31, 37, 23], [4, 35, 31]], ![[0, 1], [38, 30, 46], [26, 1, 50], [45, 34, 34], [36, 38, 1], [25, 17, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 15], []]
 b := ![[], [0, 15, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [21, 22, 24, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-285034, 82627, -14151]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5378, 1559, -267]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-946, -51, -32]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-946, -51, -32]] 
 ![![59, 0, 0], ![0, 59, 0], ![48, 44, 1]] where
  M :=![![![-946, -51, -32], ![-4512, -242, -153], ![-7191, -382, -242]]]
  hmulB := by decide  
  f := ![![![-2, 2, -1]], ![![-141, 20, 6]], ![![-102, 15, 4]]]
  g := ![![![10, 23, -32], ![48, 110, -153], ![75, 174, -242]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [6, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 58], [0, 1]]
 g := ![![[45, 5], [50, 26], [53], [53, 15], [25, 1]], ![[52, 54], [51, 33], [53], [15, 44], [50, 58]]]
 h' := ![![[25, 58], [54, 8], [34, 12], [36, 17], [27, 29], [0, 1]], ![[0, 1], [18, 51], [39, 47], [48, 42], [44, 30], [25, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [13, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [6, 34, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![288, -31, -53]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![48, 39, -53]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 2, -1]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-2, 2, -1]] 
 ![![59, 0, 0], ![45, 1, 0], ![33, 0, 1]] where
  M :=![![![-2, 2, -1], ![-141, 20, 6], ![282, -91, 20]]]
  hmulB := by decide  
  f := ![![![-946, -51, -32]], ![![-798, -43, -27]], ![![-651, -35, -22]]]
  g := ![![![-1, 2, -1], ![-21, 20, 6], ![63, -91, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-946, -51, -32]] ![![-2, 2, -1]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1568, -2390, 1297]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![1568, -2390, 1297]] 
 ![![61, 0, 0], ![0, 61, 0], ![37, 26, 1]] where
  M :=![![![1568, -2390, 1297], ![182877, -26966, -7170], ![-336990, 113539, -26966]]]
  hmulB := by decide  
  f := ![![![-25266226, -1357563, -854282]], ![![-120453762, -6472022, -4072689]], ![![-69804337, -3750611, -2360170]]]
  g := ![![![-761, -592, 1297], ![7347, 2614, -7170], ![10832, 13355, -26966]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [11, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 60], [0, 1]]
 g := ![![[29, 42], [5], [9, 52], [11, 4], [47, 1]], ![[51, 19], [5], [13, 9], [16, 57], [33, 60]]]
 h' := ![![[47, 60], [47, 15], [23, 35], [1, 33], [32, 2], [0, 1]], ![[0, 1], [20, 46], [21, 26], [27, 28], [4, 59], [47, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [28, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [11, 14, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5384, -485, 1077]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-565, -467, 1077]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25266226, 1357563, 854282]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![25266226, 1357563, 854282]] 
 ![![61, 0, 0], ![44, 1, 0], ![46, 0, 1]] where
  M :=![![![25266226, 1357563, 854282], ![120453762, 6472022, 4072689], ![191416383, 10284868, 6472022]]]
  hmulB := by decide  
  f := ![![![-1568, 2390, -1297]], ![![-4129, 2166, -818]], ![![4342, -59, -536]]]
  g := ![![![-1209238, 1357563, 854282], ![-5764900, 6472022, 4072689], ![-9161161, 10284868, 6472022]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![1568, -2390, 1297]] ![![25266226, 1357563, 854282]]
  ![![61, 0, 0]] where
 M := ![![![-61, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [63, 51, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 22, 52], [4, 44, 15], [0, 1]]
 g := ![![[26, 14, 33], [59, 37, 33], [27, 14], [41, 15], [41, 1], []], ![[45, 52, 6, 11], [44, 0, 28, 30], [37, 64], [16, 39], [61, 60], [56, 24]], ![[13, 10, 30, 1], [13, 65, 19, 33], [57, 1], [23, 1], [39, 15], [26, 24]]]
 h' := ![![[37, 22, 52], [35, 57, 10], [38, 39, 57], [59, 49, 58], [30, 57, 22], [0, 0, 1], [0, 1]], ![[4, 44, 15], [51, 51, 54], [23, 51, 47], [64, 10, 8], [0, 1, 46], [52, 7, 44], [37, 22, 52]], ![[0, 1], [56, 26, 3], [66, 44, 30], [46, 8, 1], [17, 9, 66], [53, 60, 22], [4, 44, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 41], []]
 b := ![[], [64, 23, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [63, 51, 26, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-42545, 4958, 2680]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-635, 74, 40]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41826135476197, 2247332623450, 1414192791098]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![41826135476197, 2247332623450, 1414192791098]] 
 ![![71, 0, 0], ![0, 71, 0], ![27, 7, 1]] where
  M :=![![![41826135476197, 2247332623450, 1414192791098], ![199401183544818, 10713894072041, 6741997870350], ![316873899906450, 17025743465706, 10713894072041]]]
  hmulB := by decide  
  f := ![![![3361811, -575722, -81458]], ![![-11485578, 5153887, -1727166]], ![![-997281, 413663, -128671]]]
  g := ![![![51308874881, -107774886116, 1414192791098], ![244609028808, -513804098879, 6741997870350], ![388714929033, -816500211811, 10713894072041]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [17, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 70], [0, 1]]
 g := ![![[7, 38], [18, 45], [41, 64], [57], [32], [1]], ![[29, 33], [59, 26], [22, 7], [57], [32], [1]]]
 h' := ![![[23, 70], [49, 31], [13, 51], [14, 63], [29, 25], [54, 23], [0, 1]], ![[0, 1], [52, 40], [50, 20], [43, 8], [36, 46], [15, 48], [23, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [25, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [17, 48, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![581, 148, 11]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, 1, 11]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3361811, -575722, -81458]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![3361811, -575722, -81458]] 
 ![![71, 0, 0], ![50, 1, 0], ![66, 0, 1]] where
  M :=![![![3361811, -575722, -81458], ![-11485578, 5153887, -1727166], ![-81176802, 8837358, 5153887]]]
  hmulB := by decide  
  f := ![![![41826135476197, 2247332623450, 1414192791098]], ![![32263492357108, 1733528524571, 1090868132750]], ![![43343645652612, 2328868966386, 1465501665979]]]
  g := ![![![528509, -575722, -81458], ![-2185732, 5153887, -1727166], ![-12157764, 8837358, 5153887]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![41826135476197, 2247332623450, 1414192791098]] ![![3361811, -575722, -81458]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7829433873354138114634774, -1038572117566974386592873, -379906494302224638616338]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![7829433873354138114634774, -1038572117566974386592873, -379906494302224638616338]] 
 ![![73, 0, 0], ![0, 73, 0], ![24, 5, 1]] where
  M :=![![![7829433873354138114634774, -1038572117566974386592873, -379906494302224638616338], ![-53566815696613674044903658, 16187376748003080164194210, -3115716352700923159778619], ![-146438668576943388509595093, 4992981354268878490075320, 16187376748003080164194210]]]
  hmulB := by decide  
  f := ![![![3802573693644070151291690116975787488174499083660, 204313590474127382808302954525749853906043442290, 128569666882819775013250811360396957823910605279]], ![![18128323030477588276868364401815971053171395344339, 974041022222035101000172267047054416048465767522, 612940771422382148424908863577249561718130326870]], ![![2886460274749281999881001389104513484695850412225, 155090501856862461592332265455142860353126221511, 97594751842761923882777206268257934416616053816]]]
  g := ![![![232153284063116841663382, 11793977451289709677929, -379906494302224638616338], ![290553106413814819038126, 435150116595995835110785, -3115716352700923159778619], ![-7327886445602976882880221, -1040327429941733182615010, 16187376748003080164194210]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [34, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 72], [0, 1]]
 g := ![![[54, 48], [61], [12], [59, 1], [48], [1]], ![[37, 25], [61], [12], [48, 72], [48], [1]]]
 h' := ![![[62, 72], [20, 62], [14, 34], [38, 31], [35, 1], [39, 62], [0, 1]], ![[0, 1], [68, 11], [5, 39], [62, 42], [24, 72], [14, 11], [62, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [64, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [34, 11, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5580, 918, 242]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-156, -4, 242]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18668647460416348962688020815447, 3274878020985179210704908352850, 403387039844922811093579303224]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-18668647460416348962688020815447, 3274878020985179210704908352850, 403387039844922811093579303224]] 
 ![![73, 0, 0], ![58, 1, 0], ![71, 0, 1]] where
  M :=![![![-18668647460416348962688020815447, 3274878020985179210704908352850, 403387039844922811093579303224], ![56877572618134116364194681754584, -27543162337004650806746765486375, 9824634062955537632114725058550], ![461757800958910268709392077751850, -53088125588962570514109756511172, -27543162337004650806746765486375]]]
  hmulB := by decide  
  f := ![![![1280197198522374680754134378620169827277552530069715341739761225, 68785435133636203786446972986095546965016116770348057435800222, 43285032880087884026653760428961170415863211841308804274940500]], ![![1100748317128631823719150331239087328914174789228329194844832350, 59143585108374534955913370991459805508212282770426150396814837, 37217646745835697053496698956685404452261844343930887948684242]], ![![1377982841766182288594966631137966162448952083555737881670833949, 74039491327565815545049704335340504257963844908062583770909786, 46591285063653164356988611501907769556915752195806119879614325]]]
  g := ![![![-3250028116528030996865984052187, 3274878020985179210704908352850, 403387039844922811093579303224], ![13107287256089872483224131517908, -27543162337004650806746765486375, 9824634062955537632114725058550], ![75293611110220131038449017875787, -53088125588962570514109756511172, -27543162337004650806746765486375]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![7829433873354138114634774, -1038572117566974386592873, -379906494302224638616338]] ![![-18668647460416348962688020815447, 3274878020985179210704908352850, 403387039844922811093579303224]]
  ![![73, 0, 0]] where
 M := ![![![-380661189211379400303279942127985102980765342511091759110, 74414525023017176101525039188081280044064454868944339411, 3418527396198039816540812039713654801418609751814391976]]]
 hmul := by decide  
 g := ![![![![-5214536838512046579496985508602535657270758116590298070, 1019377055109824330157877249151798356768006231081429307, 46829142413671778308778247119365134266008352764580712]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [74, 20, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 54, 50], [78, 24, 29], [0, 1]]
 g := ![![[15, 11, 9], [25, 30, 26], [10, 50, 73], [41, 56, 25], [74, 1], []], ![[73, 10, 54, 11], [28, 70, 65, 50], [76, 6, 29, 44], [68, 37, 63, 42], [38, 23], [10, 51]], ![[8, 4, 18, 47], [4, 63, 12, 59], [15, 0, 18, 48], [46, 0, 5, 24], [66, 72], [31, 51]]]
 h' := ![![[75, 54, 50], [46, 17, 76], [50, 47, 37], [47, 6, 28], [54, 26, 5], [0, 0, 1], [0, 1]], ![[78, 24, 29], [17, 74, 67], [13, 44, 78], [54, 38, 24], [43, 72, 77], [66, 18, 24], [75, 54, 50]], ![[0, 1], [35, 67, 15], [8, 67, 43], [64, 35, 27], [18, 60, 76], [77, 61, 54], [78, 24, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 14], []]
 b := ![[], [17, 40, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [74, 20, 5, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6478, 316, -316]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![82, 4, -4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB231I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB231I1 : PrimesBelowBoundCertificateInterval O 31 79 231 where
  m := 11
  g := ![2, 2, 2, 3, 1, 2, 2, 1, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB231I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I41N1, I43N1, I47N0, I47N1, I47N2, I59N1, I61N1, I71N1, I73N1]
  Il := ![[I37N1], [I41N1], [I43N1], [I47N0, I47N1, I47N2], [], [I59N1], [I61N1], [], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
