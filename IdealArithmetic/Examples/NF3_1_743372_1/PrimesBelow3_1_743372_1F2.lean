
import IdealArithmetic.Examples.NF3_1_743372_1.RI3_1_743372_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [66, 49, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 7, 9], [61, 75, 74], [0, 1]]
 g := ![![[77, 46, 11], [41, 55, 29], [35, 29], [59, 68], [55, 42, 1], []], ![[73, 17, 16, 38], [42, 51, 9, 12], [14, 59], [21, 69], [51, 33, 71, 78], [42, 81]], ![[14, 68, 0, 34], [28, 6], [38, 16], [41, 21], [55, 17, 42, 57], [60, 81]]]
 h' := ![![[64, 7, 9], [33, 73, 54], [63, 24, 19], [76, 77, 64], [22, 11, 20], [0, 0, 1], [0, 1]], ![[61, 75, 74], [7, 3, 59], [29, 20, 64], [17, 23, 15], [65, 61, 22], [79, 49, 75], [64, 7, 9]], ![[0, 1], [46, 7, 53], [57, 39], [18, 66, 4], [63, 11, 41], [10, 34, 7], [61, 75, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 40], []]
 b := ![[], [25, 79, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [66, 49, 41, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-867433, 79265, 19920]
  a := ![-1, -1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10451, 955, 240]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22873578870321887380657394067156278, -1298852459438716209947529334282689, 336436782701281880301333923772778]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-22873578870321887380657394067156278, -1298852459438716209947529334282689, 336436782701281880301333923772778]] 
 ![![89, 0, 0], ![7, 1, 0], ![81, 0, 1]] where
  M :=![![![-22873578870321887380657394067156278, -1298852459438716209947529334282689, 336436782701281880301333923772778], ![-59165979084059199621776964223200505, -19509211043309068577644054829428498, -7456677973931015379383842081923356], ![214318829890524577342839029554757502, -22072317727321772867611309284691896, -20808063502747784787591584163711187]]]
  hmulB := by decide  
  f := ![![![-241362736846756111124181091885268472819270874135796983279302392884150, 34452544019641555504977880833985539285002294578649713556508451748931, -16248740722134024588728973299152216683734341137395696437335485411728]], ![![12805581913476415807832512866194241563510256755731804694641519015473, -1827891414950623241310400663358335557995485656845010705135933536617, 862082453267158835056578636075230362248753240143064155509739631458]], ![![-281320261308628920045159344573878080954163014177726096331852690093434, 40156151744775283312906398145728021633663326037829300420790193429993, -18938714590351806665095952598585782603978580034383771297981158579803]]]
  g := ![![![-461044843292749508038570073626657, -1298852459438716209947529334282689, 336436782701281880301333923772778], ![7656060832668725012941827283354953, -19509211043309068577644054829428498, -7456677973931015379383842081923356], ![23081777502296039946191421480991089, -22072317727321772867611309284691896, -20808063502747784787591584163711187]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![120309809885162052949238497140, -10519481272144200034828550813, -10716073771095514291661765664]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![120309809885162052949238497140, -10519481272144200034828550813, -10716073771095514291661765664]] 
 ![![89, 0, 0], ![29, 1, 0], ![38, 0, 1]] where
  M :=![![![120309809885162052949238497140, -10519481272144200034828550813, -10716073771095514291661765664], ![1832645207356284258130995143395, 13149072174206910032620840500, -73832961403960714500633070542], ![2098684770628381291865378412764, 184139179098136885526582164798, 2629590902062709997792289687]]]
  hmulB := by decide  
  f := ![![![13630117583869610625763347881341400358100208301485625104016, -1945587095116954586126768773794589955887859484972810530341, 917590882196170814061348349920967794080548395713981042646]], ![![2646092034824273860027622512344938874687234350509051439899, -377707857893936676756173742241483487885867784332427751117, 178137122417790976461571211852376338057183089455983911206]], ![![9301241513796233490035449922873893882925224047050558168762, -1327675667246184630491475354943892677784180471494071838290, 626167335215380394545857302289362522675041256300942748547]]]
  g := ![![![9354894045831161764521500741, -10519481272144200034828550813, -10716073771095514291661765664], ![47831175816345966496730870219, 13149072174206910032620840500, -73832961403960714500633070542], ![-37542425589842374924961925556, 184139179098136885526582164798, 2629590902062709997792289687]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-62139554164241692, 2949454737324077, 4254120475413955]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![-62139554164241692, 2949454737324077, 4254120475413955]] 
 ![![89, 0, 0], ![52, 1, 0], ![39, 0, 1]] where
  M :=![![![-62139554164241692, 2949454737324077, 4254120475413955], ![-728759267033876183, -19598349410102142, 21950848899358417], ![-622167467655918029, -85366705462936015, -16648894672778065]]]
  hmulB := by decide  
  f := ![![![2200162507742035873295465169803485, -314055088364673576983503001118320, 148116774784330213393844988897719]], ![![995711348891195450906060086946688, -142129599318850426920317314599685, 67032118352600672449132206796283]], ![![1526119776196475713910694866454478, -217841036506133944200286087135237, 102739655997860030928206366569364]]]
  g := ![![![-4285639315126269, 2949454737324077, 4254120475413955], ![-6356496682961158, -19598349410102142, 21950848899358417], ![50182113580394374, -85366705462936015, -16648894672778065]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-22873578870321887380657394067156278, -1298852459438716209947529334282689, 336436782701281880301333923772778]] ![![120309809885162052949238497140, -10519481272144200034828550813, -10716073771095514291661765664]]
  ![![-4426176908000581605952897940768045988750871412595892505026295683, 285490672805490854920167888325984617554022099799895337657118358, 341897773193429664501617281308733668612663659486446056149626516]] where
 M := ![![![-4426176908000581605952897940768045988750871412595892505026295683, 285490672805490854920167888325984617554022099799895337657118358, 341897773193429664501617281308733668612663659486446056149626516]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![-4426176908000581605952897940768045988750871412595892505026295683, 285490672805490854920167888325984617554022099799895337657118358, 341897773193429664501617281308733668612663659486446056149626516]] ![![-62139554164241692, 2949454737324077, 4254120475413955]]
  ![![89, 0, 0]] where
 M := ![![![-145730985488473275005870605032171785476792759043092983770158072278501554740908842, -47836640911141116847132400637116364547487896951678680636335226828450972415756167, -18254947205954974957017593476069949336614431210626691700925820112618912329108519]]]
 hmul := by decide  
 g := ![![![![-1637426803241272752874950618339008825581941112843741390675933396387657918437178, -537490347316192324125083153226026567949302212940209894790283447510685083323103, -205111766359044662438399926697415161085555406860974064055346293400212498079871]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [26, 90, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 26, 90], [19, 70, 7], [0, 1]]
 g := ![![[54], [32, 73], [21, 85], [25, 32], [18, 50], [1]], ![[65, 36, 31, 5], [53, 33], [89, 89], [70, 66], [41, 1], [90, 51, 85, 45]], ![[32, 19, 82, 92], [12, 88], [78, 33], [37, 4], [83, 94], [65, 92, 59, 52]]]
 h' := ![![[51, 26, 90], [91, 65], [27, 34, 48], [31, 26, 52], [14, 14, 56], [71, 7, 70], [0, 1]], ![[19, 70, 7], [11, 41, 30], [15, 37, 18], [96, 9, 63], [49, 71, 39], [40, 34, 1], [51, 26, 90]], ![[0, 1], [65, 88, 67], [59, 26, 31], [70, 62, 79], [81, 12, 2], [28, 56, 26], [19, 70, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89, 36], []]
 b := ![[], [6, 67, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [26, 90, 27, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11509147, -1454321, 322234]
  a := ![2, -2, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![118651, -14993, 3322]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-536638928672590988521712743076555307234524437, 76600789973989766598795223495589263293763524, -36126980193056662057482282852085555675951288]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-536638928672590988521712743076555307234524437, 76600789973989766598795223495589263293763524, -36126980193056662057482282852085555675951288]] 
 ![![101, 0, 0], ![0, 101, 0], ![54, 19, 1]] where
  M :=![![![-536638928672590988521712743076555307234524437, 76600789973989766598795223495589263293763524, -36126980193056662057482282852085555675951288], ![6290441383179735640485747874054304839557385060, -897908730603157609096535571597410863994037317, 423477759650881937535289058121450024086629856], ![-12199907410313709979440756804235043283276641352, 1741436364952427541539973871962202636188320016, -821307940629167842497740348101821600700273793]]]
  hmulB := by decide  
  f := ![![![-27681648578850549417185, -2528907056026245793524, -86303225654574613448]], ![![12315247756560587719532, -28544680835396295551665, -15259745561812049374592]], ![![-8153634803505848621858, -6949196043223127046575, -3224446809417807015729]]]
  g := ![![![14002158433192760025567629019168957418483615, 7554588253881845006841174234507077436998396, -36126980193056662057482282852085555675951288], ![-164132253841266227588315458064396004565550764, -88554318455147667547198293820841201204356481, 423477759650881937535289058121450024086629856], ![318323974095656965499378435576864585688496470, 171745418187194223257396440454423891579143783, -821307940629167842497740348101821600700273793]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [21, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 100], [0, 1]]
 g := ![![[34, 77], [95], [60, 25], [87], [77], [94, 1]], ![[0, 24], [95], [87, 76], [87], [77], [87, 100]]]
 h' := ![![[94, 100], [6, 73], [53, 87], [27, 96], [95, 17], [46, 28], [0, 1]], ![[0, 1], [0, 28], [50, 14], [62, 5], [77, 84], [52, 73], [94, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [81, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [21, 7, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2753516, -2876095, 1102212]
  a := ![-65, 1, -326]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-616564, -235823, 1102212]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27681648578850549417185, -2528907056026245793524, -86303225654574613448]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-27681648578850549417185, -2528907056026245793524, -86303225654574613448]] 
 ![![101, 0, 0], ![87, 1, 0], ![18, 0, 1]] where
  M :=![![![-27681648578850549417185, -2528907056026245793524, -86303225654574613448], ![12315247756560587719532, -28544680835396295551665, -15259745561812049374592], ![437302200729187791049224, -22958883467588943372144, -31073587891422541345189]]]
  hmulB := by decide  
  f := ![![![-536638928672590988521712743076555307234524437, 76600789973989766598795223495589263293763524, -36126980193056662057482282852085555675951288]], ![![-399971736745897825355477829441643632572735059, 57092673238950020643550978935830247946172171, -26926430862822254073917520297128646729912200]], ![![-216429783429904433394372140392208305084139418, 30893570143408349904141464305770389856198648, -14570233505982057025073479598409520820469277]]]
  g := ![![![1919670528289259184767, -2528907056026245793524, -86303225654574613448], ![27429484163848071182743, -28544680835396295551665, -15259745561812049374592], ![29644055885693382263754, -22958883467588943372144, -31073587891422541345189]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-536638928672590988521712743076555307234524437, 76600789973989766598795223495589263293763524, -36126980193056662057482282852085555675951288]] ![![-27681648578850549417185, -2528907056026245793524, -86303225654574613448]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [75, 41, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 40, 49], [101, 62, 54], [0, 1]]
 g := ![![[9, 44, 25], [92, 0, 15], [31, 77, 4], [10, 33], [0, 82], [1]], ![[59, 6, 24, 1], [99, 72, 37, 66], [1, 100, 1, 7], [17, 59], [60, 4], [44, 94, 11, 23]], ![[0, 92, 25, 43], [36, 47, 41, 43], [41, 85, 52, 85], [11, 64], [79, 13], [52, 50, 99, 80]]]
 h' := ![![[46, 40, 49], [1, 18, 5], [44, 16, 18], [26, 102, 101], [63, 0, 62], [28, 62, 44], [0, 1]], ![[101, 62, 54], [73, 88, 59], [36, 54, 46], [97, 48, 33], [41, 53, 33], [100, 29, 101], [46, 40, 49]], ![[0, 1], [0, 100, 39], [35, 33, 39], [14, 56, 72], [85, 50, 8], [6, 12, 61], [101, 62, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 68], []]
 b := ![[], [91, 91, 89], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [75, 41, 59, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10494670, 973968, -89610]
  a := ![-2, 1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-101890, 9456, -870]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![12, 1, 0]] 
 ![![107, 0, 0], ![12, 1, 0], ![101, 0, 1]] where
  M :=![![![12, 1, 0], ![1, 12, 6], ![-172, 10, 13]]]
  hmulB := by decide  
  f := ![![![96, -13, 6]], ![![1, 0, 0]], ![![110, -15, 7]]]
  g := ![![![0, 1, 0], ![-7, 12, 6], ![-15, 10, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10029839034181664143226911463091391412633075, -1431676966169217222181754743446798096601888, 675217127880969876776767367742080108205064]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![10029839034181664143226911463091391412633075, -1431676966169217222181754743446798096601888, 675217127880969876776767367742080108205064]] 
 ![![107, 0, 0], ![38, 1, 0], ![27, 0, 1]] where
  M :=![![![10029839034181664143226911463091391412633075, -1431676966169217222181754743446798096601888, 675217127880969876776767367742080108205064], ![-117569022961696036027785741995084576707872896, 16782010312991362910994585140512192494683715, -7914844669134333456313761092938708471406264], ![228017575728319175542289096943813109693988008, -32547632114478358894790266363504143887555608, 15350333346822145688812830397065394398081827]]]
  hmulB := by decide  
  f := ![![![-50530398307398205181207, -2398171743529300509536, 986156667340076093672]], ![![-19553011721562188649598, -1231769699888886575765, 224963360421375370056]], ![![-9144499480662559876463, -1078117612418375452168, -153652087470511123597]]]
  g := ![![![431800946689960111337952082103117347308113, -1431676966169217222181754743446798096601888, 675217127880969876776767367742080108205064], ![-5061538399894774049767368484347689371755934, 16782010312991362910994585140512192494683715, -7914844669134333456313761092938708471406264], ![9816528931909335326601614934917803071709269, -32547632114478358894790266363504143887555608, 15350333346822145688812830397065394398081827]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2799437733259727538832, -48386550071929266207, 98190459059357822378]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![-2799437733259727538832, -48386550071929266207, 98190459059357822378]] 
 ![![107, 0, 0], ![56, 1, 0], ![66, 0, 1]] where
  M :=![![![-2799437733259727538832, -48386550071929266207, 98190459059357822378], ![-16937145508281474715223, -1817533142666149315052, -192128841372217774864], ![5671344217769172583398, -3135007895321953866276, -1865919692738078581259]]]
  hmulB := by decide  
  f := ![![![2789045448483933690937195562012120243724004, -398113281039243755186471780849384664538941, 187760865437305065007447319966252827054504]], ![![1154145448400416558467434959417138904024585, -164744762947109027564773373512998997195436, 77698034053186225928090341616636478082926]], ![![2312924678241890773259130614577619365009444, -330150960054109926629653579286374400331132, 155708018137195092302025421482223835844181]]]
  g := ![![![-61405245113544905684, -48386550071929266207, 98190459059357822378], ![911450598239151963259, -1817533142666149315052, -192128841372217774864], ![2844696131556184817364, -3135007895321953866276, -1865919692738078581259]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![12, 1, 0]] ![![10029839034181664143226911463091391412633075, -1431676966169217222181754743446798096601888, 675217127880969876776767367742080108205064]]
  ![![2789045448483933690937195562012120243724004, -398113281039243755186471780849384664538941, 187760865437305065007447319966252827054504]] where
 M := ![![![2789045448483933690937195562012120243724004, -398113281039243755186471780849384664538941, 187760865437305065007447319966252827054504]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![2789045448483933690937195562012120243724004, -398113281039243755186471780849384664538941, 187760865437305065007447319966252827054504]] ![![-2799437733259727538832, -48386550071929266207, 98190459059357822378]]
  ![![107, 0, 0]] where
 M := ![![![107, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-335091910147185037695006363301114, 47831612020133694361108081121295, -22558666831505224952025821523444]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-335091910147185037695006363301114, 47831612020133694361108081121295, -22558666831505224952025821523444]] 
 ![![109, 0, 0], ![0, 109, 0], ![43, 42, 1]] where
  M :=![![![-335091910147185037695006363301114, 47831612020133694361108081121295, -22558666831505224952025821523444], ![3927922307039032386109549383153663, -560678578462237287215264578535554, 264431005289296941214622665204326], ![-7617953263012354356405892771729752, 1087400124651978017315777992345938, -512846966442103592854156497414259]]]
  hmulB := by decide  
  f := ![![![25412714816037278, -1009229268040137, -1638205023543066]], ![![280762034781367215, 9030664580606618, -7693580631783888]], ![![120207074932528370, 3394773365275353, -3537172176465217]]]
  g := ![![![5825052877133391149010128093642, 9131152467370212315102684267027, -22558666831505224952025821523444], ![-68280834132116844826781882758095, -107034686244153291910361619423094, 264431005289296941214622665204326], ![132426296275211927856172813000765, 207586905644223201075140833795824, -512846966442103592854156497414259]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [16, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 108], [0, 1]]
 g := ![![[38, 75], [38], [42, 34], [38, 89], [78], [46, 1]], ![[0, 34], [38], [80, 75], [99, 20], [78], [92, 108]]]
 h' := ![![[46, 108], [43, 82], [91, 16], [46, 19], [26, 31], [27, 29], [0, 1]], ![[0, 1], [0, 27], [64, 93], [48, 90], [35, 78], [53, 80], [46, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [32, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [16, 63, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3081, -913, 12]
  a := ![-1, -1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33, -13, 12]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25412714816037278, -1009229268040137, -1638205023543066]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![25412714816037278, -1009229268040137, -1638205023543066]] 
 ![![109, 0, 0], ![74, 1, 0], ![14, 0, 1]] where
  M :=![![![25412714816037278, -1009229268040137, -1638205023543066], ![280762034781367215, 9030664580606618, -7693580631783888], ![217818969738566346, 34139242955261412, 8021435312566481]]]
  hmulB := by decide  
  f := ![![![-335091910147185037695006363301114, 47831612020133694361108081121295, -22558666831505224952025821523444]], ![![-191457605906905141314870839459897, 27328997348877578857859939673764, -12889085690294400965461358968170]], ![![-112928807385990320037944787687572, 16119657733338070994232028697652, -7602461487001621487913009162775]]]
  g := ![![![1128720651198260, -1009229268040137, -1638205023543066], ![-2566945094849065, 9030664580606618, -7693580631783888], ![-22209037645199164, 34139242955261412, 8021435312566481]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-335091910147185037695006363301114, 47831612020133694361108081121295, -22558666831505224952025821523444]] ![![25412714816037278, -1009229268040137, -1638205023543066]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![162342, -23173, 10929]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![162342, -23173, 10929]] 
 ![![113, 0, 0], ![0, 113, 0], ![33, 85, 1]] where
  M :=![![![162342, -23173, 10929], ![-1902961, 271632, -128109], ![3690673, -526813, 248459]]]
  hmulB := by decide  
  f := ![![![-633, 10, 33]], ![![-5666, -303, 93]], ![![-4470, -232, 77]]]
  g := ![![![-1755, -8426, 10929], ![20572, 98769, -128109], ![-39898, -191556, 248459]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [93, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [87, 112], [0, 1]]
 g := ![![[10, 41], [11], [99], [11], [89, 98], [87, 1]], ![[74, 72], [11], [99], [11], [27, 15], [61, 112]]]
 h' := ![![[87, 112], [111, 70], [2, 89], [100, 41], [85, 89], [45, 18], [0, 1]], ![[0, 1], [99, 43], [61, 24], [51, 72], [31, 24], [29, 95], [87, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [75, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [93, 26, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-74653, 1483, 4124]
  a := ![2, 19, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1865, -3089, 4124]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![633, -10, -33]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![633, -10, -33]] 
 ![![113, 0, 0], ![54, 1, 0], ![98, 0, 1]] where
  M :=![![![633, -10, -33], ![5666, 303, -93], ![2611, 791, 293]]]
  hmulB := by decide  
  f := ![![![-162342, 23173, -10929]], ![![-60739, 8670, -4089]], ![![-173453, 24759, -11677]]]
  g := ![![![39, -10, -33], ![-14, 303, -93], ![-609, 791, 293]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![162342, -23173, 10929]] ![![633, -10, -33]]
  ![![113, 0, 0]] where
 M := ![![![-113, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-264918361, 27752856, 25962756]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-264918361, 27752856, 25962756]] 
 ![![127, 0, 0], ![0, 127, 0], ![118, 63, 1]] where
  M :=![![![-264918361, 27752856, 25962756], ![-4437841176, -5290801, 192479892], ![-5474485644, -423465852, 22462055]]]
  hmulB := by decide  
  f := ![![![-640864718075527, 91478163525096, -43143547251804]], ![![7512168290835384, -1072300190593567, 505725433898772]], ![![3016340135741726, -430557726774675, 203062533329459]]]
  g := ![![![-26208847, -12660636, 25962756], ![-213783216, -95523811, 192479892], ![-63976442, -14476971, 22462055]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [42, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [108, 126], [0, 1]]
 g := ![![[70, 124], [63, 47], [11, 94], [121, 74], [97, 34], [108, 1]], ![[0, 3], [59, 80], [3, 33], [112, 53], [86, 93], [89, 126]]]
 h' := ![![[108, 126], [21, 88], [46, 38], [125, 27], [117, 57], [36, 65], [0, 1]], ![[0, 1], [0, 39], [86, 89], [120, 100], [50, 70], [71, 62], [108, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100]]
 b := ![[], [94, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [42, 19, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8102, -3882, 1033]
  a := ![-2, 3, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-896, -543, 1033]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-640864718075527, 91478163525096, -43143547251804]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-640864718075527, 91478163525096, -43143547251804]] 
 ![![127, 0, 0], ![2, 1, 0], ![63, 0, 1]] where
  M :=![![![-640864718075527, 91478163525096, -43143547251804], ![7512168290835384, -1072300190593567, 505725433898772], ![-14569368350517804, 2079657411049668, -980822027068471]]]
  hmulB := by decide  
  f := ![![![-264918361, 27752856, 25962756]], ![![-39115574, 395393, 1924452]], ![![-174522381, 10432788, 13056029]]]
  g := ![![![14915137257779, 91478163525096, -43143547251804], ![-174834123335434, -1072300190593567, 505725433898772], ![339079563249579, 2079657411049668, -980822027068471]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-264918361, 27752856, 25962756]] ![![-640864718075527, 91478163525096, -43143547251804]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![201903907916330723111305064548137146595465, -28820120976841370451136970386978468779818, 13592339452966280517246544648578495662280]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![201903907916330723111305064548137146595465, -28820120976841370451136970386978468779818, 13592339452966280517246544648578495662280]] 
 ![![131, 0, 0], ![37, 1, 0], ![34, 0, 1]] where
  M :=![![![201903907916330723111305064548137146595465, -28820120976841370451136970386978468779818, 13592339452966280517246544648578495662280], ![-2366702506887041619417542649942479722691978, 337827302445993528283770511033922103218265, -159328386408081942189575277673292317016628], ![4590067642786626143629902201048677247247136, -655194374998503278477026409381404070679740, 309007181469152157832633540646943634438447]]]
  hmulB := by decide  
  f := ![![![4203969602219905917735, 651134867358638655446, 150813601306609269504]], ![![994336417746247047763, 227512180973707090567, 73570427891625833388]], ![![205097725606965665570, 187618068156501149336, 87716816237170629247]]]
  g := ![![![6153502615714564062725117945150165182681, -28820120976841370451136970386978468779818, 13592339452966280517246544648578495662280], ![-72130897400870352148637344406913425673301, 337827302445993528283770511033922103218265, -159328386408081942189575277673292317016628], ![139893246929618886114277396688278964057178, -655194374998503278477026409381404070679740, 309007181469152157832633540646943634438447]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-86986456725179386004197901, 12416600708914136159318710, -5856000806628107275219429]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-86986456725179386004197901, 12416600708914136159318710, -5856000806628107275219429]] 
 ![![131, 0, 0], ![104, 1, 0], ![97, 0, 1]] where
  M :=![![![-86986456725179386004197901, 12416600708914136159318710, -5856000806628107275219429], ![1019648739448948587497060498, -145546464791460458756392191, 68643603446856709680692831], ![-1977543300154272522971893537, 282278028868100258024111683, -133129864082546322597073481]]]
  hmulB := by decide  
  f := ![![![-13223720142298, -14246140640503, -6763834089071]], ![![-1726210474193, -11927180821720, -6073888726683]], ![![10307319517317, -10242088000984, -5734351971858]]]
  g := ![![![-6185350016865062144099688, 12416600708914136159318710, -5856000806628107275219429], ![72504210255081950069730105, -145546464791460458756392191, 68643603446856709680692831], ![-140617263255188595920331152, 282278028868100258024111683, -133129864082546322597073481]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8318586199850729651149563248283736, -812866080444950318004697307354475, -785035762621926769333791424912133]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![8318586199850729651149563248283736, -812866080444950318004697307354475, -785035762621926769333791424912133]] 
 ![![131, 0, 0], ![120, 1, 0], ![111, 0, 1]] where
  M :=![![![8318586199850729651149563248283736, -812866080444950318004697307354475, -785035762621926769333791424912133], ![134213285090526454007407427777532401, 468228573631461957811648999162406, -5662232245291628677361975269038983], ![161008931427323477468820305337597291, 13067304786342519591965395399082841, -344637506813488360193048308192069]]]
  hmulB := by decide  
  f := ![![![-73828745392047067952864510680695623057895465094412036225972503232689, 10538445717697353853277234978678231516985296298708592355011779668628, -4970212707181368427274839145378578835267489666648985024170521370923]], ![![-61023163478570652145031997814501381494385208338680231531330984217216, 8710554302746730611966834315319895958989810641863581649875846132011, -4108130253914209592218260509303348473018736426505920868660781739465]], ![![-75369524113490629450345224770722506502256834869145735194598243395554, 10758379197979211937274550300345707191659870787353147103885720739839, -5073939215597673998472082536586453668765468843207867418286975644624]]]
  g := ![![![1473293782475409459601252582412729, -812866080444950318004697307354475, -785035762621926769333791424912133], ![5393386530397876353108311471308174, 468228573631461957811648999162406, -5662232245291628677361975269038983], ![-10448953279980776073172509773610870, 13067304786342519591965395399082841, -344637506813488360193048308192069]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![201903907916330723111305064548137146595465, -28820120976841370451136970386978468779818, 13592339452966280517246544648578495662280]] ![![-86986456725179386004197901, 12416600708914136159318710, -5856000806628107275219429]]
  ![![-73828745392047067952864510680695623057895465094412036225972503232689, 10538445717697353853277234978678231516985296298708592355011779668628, -4970212707181368427274839145378578835267489666648985024170521370923]] where
 M := ![![![-73828745392047067952864510680695623057895465094412036225972503232689, 10538445717697353853277234978678231516985296298708592355011779668628, -4970212707181368427274839145378578835267489666648985024170521370923]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![-73828745392047067952864510680695623057895465094412036225972503232689, 10538445717697353853277234978678231516985296298708592355011779668628, -4970212707181368427274839145378578835267489666648985024170521370923]] ![![8318586199850729651149563248283736, -812866080444950318004697307354475, -785035762621926769333791424912133]]
  ![![131, 0, 0]] where
 M := ![![![131, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25323, -21448, -9945]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-25323, -21448, -9945]] 
 ![![137, 0, 0], ![0, 137, 0], ![64, 28, 1]] where
  M :=![![![-25323, -21448, -9945], ![1689092, -124773, -138633], ![3957571, 54035, -146221]]]
  hmulB := by decide  
  f := ![![![187850124, -26814059, 12646227]], ![![-2201965103, 314312394, -148238127]], ![![-331109817, 47263201, -22290589]]]
  g := ![![![4461, 1876, -9945], ![77092, 27423, -138633], ![97195, 30279, -146221]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [49, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 136], [0, 1]]
 g := ![![[43, 14], [120], [25], [94, 74], [87], [101], [1]], ![[0, 123], [120], [25], [82, 63], [87], [101], [1]]]
 h' := ![![[85, 136], [110, 39], [109, 42], [52, 5], [132, 99], [55, 118], [88, 85], [0, 1]], ![[0, 1], [0, 98], [117, 95], [66, 132], [53, 38], [84, 19], [52, 52], [85, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [64, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [49, 52, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7858, -3592, 2142]
  a := ![2, 1, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1058, -464, 2142]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-187850124, 26814059, -12646227]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-187850124, 26814059, -12646227]] 
 ![![137, 0, 0], ![105, 1, 0], ![35, 0, 1]] where
  M :=![![![-187850124, 26814059, -12646227], ![2201965103, -314312394, 148238127], ![-4270570019, 609588719, -287498335]]]
  hmulB := by decide  
  f := ![![![25323, 21448, 9945]], ![![7079, 17349, 8634]], ![![-22418, 5085, 3608]]]
  g := ![![![-18691302, 26814059, -12646227], ![219098044, -314312394, 148238127], ![-424926597, 609588719, -287498335]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-25323, -21448, -9945]] ![![-187850124, 26814059, -12646227]]
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


lemma PB244I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB244I2 : PrimesBelowBoundCertificateInterval O 79 137 244 where
  m := 11
  g := ![1, 3, 1, 2, 1, 3, 2, 2, 2, 3, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB244I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N2]
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
    · exact ![89, 89, 89]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![131, 131, 131]
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
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
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
      exact NI107N2
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
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I89N0, I89N1, I89N2, I101N1, I107N0, I107N1, I107N2, I109N1, I113N1, I127N1, I131N0, I131N1, I131N2, I137N1]
  Il := ![[], [I89N0, I89N1, I89N2], [], [I101N1], [], [I107N0, I107N1, I107N2], [I109N1], [I113N1], [I127N1], [I131N0, I131N1, I131N2], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
