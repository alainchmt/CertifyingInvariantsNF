
import IdealArithmetic.Examples.NF3_1_837620_1.RI3_1_837620_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [26, 52, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 59, 32], [13, 23, 51], [0, 1]]
 g := ![![[52, 35, 33], [8, 69, 29], [21, 44], [71, 51], [69, 72, 1], []], ![[7, 30, 72, 62], [75, 1, 33, 56], [76, 63], [5, 49], [44, 4, 7, 79], [65, 28]], ![[13, 20, 49, 1], [76, 25, 5, 78], [55, 31], [21, 11], [12, 62, 18, 77], [46, 28]]]
 h' := ![![[59, 59, 32], [41, 38, 38], [16, 67, 19], [8, 35, 25], [32, 18, 36], [0, 0, 1], [0, 1]], ![[13, 23, 51], [40, 55, 15], [67, 79, 8], [36, 43, 35], [0, 56, 76], [48, 32, 23], [59, 59, 32]], ![[0, 1], [21, 73, 30], [49, 20, 56], [20, 5, 23], [63, 9, 54], [52, 51, 59], [13, 23, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 73], []]
 b := ![[], [58, 31, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [26, 52, 11, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3411466, -114540, 73870]
  a := ![-1, -5, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-41102, -1380, 890]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2003911569547769155215925083493999, -1227793826272780584240759259326850, -966535709911287720572622548751404]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![2003911569547769155215925083493999, -1227793826272780584240759259326850, -966535709911287720572622548751404]] 
 ![![89, 0, 0], ![0, 89, 0], ![70, 11, 1]] where
  M :=![![![2003911569547769155215925083493999, -1227793826272780584240759259326850, -966535709911287720572622548751404], ![167915955408202570515968186772168850, 1925414814013085421116000789943619, -9378331132993942680689724947014288], ![96946562988559500332272919434527462, 21603540489944506450365757076656714, 8586900178099974069656070507728761]]]
  hmulB := by decide  
  f := ![![![2462230350214686184207276577261656063889262111823512498970565886019, -116153374365774987204002460402076438311945224872256958490069539254, 150288081347950807800053765374332447233806660562461327931597967684]], ![![-26416567610257166352213411400910254704228110823302989346519713883954, 1246176446011832196390997908781688074472447909522178025352297890583, -1612397987701602295440185900143761724820872230409953568695489295592]], ![![-893979019767867142331810955681628561878045441431705147644495722194, 42172609784129967047639964319935743518871694596043536293429092831, -54566134169583258218192793966665389095948881914430302357219594527]]]
  g := ![![![782712486104920332531455095461711, 105664033514060498225371784010546, -966535709911287720572622548751404], ![9262911626042455709710662169249090, 1180753452549960167513516575360683, -9378331132993942680689724947014288], ![-5664454488521782972400584450634672, -818565859203991104672483354026513, 8586900178099974069656070507728761]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [7, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [88, 88], [0, 1]]
 g := ![![[51, 8], [69], [71], [22, 40], [13, 1], [1]], ![[43, 81], [69], [71], [71, 49], [12, 88], [1]]]
 h' := ![![[88, 88], [62, 50], [79, 43], [24, 58], [87, 29], [82, 88], [0, 1]], ![[0, 1], [12, 39], [36, 46], [55, 31], [58, 60], [83, 1], [88, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [33, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [7, 1, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9751, -8142, -1614]
  a := ![2, 6, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1379, 108, -1614]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1481410642206098041821140845722212, 269951726819361077948872668065471, 90104625229317261681095291354056]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![1481410642206098041821140845722212, 269951726819361077948872668065471, 90104625229317261681095291354056]] 
 ![![89, 0, 0], ![71, 1, 0], ![55, 0, 1]] where
  M :=![![![1481410642206098041821140845722212, 269951726819361077948872668065471, 90104625229317261681095291354056], ![-15498357688311159716242803318894329, 2110694423336956045211155061213816, 2429203392505658994445440806592542], ![-36248787915411482715959091366262593, -2791432637765881576641888001992251, 401241586060063022931236967463631]]]
  hmulB := by decide  
  f := ![![![-7627856011719750192066195535047344829890607961691887874192493117938, 359836850707432577098588423974024886035950064072714828457728805257, -465584320613966482058042898979778044926156769015805233396901479586]], ![![-5165625661505064007858918957785688766001345849868375375221927231919, 243683476341657589894585963571948447724004839200457869967659266003, -315296239266015674257989133605445597692350108453343905465303511902]], ![![-6059604681272931150190729913467317327879391291300080522866422954113, 285856086125787556942225927891884191242876533796501406261088358834, -369862373435598932476181927572110986788298990367774207822523106429]]]
  g := ![![![-254392318534617841404596175408981, 269951726819361077948872668065471, 90104625229317261681095291354056], ![-3359144363292654872143079292445675, 2110694423336956045211155061213816, 2429203392505658994445440806592542], ![1571625192501827449038167680502107, -2791432637765881576641888001992251, 401241586060063022931236967463631]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![2003911569547769155215925083493999, -1227793826272780584240759259326850, -966535709911287720572622548751404]] ![![1481410642206098041821140845722212, 269951726819361077948872668065471, 90104625229317261681095291354056]]
  ![![89, 0, 0]] where
 M := ![![![57033151773489660722421874677153272546697929626976128521534486870010, 647481132683799870035076405772652994394768679207563467905221219333, -3189813548341041691804895695699329522163814378144950600312720230680]]]
 hmul := by decide  
 g := ![![![![640821930039209671038448030080373848839302580078383466534095358090, 7275068906559549101517712424411831397694030103455769302305856397, -35840601666753277436010063996621680024312521102752253936097980120]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [52, 75, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 89, 41], [75, 7, 56], [0, 1]]
 g := ![![[45, 63, 70], [66, 81], [81, 73], [16, 22], [37, 89], [1]], ![[39, 9, 54, 76], [61, 85], [6, 72], [68, 32], [47, 31], [96, 81, 20, 51]], ![[87, 10, 66, 45], [37, 35], [70, 35], [20, 64], [45, 73], [79, 18, 78, 46]]]
 h' := ![![[85, 89, 41], [12, 26, 19], [7, 5, 88], [57, 56, 48], [4, 9, 64], [45, 22, 63], [0, 1]], ![[75, 7, 56], [72, 14, 35], [72, 8, 45], [44, 72, 13], [31, 7, 41], [70, 70, 82], [85, 89, 41]], ![[0, 1], [43, 57, 43], [30, 84, 61], [88, 66, 36], [35, 81, 89], [85, 5, 49], [75, 7, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 34], []]
 b := ![[], [48, 77, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [52, 75, 34, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-654795925329, -22351172135, 9130359158]
  a := ![-65, -259, -586]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6750473457, -230424455, 94127414]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8878255547641553798258725959554663337125332005062, 418823259265857257511945523048510204200982383749, -541905428082920745940532917562983960590046927806]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-8878255547641553798258725959554663337125332005062, 418823259265857257511945523048510204200982383749, -541905428082920745940532917562983960590046927806]] 
 ![![101, 0, 0], ![0, 101, 0], ![69, 88, 1]] where
  M :=![![![-8878255547641553798258725959554663337125332005062, 418823259265857257511945523048510204200982383749, -541905428082920745940532917562983960590046927806], ![95252273173776987797105206096570703307459194749799, -4493435370163521038508279279545702717371167831036, 5813948876907334812941053983174053923779964620908], ![-139406532597641351069335482476173328927157642348407, 6576370552997445647488799065765192348435838926151, -8509009041190363332972963776011242067958138372891]]]
  hmulB := by decide  
  f := ![![![2727338522942693068036832, 59764328740095467741647, -132858337836076897689476]], ![![23309973450053552563399947, 3630687527083459427450800, 996218300909185370484898]], ![![21908876702398419395057747, 3222288641862255147665024, 806402036827224198217599]]]
  g := ![![![282309098911682947243941043091992375679088178352, 476301989411513692081968735332585136001238732977, -541905428082920745940532917562983960590046927806], ![-3028813854780486280156708106360782350825330337553, -5110108282554544401755653760384776712970376776940, 5813948876907334812941053983174053923779964620908], ![4432822685589046721839594238302993799623305993872, 7478902635423261573753560508462915785433188274659, -8509009041190363332972963776011242067958138372891]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [50, 84, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 100], [0, 1]]
 g := ![![[34, 65], [25], [4, 37], [13], [56], [17, 1]], ![[28, 36], [25], [27, 64], [13], [56], [34, 100]]]
 h' := ![![[17, 100], [67, 41], [2, 5], [26, 21], [75, 66], [59, 37], [0, 1]], ![[0, 1], [57, 60], [87, 96], [80, 80], [86, 35], [82, 64], [17, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [7, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [50, 84, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2287, -8890, -3395]
  a := ![-2, -7, -21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2342, 2870, -3395]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2727338522942693068036832, 59764328740095467741647, -132858337836076897689476]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![2727338522942693068036832, 59764328740095467741647, -132858337836076897689476]] 
 ![![101, 0, 0], ![32, 1, 0], ![97, 0, 1]] where
  M :=![![![2727338522942693068036832, 59764328740095467741647, -132858337836076897689476], ![23309973450053552563399947, 3630687527083459427450800, 996218300909185370484898], ![-26667474745518088372904297, 1826911761676753024323381, 2946620550230637357880319]]]
  hmulB := by decide  
  f := ![![![-8878255547641553798258725959554663337125332005062, 418823259265857257511945523048510204200982383749, -541905428082920745940532917562983960590046927806]], ![![-1869820835155967660863109154546322014658925043685, 88207019072711992097762153049570532842180875732, -114128958631149792645108904741004285298035020484]], ![![-9906904165533386826736949510425501709191236107321, 467348779225599996298490245559115664910209209404, -604691441239937383061432245342779071734581092773]]]
  g := ![![![135664740330288090853300, 59764328740095467741647, -132858337836076897689476], ![-1876289134701070594574859, 3630687527083459427450800, 996218300909185370484898], ![-3672780638530158503620232, 1826911761676753024323381, 2946620550230637357880319]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-8878255547641553798258725959554663337125332005062, 418823259265857257511945523048510204200982383749, -541905428082920745940532917562983960590046927806]] ![![2727338522942693068036832, 59764328740095467741647, -132858337836076897689476]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-187476400627698396093337947195354729472883160833, 8844020846773485475327291971640388576272775578, -11443067682883481596689750818585936991033309450]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-187476400627698396093337947195354729472883160833, 8844020846773485475327291971640388576272775578, -11443067682883481596689750818585936991033309450]] 
 ![![103, 0, 0], ![59, 1, 0], ![61, 0, 1]] where
  M :=![![![-187476400627698396093337947195354729472883160833, 8844020846773485475327291971640388576272775578, -11443067682883481596689750818585936991033309450], ![2011380865351382764896033685224179362007101929328, -94884978826187046208580025215863490212625511271, 122769411516385299543342172172161696735827684130], ![-2943757905497144712978425694904552313753799479050, 138868978692268278170399553239173048975169073310, -179679260119368407729250570654518084228601559217]]]
  hmulB := by decide  
  f := ![![![-4090737472650966913864507, -125594558023740152622926, 174708064655670443633810]], ![![-2641291424846340929189763, -125016844188591735410465, 82793262528933430264700]], ![![-2002345187277307387508719, -95423536736118210145872, 62321494674263488104517]]]
  g := ![![![-109189339140210308151197801829082514756747995, 8844020846773485475327291971640388576272775578, -11443067682883481596689750818585936991033309450], ![1171461297057429311246433693769531880257459829, -94884978826187046208580025215863490212625511271, 122769411516385299543342172172161696735827684130], ![-1714493019995148092696257534855913255767764001, 138868978692268278170399553239173048975169073310, -179679260119368407729250570654518084228601559217]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9633188788955, -1010632077926, -77034345218]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-9633188788955, -1010632077926, -77034345218]] 
 ![![103, 0, 0], ![72, 1, 0], ![40, 0, 1]] where
  M :=![![![-9633188788955, -1010632077926, -77034345218], ![12470378335224, -13290545374569, -9875217743606], ![167462423520454, 6285709913118, -6370189519523]]]
  hmulB := by decide  
  f := ![![![146736046919007330433234095, -6922133418285293833119022, 8956383367672195416280114]], ![![87288409275802022325346756, -4117747667078019203545749, 5327855516374063547496482]], ![![79354310638992499795255986, -3743464111871266124462598, 4843578949298392644028693]]]
  g := ![![![642851404179, -1010632077926, -77034345218], ![13246585971344, -13290545374569, -9875217743606], ![-294185528574, 6285709913118, -6370189519523]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-145826840329, 8910802416, 15375621932]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![-145826840329, 8910802416, 15375621932]] 
 ![![103, 0, 0], ![74, 1, 0], ![10, 0, 1]] where
  M :=![![![-145826840329, 8910802416, 15375621932], ![-2681823035684, -187061740325, 42981158364], ![316435452904, -290563962992, -218686113373]]]
  hmulB := by decide  
  f := ![![![53396580660694223131313, -2518932894638853231376, 3259187206971568615324]], ![![32800682279385525735962, -1547340982097030796045, 2002067599500901353148]], ![![13324270897274494348286, -628559803735333631088, 813278541683609350803]]]
  g := ![![![-9310509111, 8910802416, 15375621932], ![104183826842, -187061740325, 42981158364], ![233058542214, -290563962992, -218686113373]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-187476400627698396093337947195354729472883160833, 8844020846773485475327291971640388576272775578, -11443067682883481596689750818585936991033309450]] ![![-9633188788955, -1010632077926, -77034345218]]
  ![![-53396580660694223131313, 2518932894638853231376, -3259187206971568615324]] where
 M := ![![![-53396580660694223131313, 2518932894638853231376, -3259187206971568615324]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![-53396580660694223131313, 2518932894638853231376, -3259187206971568615324]] ![![-145826840329, 8910802416, 15375621932]]
  ![![103, 0, 0]] where
 M := ![![![-103, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [74, 13, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 12, 92], [12, 94, 15], [0, 1]]
 g := ![![[31, 44, 37], [86, 102, 105], [102, 1], [65, 8, 9], [86, 48], [1]], ![[74, 75, 38, 9], [106, 100], [37, 41], [87, 67, 96, 64], [67, 64], [57, 47, 72, 49]], ![[70, 77, 27, 63], [43, 60, 54, 77], [39, 101], [62, 17, 11, 70], [76, 87], [30, 8, 2, 58]]]
 h' := ![![[60, 12, 92], [56, 20, 95], [74, 34, 76], [5, 15, 1], [75, 36, 3], [33, 94, 72], [0, 1]], ![[12, 94, 15], [21, 93, 70], [56, 55], [36, 5, 83], [56, 14, 63], [29, 84, 8], [60, 12, 92]], ![[0, 1], [90, 101, 49], [39, 18, 31], [6, 87, 23], [77, 57, 41], [43, 36, 27], [12, 94, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 79], []]
 b := ![[], [63, 36, 98], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [74, 13, 35, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3537955, -162105, 66340]
  a := ![-1, -5, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33065, -1515, 620]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [71, 47, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 82, 34], [6, 26, 75], [0, 1]]
 g := ![![[34, 31, 35], [21, 81], [107, 80, 4], [107, 20, 26], [49, 100], [1]], ![[104, 71, 22, 31], [81, 60], [25, 70, 27, 7], [90, 35, 74, 97], [60, 25], [43, 76, 9, 64]], ![[39, 55, 62, 43], [10, 16], [27, 24, 15, 16], [52, 91, 92, 80], [90, 7], [26, 98, 11, 45]]]
 h' := ![![[93, 82, 34], [34, 25, 97], [33, 81, 100], [33, 79, 107], [36, 105, 74], [38, 62, 99], [0, 1]], ![[6, 26, 75], [48, 54, 102], [83, 22, 13], [37, 5, 18], [54, 27, 44], [45, 78, 104], [93, 82, 34]], ![[0, 1], [25, 30, 19], [100, 6, 105], [99, 25, 93], [66, 86, 100], [5, 78, 15], [6, 26, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 34], []]
 b := ![[], [101, 44, 108], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [71, 47, 10, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16663266, -5241701, -4642528]
  a := ![2, 27, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![152874, -48089, -42592]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [13, 66, 85, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [111, 99, 1], [30, 13, 112], [0, 1]]
 g := ![![[61, 0, 62], [7, 15], [37, 56], [84, 50], [91, 63, 106], [1]], ![[30, 51, 47, 62], [23, 22], [75, 69], [16, 51], [63, 51, 6, 99], [112, 11, 99, 1]], ![[41, 51], [21, 14], [63, 50], [86, 85], [16, 110, 1, 57], [87, 70, 11, 112]]]
 h' := ![![[111, 99, 1], [31, 93, 66], [3, 12, 44], [22, 98, 100], [60, 11, 84], [100, 47, 28], [0, 1]], ![[30, 13, 112], [109, 67, 47], [42, 29, 19], [0, 103, 42], [35, 68, 86], [5, 94, 72], [111, 99, 1]], ![[0, 1], [50, 66], [60, 72, 50], [75, 25, 84], [17, 34, 56], [105, 85, 13], [30, 13, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97, 76], []]
 b := ![[], [65, 100, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [13, 66, 85, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19119035, -1534766, -458780]
  a := ![-2, -5, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-169195, -13582, -4060]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![78714881, 5326798, -1373402]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![78714881, 5326798, -1373402]] 
 ![![127, 0, 0], ![59, 1, 0], ![111, 0, 1]] where
  M :=![![![78714881, 5326798, -1373402], ![245672148, 106889083, 57388186], ![-1099744694, -4659558, 66854693]]]
  hmulB := by decide  
  f := ![![![7413440410198307, -349721998686698, 452496954778794]], ![![2817766103281295, -132925435283131, 171989051029492]], ![![7396046171536985, -348901442025596, 451435256081639]]]
  g := ![![![-654477, 5326798, -1373402], ![-97880885, 106889083, 57388186], ![-64926785, -4659558, 66854693]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-946937713, -167333550, -54027210]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-946937713, -167333550, -54027210]] 
 ![![127, 0, 0], ![72, 1, 0], ![126, 0, 1]] where
  M :=![![![-946937713, -167333550, -54027210], ![9287428200, -1346135863, -1511253870], ![22692051630, 1701103110, -282855433]]]
  hmulB := by decide  
  f := ![![![-2951560500662229379, 139237058696300250, -180155510059506270]], ![![-1423983501799768644, 67175067012237173, -86916217379078190]], ![![-3293244728996481972, 155355687111845910, -201011019008428357]]]
  g := ![![![141011861, -167333550, -54027210], ![2335647228, -1346135863, -1511253870], ![-505099116, 1701103110, -282855433]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-424620873398165334520270591329419, 20031085745912865619504516682036, -25917744193892018002776847055028]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![-424620873398165334520270591329419, 20031085745912865619504516682036, -25917744193892018002776847055028]] 
 ![![127, 0, 0], ![122, 1, 0], ![25, 0, 1]] where
  M :=![![![-424620873398165334520270591329419, 20031085745912865619504516682036, -25917744193892018002776847055028], ![4555636319677016016105452751311936, -214907809445053782028368289326135, 278064090040804710203375707985444], ![-6667404797189577679752065760069716, 314528478372707959946906969470268, -406960898054227877370453600210443]]]
  hmulB := by decide  
  f := ![![![-56231144525048813, -22678532711794444, -11914415280727204]], ![![-37778389690082590, -22473655037854431, -12949612169484108]], ![![8735479899126681, -2070393777513808, -1970966004454047]]]
  g := ![![![-17484013618521531417562208268993, 20031085745912865619504516682036, -25917744193892018002776847055028], ![187580998590184721799070798027278, -214907809445053782028368289326135, 278064090040804710203375707985444], ![-274534304781923242984357291576231, 314528478372707959946906969470268, -406960898054227877370453600210443]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![78714881, 5326798, -1373402]] ![![-946937713, -167333550, -54027210]]
  ![![-56231144525048813, -22678532711794444, -11914415280727204]] where
 M := ![![![-56231144525048813, -22678532711794444, -11914415280727204]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![-56231144525048813, -22678532711794444, -11914415280727204]] ![![-424620873398165334520270591329419, 20031085745912865619504516682036, -25917744193892018002776847055028]]
  ![![127, 0, 0]] where
 M := ![![![127, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-94205982288, 4444077593, -5750086026]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-94205982288, 4444077593, -5750086026]] 
 ![![131, 0, 0], ![56, 1, 0], ![44, 0, 1]] where
  M :=![![![-94205982288, 4444077593, -5750086026], ![1010709132143, -47679241786, 61691034008], ![-1479224073947, 69780988451, -90287956989]]]
  hmulB := by decide  
  f := ![![![-3300746, -161751, 99692]], ![![-1545417, -103086, 27986]], ![![-799725, -60331, 9709]]]
  g := ![![![-687561392, 4444077593, -5750086026], ![7376650197, -47679241786, 61691034008], ![-10796101677, 69780988451, -90287956989]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4604864648994857860279832383, -217230109047996445165146952, 281068858120484356984516406]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![4604864648994857860279832383, -217230109047996445165146952, 281068858120484356984516406]] 
 ![![131, 0, 0], ![94, 1, 0], ![9, 0, 1]] where
  M :=![![![4604864648994857860279832383, -217230109047996445165146952, 281068858120484356984516406], ![-49404280280132758917455518002, 2330599922200450294696662545, -3015507664841417522605018738], ![72305669774098469456011718132, -3410951184687767485926527736, 4413348401777394124821724021]]]
  hmulB := by decide  
  f := ![![![571338200776277, -18072252702824, -48734514626694]], ![![474933272365944, -7298244205855, -35233308076774]], ![![18008223248275, 5400482619968, 2543113520035]]]
  g := ![![![171716604400169194602618307, -217230109047996445165146952, 281068858120484356984516406], ![-1842298503690094113858752890, 2330599922200450294696662545, -3015507664841417522605018738], ![2696297294036275313051219917, -3410951184687767485926527736, 4413348401777394124821724021]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27021820317173983104, -200452539799829481, -1857876968830770614]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![27021820317173983104, -200452539799829481, -1857876968830770614]] 
 ![![131, 0, 0], ![111, 1, 0], ![86, 0, 1]] where
  M :=![![![27021820317173983104, -200452539799829481, -1857876968830770614], ![324928017005585027969, 35509395002128518250, 3569105508494017032], ![-191581795732383855733, 30728294200291477229, 33196808843065783389]]]
  hmulB := by decide  
  f := ![![![1069126073921690859525935274446467184922, -50435005440335703058249760540621057497, 65256650887577859334462851431152985108]], ![![818340803775123849777019593149354687595, -38604448901945070907214514846417704983, 49949375888969860897248017932506197074]], ![![830017402424493593841439767722179596553, -39155281334873570206638444478540102435, 50662084839020307583672528434000214667]]]
  g := ![![![1595797492781689529, -200452539799829481, -1857876968830770614], ![-29950823679092869943, 35509395002128518250, 3569105508494017032], ![-49292732919606070226, 30728294200291477229, 33196808843065783389]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-94205982288, 4444077593, -5750086026]] ![![4604864648994857860279832383, -217230109047996445165146952, 281068858120484356984516406]]
  ![![-1069126073921690859525935274446467184922, 50435005440335703058249760540621057497, -65256650887577859334462851431152985108]] where
 M := ![![![-1069126073921690859525935274446467184922, 50435005440335703058249760540621057497, -65256650887577859334462851431152985108]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![-1069126073921690859525935274446467184922, 50435005440335703058249760540621057497, -65256650887577859334462851431152985108]] ![![27021820317173983104, -200452539799829481, -1857876968830770614]]
  ![![131, 0, 0]] where
 M := ![![![-131, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4315253138077031646949890377119824974170622561, -203567961537978577094024540482977138480111932, 263391731239026586574458191145246845089801978]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![4315253138077031646949890377119824974170622561, -203567961537978577094024540482977138480111932, 263391731239026586574458191145246845089801978]] 
 ![![137, 0, 0], ![7, 1, 0], ![102, 0, 1]] where
  M :=![![![4315253138077031646949890377119824974170622561, -203567961537978577094024540482977138480111932, 263391731239026586574458191145246845089801978], ![-46297120928367631227624207990901175029195458082, 2184022635729984405701501259461682194801164943, -2825854809096865530663619978265511920070525254], ![67758184480307494553538193904241114334975429416, -3196427892134532499721208355909063829036271988, 4135781828973887618508589425133015854341552423]]]
  hmulB := by decide  
  f := ![![![-669397242790405662478063, -3642242530222582581028, 40142651851744367073474]], ![![-85506474570206762465587, -6643614378697634352093, 906191110253661623968]], ![![-457983378072405933124954, -7267006971237229076900, 24201839548342733033131]]]
  g := ![![![-154202392098816278423260389316164330333053983, -203567961537978577094024540482977138480111932, 263391731239026586574458191145246845089801978], ![1654393512039436219417186284495980039813065425, 2184022635729984405701501259461682194801164943, -2825854809096865530663619978265511920070525254], ![-2421288808978739525812331890277102598573788422, -3196427892134532499721208355909063829036271988, 4135781828973887618508589425133015854341552423]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![969714, 253925, 111742]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![969714, 253925, 111742]] 
 ![![137, 0, 0], ![30, 1, 0], ![131, 0, 1]] where
  M :=![![![969714, 253925, 111742], ![-19300925, 1426704, 2204024], ![-30804351, -3057497, -127287]]]
  hmulB := by decide  
  f := ![![![-6557195895880, 309329478299, -400234035832]], ![![-922376577573, 43512237558, -56299446602]], ![![-7021561119957, 331235465978, -428577670929]]]
  g := ![![![-155374, 253925, 111742], ![-2560797, 1426704, 2204024], ![566388, -3057497, -127287]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18343839818403506, 17923112134946789, 11078073938089822]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![18343839818403506, 17923112134946789, 11078073938089822]] 
 ![![137, 0, 0], ![99, 1, 0], ![49, 0, 1]] where
  M :=![![![18343839818403506, 17923112134946789, 11078073938089822], ![-1920739827030772061, 34645918667741552, 145996899535198424], ![-1785019603168729791, -266864743684171097, -68659718400706327]]]
  hmulB := by decide  
  f := ![![![-36582646153683496316266741173551624, 1725751529952907348066611441640731, -2232908753069634757568662138976792]], ![![-23570782378814066754655656134445485, 1111929235013241856368157284746917, -1438698722592378563838871904564706]], ![![-17277160928078434641110248910557125, 815033630416365543328682464641028, -1054552579450696475975365210886177]]]
  g := ![![![-16780072149691459, 17923112134946789, 11078073938089822], ![-91273969725269405, 34645918667741552, 145996899535198424], ![204371651264224955, -266864743684171097, -68659718400706327]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![4315253138077031646949890377119824974170622561, -203567961537978577094024540482977138480111932, 263391731239026586574458191145246845089801978]] ![![969714, 253925, 111742]]
  ![![-36582646153683496316266741173551624, 1725751529952907348066611441640731, -2232908753069634757568662138976792]] where
 M := ![![![-36582646153683496316266741173551624, 1725751529952907348066611441640731, -2232908753069634757568662138976792]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![-36582646153683496316266741173551624, 1725751529952907348066611441640731, -2232908753069634757568662138976792]] ![![18343839818403506, 17923112134946789, 11078073938089822]]
  ![![137, 0, 0]] where
 M := ![![![137, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)


lemma PB259I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB259I2 : PrimesBelowBoundCertificateInterval O 79 137 259 where
  m := 11
  g := ![1, 2, 1, 2, 3, 1, 1, 1, 3, 3, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB259I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N0, I137N1, I137N2]
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
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![1225043]
    · exact ![1295029]
    · exact ![1442897]
    · exact ![127, 127, 127]
    · exact ![131, 131, 131]
    · exact ![137, 137, 137]
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
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
  β := ![I89N1, I101N1, I103N0, I103N1, I103N2, I127N0, I127N1, I127N2, I131N0, I131N1, I131N2, I137N0, I137N1, I137N2]
  Il := ![[], [I89N1], [], [I101N1], [I103N0, I103N1, I103N2], [], [], [], [I127N0, I127N1, I127N2], [I131N0, I131N1, I131N2], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
