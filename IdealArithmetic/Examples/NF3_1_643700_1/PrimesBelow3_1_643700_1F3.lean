
import IdealArithmetic.Examples.NF3_1_643700_1.RI3_1_643700_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [124, 37, 134, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [136, 20, 67], [8, 118, 72], [0, 1]]
 g := ![![[111, 87, 24], [77, 104, 106], [117, 117], [42, 45, 13], [74, 5], [5, 1], []], ![[78, 93, 108, 54], [8, 48, 137, 54], [45, 67], [77, 135, 117, 137], [56, 46], [25, 24], [105, 41]], ![[128, 9, 15, 90], [54, 111, 45, 14], [16, 54], [52, 42, 126, 115], [93, 66], [129, 122], [100, 41]]]
 h' := ![![[136, 20, 67], [43, 110, 118], [3, 77, 55], [74, 32, 123], [63, 54, 41], [75, 108, 127], [0, 0, 1], [0, 1]], ![[8, 118, 72], [87, 137, 27], [17, 99, 112], [71, 114, 117], [71, 117, 116], [64, 28, 121], [55, 85, 118], [136, 20, 67]], ![[0, 1], [49, 31, 133], [42, 102, 111], [48, 132, 38], [123, 107, 121], [102, 3, 30], [35, 54, 20], [8, 118, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81, 111], []]
 b := ![[], [58, 70, 100], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [124, 37, 134, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4641071, 764361, -77562]
  a := ![-5, 3, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33389, 5499, -558]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51856419779199854284630964, 1821045275735469660270315, 2901665000311392865858446]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-51856419779199854284630964, 1821045275735469660270315, 2901665000311392865858446]] 
 ![![149, 0, 0], ![2, 1, 0], ![75, 0, 1]] where
  M :=![![![-51856419779199854284630964, 1821045275735469660270315, 2901665000311392865858446], ![-525541559229778485471284673, -366875324754329153861120, 19631266655346996559197228], ![-748189380504120127647225423, -26335104767565326637891381, 14541681054545804879207347]]]
  hmulB := by decide  
  f := ![![![-511656480129214545297570218053625620593425898643228, 102896711369210627736290249615928141892902823458231, -36813974688740415450277813826059673338726141706340]], ![![40418352630125495436339397603419150372340540975493, -8128335565203237844649991145964828282075319403112, 2908123454842695900445318312518593856803934444414]], ![![-348590173219911116534692313131612337070270609577797, 70103250585029179407161862780164419315745734100046, -25081261182152097619566238902735368023036423034075]]]
  g := ![![![-1833042854725001735198356, 1821045275735469660270315, 2901665000311392865858446], ![-13403710119001976973848017, -366875324754329153861120, 19631266655346996559197228], ![-11987552013824998928268414, -26335104767565326637891381, 14541681054545804879207347]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![50, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![50, 1, 0]] 
 ![![149, 0, 0], ![50, 1, 0], ![122, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![50, 1, 0], ![3, 48, 6], ![-183, 19, 53]]]
  hmulB := by decide  
  f := ![![![814, 15405, 1926], ![447, -47829, 0]], ![![271, 5135, 642], ![150, -15943, 0]], ![![642, 12613, 1577], ![439, -39162, 0]]]
  g := ![![![1, 0, 0], ![-50, 149, 0], ![-122, 0, 149]], ![![0, 1, 0], ![-21, 48, 6], ![-51, 19, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-53, 1, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-53, 1, 0]] 
 ![![149, 0, 0], ![96, 1, 0], ![61, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-53, 1, 0], ![3, -55, 6], ![-183, 19, -50]]]
  hmulB := by decide  
  f := ![![![25189, -543316, 59280], ![-12516, -1472120, 0]], ![![16234, -350021, 38190], ![-8045, -948385, 0]], ![![10345, -222432, 24269], ![-5032, -602680, 0]]]
  g := ![![![1, 0, 0], ![-96, 149, 0], ![-61, 0, 149]], ![![-1, 1, 0], ![33, -55, 6], ![7, 19, -50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-51856419779199854284630964, 1821045275735469660270315, 2901665000311392865858446]] ![![149, 0, 0], ![50, 1, 0]]
  ![![149, 0, 0], ![42, 58, 1]] where
 M := ![![![-7726606547100778288410013636, 271335746084584979380276935, 432348085046397537012908454], ![-3118362548189771199702832873, 90685388462019153859654630, 164714516670916639852119528]]]
 hmul := by decide  
 g := ![![![![-48676149443714897813159894, 6212847167595647644682745, 2977385722584844210417281], ![-11282387618744250339266415, 0, 0]], ![![-19633729565075462873425889, 2396791819915209954094482, 1136296986764465660810386], ![-4593734356988743608627986, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![42, 58, 1]] ![![149, 0, 0], ![-53, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-7897, 149, 0]], ![![6258, 8642, 149], ![-2235, -3129, 298]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-53, 1, 0]]], ![![![42, 58, 1]], ![![-15, -21, 2]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24241415134615490521182100325704, 3006687675740172022296340327315, 647278393344506163737174213286]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![24241415134615490521182100325704, 3006687675740172022296340327315, 647278393344506163737174213286]] 
 ![![151, 0, 0], ![0, 151, 0], ![135, 70, 1]] where
  M :=![![![24241415134615490521182100325704, 3006687675740172022296340327315, 647278393344506163737174213286], ![-109431882954824111897013860049393, 30526329256680763587595729723508, 19981961234474550624989564603748], ![-642784654908715861494646192398543, 43534219578828638985149807739979, 46854324422070636026551779786655]]]
  hmulB := by decide  
  f := ![![![-3711201631855695391946937612403099139486846155635149561757248, 746341457552850292305815139240307825006304367357834242343181, -267023067714190644817873792523806166222465578441363737719532]], ![![51104245764355438878588349449577451893730113956843066729703899, -10277322833531018228098169948836031947726300880736729063114718, 3676979542174529819381269457870428451370429468822914240900490]], ![![19721117848710725180830064010900206612742004135489409459517453, -3966016751404200843778814671076257627809261006166860414603114, 1418945643242425180464046743195589761594420526670129847311653]]]
  g := ![![![-418153430244323454194280917006, -280150992439571254564939434455, 647278393344506163737174213286], ![-18589381785489327458745729016923, -9060999716268462120275985381052, 19981961234474550624989564603748], ![-46146479813829481623040638831768, -21432241655404740946181952167721, 46854324422070636026551779786655]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [31, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 150], [0, 1]]
 g := ![![[130, 39], [102, 91], [95, 29], [69], [124, 20], [95], [1]], ![[0, 112], [0, 60], [99, 122], [69], [7, 131], [95], [1]]]
 h' := ![![[47, 150], [9, 48], [75, 98], [55, 123], [82, 62], [130, 41], [120, 47], [0, 1]], ![[0, 1], [0, 103], [0, 53], [98, 28], [127, 89], [94, 110], [64, 104], [47, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [14, 99]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [31, 104, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1058, -2175, 1727]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1537, -815, 1727]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15567854957959341293517270, -275550485653394465351267, 444058350750084507027772]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-15567854957959341293517270, -275550485653394465351267, 444058350750084507027772]] 
 ![![151, 0, 0], ![30, 1, 0], ![87, 0, 1]] where
  M :=![![![-15567854957959341293517270, -275550485653394465351267, 444058350750084507027772], ![-82089329644225648182136077, -6579645322400946729287068, -321127861670113271024286], ![-13074605282690897345689535, -14560684593166269489257285, -7069281049167750041987859]]]
  hmulB := by decide  
  f := ![![![41837520480037796352591253682932010760071244283902, -8413737412552090312074259645777863773438532586373, 3010233388625908250436829927956370986171114322858]], ![![4496766172483022581533608971752389675579521918377, -904322468129327653160187071309120040787791364240, 323544883108228015840859799654920926510036934676]], ![![31451091746270304172003721231090549375119075283689, -6324973952924938055225463251255214243007138112156, 2262923935191917989824808655396599244677059558897]]]
  g := ![![![-304201436447780526121824, -275550485653394465351267, 444058350750084507027772], ![948597046311937803149595, -6579645322400946729287068, -321127861670113271024286], ![6879293932383387026390548, -14560684593166269489257285, -7069281049167750041987859]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![24241415134615490521182100325704, 3006687675740172022296340327315, 647278393344506163737174213286]] ![![-15567854957959341293517270, -275550485653394465351267, 444058350750084507027772]]
  ![![151, 0, 0]] where
 M := ![![![-632666720043433750248898060854707269361812668871627113345, -35887488744334009793808059805216152938350227189505017898, 5223278760899102050317400923876975803249628913730784724]]]
 hmul := by decide  
 g := ![![![![-4189845828102210266548993780494750128223924959414749095, -237665488373072912541775230498120218134769716486788198, 34591250072179483776936429959450170882447873600866124]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1612182561, 324218084, -115997452]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-1612182561, 324218084, -115997452]] 
 ![![157, 0, 0], ![85, 1, 0], ![133, 0, 1]] where
  M :=![![![-1612182561, 324218084, -115997452], ![22200187968, -4464570317, 1597316148], ![-42744273736, 8596090088, -3075474801]]]
  hmulB := by decide  
  f := ![![![-940893, -45508, 11852]], ![![-524085, -28617, 4904]], ![![-754813, -45644, 4763]]]
  g := ![![![-87535405, 324218084, -115997452], ![1205386097, -4464570317, 1597316148], ![-2320852119, 8596090088, -3075474801]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-43, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-43, 1, 0]] 
 ![![157, 0, 0], ![114, 1, 0], ![149, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-43, 1, 0], ![3, -45, 6], ![-183, 19, -40]]]
  hmulB := by decide  
  f := ![![![4389, -72260, 9636], ![-1570, -252142, 0]], ![![3198, -52463, 6996], ![-1098, -183062, 0]], ![![4167, -68578, 9145], ![-1484, -239294, 0]]]
  g := ![![![1, 0, 0], ![-114, 157, 0], ![-149, 0, 157]], ![![-1, 1, 0], ![27, -45, 6], ![23, 19, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-1612182561, 324218084, -115997452]] ![![157, 0, 0], ![-43, 1, 0]]
  ![![157, 0, 0], ![-33, 59, 1]] where
 M := ![![![-253112662077, 50902239188, -18211599964], ![91524038091, -18405947929, 6585206584]]]
 hmul := by decide  
 g := ![![![![-1530625668, 178404245, -118468873], ![388013097, 0, 0]], ![![553465206, -64509986, 42837641], ![-140303053, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-33, 59, 1]] ![![157, 0, 0], ![-43, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-6751, 157, 0]], ![![-5181, 9263, 157], ![1413, -2669, 314]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-43, 1, 0]]], ![![![-33, 59, 1]], ![![9, -17, 2]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![42482933745156835012614, -1866750430466025441073, -2571863919099846428098]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![42482933745156835012614, -1866750430466025441073, -2571863919099846428098]] 
 ![![163, 0, 0], ![74, 1, 0], ![9, 0, 1]] where
  M :=![![![42482933745156835012614, -1866750430466025441073, -2571863919099846428098], ![465050845903873820018715, -2648979856808196239102, -18916094340095691930732], ![709391869206560694934373, 18540884122242291609671, -17126459847338016300663]]]
  hmulB := by decide  
  f := ![![![-396088760359150274266668664636246589582433798, 79655457194583518509158478998916102540267157, -28498811535962302773439284253503935404667440]], ![![-146357787631363609402862679311007847499540847, 29433292874034228869309174370976306875019142, -10530526043568074861962417260897585343053926]], ![![-86297039633119797907817190124397566308241411, 17354772047261023782200382707320451009972372, -6209121072725575472039090522973106405531629]]]
  g := ![![![1250118042156695309846, -1866750430466025441073, -2571863919099846428098], ![5100123953181236620177, -2648979856808196239102, -18916094340095691930732], ![-3119603786584826610278, 18540884122242291609671, -17126459847338016300663]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N0)

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := prime_ideal_of_norm_prime hp163.out _ NI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-57, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-57, 1, 0]] 
 ![![163, 0, 0], ![106, 1, 0], ![92, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-57, 1, 0], ![3, -59, 6], ![-183, 19, -54]]]
  hmulB := by decide  
  f := ![![![-5087, 117984, -12000], ![2608, 326000, 0]], ![![-3272, 76689, -7800], ![1794, 211900, 0]], ![![-2860, 66592, -6773], ![1504, 184000, 0]]]
  g := ![![![1, 0, 0], ![-106, 163, 0], ![-92, 0, 163]], ![![-1, 1, 0], ![35, -59, 6], ![17, 19, -54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-18, 1, 0]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-18, 1, 0]] 
 ![![163, 0, 0], ![145, 1, 0], ![22, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-18, 1, 0], ![3, -20, 6], ![-183, 19, -15]]]
  hmulB := by decide  
  f := ![![![-2942, 19977, -5994], ![489, 162837, 0]], ![![-2609, 17757, -5328], ![490, 144744, 0]], ![![-392, 2696, -809], ![112, 21978, 0]]]
  g := ![![![1, 0, 0], ![-145, 163, 0], ![-22, 0, 163]], ![![-1, 1, 0], ![17, -20, 6], ![-16, 19, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![42482933745156835012614, -1866750430466025441073, -2571863919099846428098]] ![![163, 0, 0], ![-57, 1, 0]]
  ![![163, 0, 0], ![31, -79, 1]] where
 M := ![![![6924718200460564107056082, -304280320165962146894899, -419213818813274967779974], ![-1956476377570065775700283, 103755794679755253902059, 127680149048595554470854]]]
 hmul := by decide  
 g := ![![![![41141051613455575995872, 1552884679353312053205, -2615150439477306396380], ![7055702821525974829966, 0, 0]], ![![-11615933075554151660839, -349660395616855822825, 795797329657866860000], ![-2034815685636743709146, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![31, -79, 1]] ![![163, 0, 0], ![-18, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-2934, 163, 0]], ![![5053, -12877, 163], ![-978, 1630, -489]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-18, 1, 0]]], ![![![31, -79, 1]], ![![-6, 10, -3]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3736242268271, 265580334804, 278854614666]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-3736242268271, 265580334804, 278854614666]] 
 ![![167, 0, 0], ![17, 1, 0], ![125, 0, 1]] where
  M :=![![![-3736242268271, 265580334804, 278854614666], ![-50233653479466, 1030834740775, 2430045852822], ![-88477411166370, -809920546710, 2916445644127]]]
  hmulB := by decide  
  f := ![![![-4974517555195996382494045, 1000400692567809200344968, -357919366758399845010738]], ![![-96205702058930175235921, 19347454280907452499859, -6922054968629591006856]], ![![-4513206896365014692445205, 907628781028089350867670, -324727802540233210497167]]]
  g := ![![![-258131346067, 265580334804, 278854614666], ![-2224632189673, 1030834740775, 2430045852822], ![-2630326152025, -809920546710, 2916445644127]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-178347106186564024383493023, 35866506966115943925968740, -12832175703714655199019818]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-178347106186564024383493023, 35866506966115943925968740, -12832175703714655199019818]] 
 ![![167, 0, 0], ![21, 1, 0], ![101, 0, 1]] where
  M :=![![![-178347106186564024383493023, 35866506966115943925968740, -12832175703714655199019818], ![2455887674678129733198532914, -493891458489374361016807045, 176702514685551697958752986], ![-4728569649168022044992445446, 950939322134210693772822238, -340223275066223951785002981]]]
  hmulB := by decide  
  f := ![![![364295902901523, 12660940298744, -7164380639830]], ![![53887894843815, 2806769679167, -574727506368]], ![![212583476346583, 9998591792130, -2825004277015]]]
  g := ![![![2182670620360367235162665, 35866506966115943925968740, -12832175703714655199019818], ![-30055962157399581911871681, -493891458489374361016807045, 176702514685551697958752986], ![57869792620971092910560411, 950939322134210693772822238, -340223275066223951785002981]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, -4, -4]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![51, -4, -4]] 
 ![![167, 0, 0], ![128, 1, 0], ![68, 0, 1]] where
  M :=![![![51, -4, -4], ![720, -17, -36], ![1304, 8, -45]]]
  hmulB := by decide  
  f := ![![![1053, -212, 76]], ![![720, -145, 52]], ![![596, -120, 43]]]
  g := ![![![5, -4, -4], ![32, -17, -36], ![20, 8, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-3736242268271, 265580334804, 278854614666]] ![![-178347106186564024383493023, 35866506966115943925968740, -12832175703714655199019818]]
  ![![1053, -212, 76]] where
 M := ![![![1053, -212, 76]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![1053, -212, 76]] ![![51, -4, -4]]
  ![![167, 0, 0]] where
 M := ![![![167, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![37, 1, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![37, 1, 0]] 
 ![![173, 0, 0], ![37, 1, 0], ![73, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![37, 1, 0], ![3, 35, 6], ![-183, 19, 40]]]
  hmulB := by decide  
  f := ![![![4035, 50078, 8586], ![1211, -247563, 0]], ![![844, 10708, 1836], ![347, -52938, 0]], ![![1696, 21131, 3623], ![542, -104463, 0]]]
  g := ![![![1, 0, 0], ![-37, 173, 0], ![-73, 0, 173]], ![![0, 1, 0], ![-10, 35, 6], ![-22, 19, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N0 : Nat.card (O ⧸ I173N0) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N0)

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := prime_ideal_of_norm_prime hp173.out _ NI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-36, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-36, 1, 0]] 
 ![![173, 0, 0], ![137, 1, 0], ![32, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-36, 1, 0], ![3, -38, 6], ![-183, 19, -33]]]
  hmulB := by decide  
  f := ![![![-10979, 147725, -23328], ![3287, 672624, 0]], ![![-8693, 116949, -18468], ![2596, 532494, 0]], ![![-2036, 27325, -4315], ![583, 124416, 0]]]
  g := ![![![1, 0, 0], ![-137, 173, 0], ![-32, 0, 173]], ![![-1, 1, 0], ![29, -38, 6], ![-10, 19, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7573800141888397836, 172264613044566653, -196190997915207136]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![7573800141888397836, 172264613044566653, -196190997915207136]] 
 ![![173, 0, 0], ![171, 1, 0], ![28, 0, 1]] where
  M :=![![![7573800141888397836, 172264613044566653, -196190997915207136], ![36419746457616605847, 3501641955410328946, 445014684521778510], ![-3469111485281077051, 7393038604066116263, 3970583024802747939]]]
  hmulB := by decide  
  f := ![![![10613549365043540418976680187518634164, -2134438569686351661643129498547130935, 763650912002003765444079225284585686]], ![![9646043403566587673894892632040265137, -1939868217248045195695229478534909629, 694038307920407775823185018544711698]], ![![3344390520563785822852811643173126963, -672573883972835879604351157009777187, 240630799676778438964203316363132601]]]
  g := ![![![-94740466746281503, 172264613044566653, -196190997915207136], ![-3322667277943118163, 3501641955410328946, 445014684521778510], ![-7970260332225802892, 7393038604066116263, 3970583024802747939]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![37, 1, 0]] ![![173, 0, 0], ![-36, 1, 0]]
  ![![-10613549365043540418976680187518634164, 2134438569686351661643129498547130935, -763650912002003765444079225284585686]] where
 M := ![![![29929, 0, 0], ![-6228, 173, 0]], ![![6401, 173, 0], ![-1329, -1, 6]]]
 hmul := by decide  
 g := ![![![![-1310267424546692825628, -29801778056710030969, 33941042639330834528]], ![![236237058650365716249, 2699884114194070562, -7507890609469235406]]], ![![![-316650351707487325779, -9875432638059295107, 6814052238340885522]], ![![58513380369589501689, 1087185439695044585, -1642290865280953716]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![-10613549365043540418976680187518634164, 2134438569686351661643129498547130935, -763650912002003765444079225284585686]] ![![7573800141888397836, 172264613044566653, -196190997915207136]]
  ![![173, 0, 0]] where
 M := ![![![-173, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![50, 26, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![50, 26, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![50, 26, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![50, 26, 1], ![-105, 17, 159], ![-4901, 473, 149]]]
  hmulB := by decide  
  f := ![![![-49, -26, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-50, -26, 179]], ![![0, 0, 1], ![-45, -23, 159], ![-69, -19, 149]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [163, 122, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 178], [0, 1]]
 g := ![![[149, 66], [76, 173], [45], [45], [54, 147], [141, 27], [1]], ![[152, 113], [92, 6], [45], [45], [20, 32], [69, 152], [1]]]
 h' := ![![[57, 178], [142, 148], [71, 129], [70, 90], [148, 89], [108, 133], [16, 57], [0, 1]], ![[0, 1], [165, 31], [85, 50], [9, 89], [30, 90], [171, 46], [43, 122], [57, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [38, 118]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [163, 122, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-752947, -1286826, 766430]
  a := ![-129, 65, -194]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-218293, -118514, 766430]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![20, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![20, 1, 0]] 
 ![![179, 0, 0], ![20, 1, 0], ![30, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![20, 1, 0], ![3, 18, 6], ![-183, 19, 23]]]
  hmulB := by decide  
  f := ![![![-539, -3240, -1080], ![0, 32220, 0]], ![![-60, -360, -120], ![1, 3580, 0]], ![![-90, -543, -181], ![-3, 5400, 0]]]
  g := ![![![1, 0, 0], ![-20, 179, 0], ![-30, 0, 179]], ![![0, 1, 0], ![-3, 18, 6], ![-7, 19, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![50, 26, 1]] ![![179, 0, 0], ![20, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![3580, 179, 0]], ![![8950, 4654, 179], ![895, 537, 179]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![20, 1, 0]]], ![![![50, 26, 1]], ![![5, 3, 1]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![48, 1, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![48, 1, 0]] 
 ![![181, 0, 0], ![48, 1, 0], ![85, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![48, 1, 0], ![3, 46, 6], ![-183, 19, 51]]]
  hmulB := by decide  
  f := ![![![60025, 1007833, 131472], ![21539, -3966072, 0]], ![![15894, 267228, 34860], ![5793, -1051610, 0]], ![![28153, 473291, 61741], ![10249, -1862520, 0]]]
  g := ![![![1, 0, 0], ![-48, 181, 0], ![-85, 0, 181]], ![![0, 1, 0], ![-15, 46, 6], ![-30, 19, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-25, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-25, 1, 0]] 
 ![![181, 0, 0], ![156, 1, 0], ![69, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-25, 1, 0], ![3, -27, 6], ![-183, 19, -22]]]
  hmulB := by decide  
  f := ![![![79119, -730430, 162336], ![-14842, -4897136, 0]], ![![68180, -629515, 139908], ![-12850, -4220558, 0]], ![![30156, -278451, 61885], ![-5697, -1866864, 0]]]
  g := ![![![1, 0, 0], ![-156, 181, 0], ![-69, 0, 181]], ![![-1, 1, 0], ![21, -27, 6], ![-9, 19, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1650738225753814588193, -278900482416490070864, -82592390631788957682]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![-1650738225753814588193, -278900482416490070864, -82592390631788957682]] 
 ![![181, 0, 0], ![157, 1, 0], ![168, 0, 1]] where
  M :=![![![-1650738225753814588193, -278900482416490070864, -82592390631788957682], ![14277706038367909043214, -2662192682924824642423, -1921180066394307298230], ![62849500142563503916638, -3564668962645743235094, -4221879876270852912107]]]
  hmulB := by decide  
  f := ![![![-4391086760466353108672571384266369662431641, 883069802760561143081013370820924250258340, -315941189321099331685200977496949552827234]], ![![-3474774443862842966485960709035444729743695, 698794751769722302579368411715662141568473, -250011997098411747022906498202134712435400]], ![![-4718921323705043132651014915110030138295566, 948998994983248727743307850115739090650174, -339529072562831178828356442092414709370187]]]
  g := ![![![309459442761191554851, -278900482416490070864, -82592390631788957682], ![4171271869678502784565, -2662192682924824642423, -1921180066394307298230], ![7357891417079825862212, -3564668962645743235094, -4221879876270852912107]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![48, 1, 0]] ![![181, 0, 0], ![-25, 1, 0]]
  ![![-4391086760466353108672571384266369662431641, 883069802760561143081013370820924250258340, -315941189321099331685200977496949552827234]] where
 M := ![![![32761, 0, 0], ![-4525, 181, 0]], ![![8688, 181, 0], ![-1197, 21, 6]]]
 hmul := by decide  
 g := ![![![![-298783618861440440462933, -50480987317384702826384, -14949222704353801340442]], ![![55546161682213273748039, 4310319377487427129177, 143629699400416643820]]], ![![![-64957728797815191190050, -16049415838916348043895, -5885614816720177266966]], ![![14656698806013387709803, 1417402305719573690181, 183353762068208903922]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![-4391086760466353108672571384266369662431641, 883069802760561143081013370820924250258340, -315941189321099331685200977496949552827234]] ![![-1650738225753814588193, -278900482416490070864, -82592390631788957682]]
  ![![181, 0, 0]] where
 M := ![![![181, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149483106244687918771679116370, 28498981449337566947484466197, 9163535926221127912165904136]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![149483106244687918771679116370, 28498981449337566947484466197, 9163535926221127912165904136]] 
 ![![191, 0, 0], ![0, 191, 0], ![11, 133, 1]] where
  M :=![![![149483106244687918771679116370, 28498981449337566947484466197, 9163535926221127912165904136], ![-1591430130150453707083907058297, 266592325944214215207862362560, 198484496474688785421404509590], ![-6525699242678396042829381605499, 349046393086770085846720870887, 427414305043344305769616501817]]]
  hmulB := by decide  
  f := ![![![-233848566205241851876984651437108023608213314068535128090, 47028131872477789718334622000836824963240240602204451787, -16825537311877505560409749461776496245794383070692574770]], ![![3220157723691016886709988017507609287870092823743354538271, -647590038875870036961439135212535102204787073616102952294, 231692179299234221628778483619691461042058294401148986412]], ![![2196379825788390750463167191149658361371244145822083197362, -441703114820769390615459484735836426299360165070110026342, 158030777393875721549593955775955596282774033009574507997]]]
  g := ![![![254891157362594302292430214, -6231682181874724844872150701, 9163535926221127912165904136], ![-19763139221843090820520191957, -136815946100468032700727421010, 198484496474688785421404509590], ![-58781448157880541394215513746, -295796105642293311945090439114, 427414305043344305769616501817]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [94, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [136, 190], [0, 1]]
 g := ![![[27, 17], [93, 80], [104, 97], [80, 121], [152, 144], [12, 160], [1]], ![[47, 174], [86, 111], [117, 94], [110, 70], [63, 47], [189, 31], [1]]]
 h' := ![![[136, 190], [44, 50], [156, 135], [120, 111], [37, 11], [18, 12], [97, 136], [0, 1]], ![[0, 1], [159, 141], [180, 56], [127, 80], [5, 180], [122, 179], [66, 55], [136, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [155, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [94, 55, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1307, -4065, 1878]
  a := ![-5, 4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-115, -1329, 1878]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2305225364905561523242602072, -22429635744089738529527301, 75296682376242073938314098]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-2305225364905561523242602072, -22429635744089738529527301, 75296682376242073938314098]] 
 ![![191, 0, 0], ![154, 1, 0], ![142, 0, 1]] where
  M :=![![![-2305225364905561523242602072, -22429635744089738529527301, 75296682376242073938314098], ![-13846581782084568746300061837, -829729128268782641355579608, 91312232664187790637778488], ![-6662802238634194422275419931, -2007393409038788584765614777, -791283942236747186126587917]]]
  hmulB := by decide  
  f := ![![![839850909619888953899297109692084171958390423769913712, -168898274519073033812834059600751968228409581924448163, 60427750511933440057042703489041815340533505761212696]], ![![616607680179172043291175067933424368427168926494719601, -124002929620693595940144861692829426739736803242320240, 44365273210780690503029843404057870152320957659495834]], ![![740974058009466569179537779498851219948660221694493955, -149013638525242726099812462664874057627880347177076549, 53313504814177071108684584291118555852251953492535281]]]
  g := ![![![-49964347422733593135790574, -22429635744089738529527301, 75296682376242073938314098], ![528614486560174302365940589, -829729128268782641355579608, 91312232664187790637778488], ![2171927238486687686186412251, -2007393409038788584765614777, -791283942236747186126587917]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![149483106244687918771679116370, 28498981449337566947484466197, 9163535926221127912165904136]] ![![-2305225364905561523242602072, -22429635744089738529527301, 75296682376242073938314098]]
  ![![191, 0, 0]] where
 M := ![![![-800260553167522160910857812074497274490769667248217077145, -45394108279256926295479069025140961663741015848976545818, 6606928763786281401394858122254982638547543857765429684]]]
 hmul := by decide  
 g := ![![![![-4189845828102210266548993780494750128223924959414749095, -237665488373072912541775230498120218134769716486788198, 34591250072179483776936429959450170882447873600866124]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![456647, -91834, 32856]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![456647, -91834, 32856]] 
 ![![193, 0, 0], ![0, 193, 0], ![189, 135, 1]] where
  M :=![![![456647, -91834, 32856], ![-6288150, 1264579, -452436], ![12107214, -2434822, 871121]]]
  hmulB := by decide  
  f := ![![![1019, 74, 0]], ![![222, 871, 444]], ![![1083, 689, 317]]]
  g := ![![![-29809, -23458, 32856], ![410478, 323023, -452436], ![-790335, -621949, 871121]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [113, 170, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 192], [0, 1]]
 g := ![![[22, 21], [107], [170], [145], [107], [128], [23, 1]], ![[119, 172], [107], [170], [145], [107], [128], [46, 192]]]
 h' := ![![[23, 192], [124, 139], [153, 140], [177, 154], [93, 96], [5, 53], [103, 30], [0, 1]], ![[0, 1], [40, 54], [92, 53], [52, 39], [178, 97], [66, 140], [21, 163], [23, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [78, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [113, 170, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4005, -2778, 374]
  a := ![-5, 3, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-387, -276, 374]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1019, -74, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-1019, -74, 0]] 
 ![![193, 0, 0], ![152, 1, 0], ![157, 0, 1]] where
  M :=![![![-1019, -74, 0], ![-222, -871, -444], ![13542, -1406, -1241]]]
  hmulB := by decide  
  f := ![![![-456647, 91834, -32856]], ![![-327058, 65773, -23532]], ![![-434201, 87320, -31241]]]
  g := ![![![53, -74, 0], ![1046, -871, -444], ![2187, -1406, -1241]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![456647, -91834, 32856]] ![![-1019, -74, 0]]
  ![![193, 0, 0]] where
 M := ![![![-193, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)


lemma PB228I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB228I3 : PrimesBelowBoundCertificateInterval O 137 193 228 where
  m := 11
  g := ![1, 3, 2, 3, 3, 3, 3, 2, 3, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB228I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1, I157N1]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0, I173N1, I173N2]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1]
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
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2685619]
    · exact ![149, 149, 149]
    · exact ![22801, 151]
    · exact ![157, 157, 157]
    · exact ![163, 163, 163]
    · exact ![167, 167, 167]
    · exact ![173, 173, 173]
    · exact ![32041, 179]
    · exact ![181, 181, 181]
    · exact ![36481, 191]
    · exact ![37249, 193]
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
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
      exact NI173N2
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I149N0, I149N1, I149N2, I151N1, I157N0, I157N1, I163N0, I163N1, I163N2, I167N0, I167N1, I167N2, I173N0, I173N1, I173N2, I179N1, I181N0, I181N1, I181N2, I191N1, I193N1]
  Il := ![[], [I149N0, I149N1, I149N2], [I151N1], [I157N0, I157N1, I157N1], [I163N0, I163N1, I163N2], [I167N0, I167N1, I167N2], [I173N0, I173N1, I173N2], [I179N1], [I181N0, I181N1, I181N2], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
