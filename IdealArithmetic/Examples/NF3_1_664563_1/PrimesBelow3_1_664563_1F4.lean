
import IdealArithmetic.Examples.NF3_1_664563_1.RI3_1_664563_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-508204, -27306, -17183]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-508204, -27306, -17183]] 
 ![![197, 0, 0], ![0, 197, 0], ![142, 146, 1]] where
  M :=![![![-508204, -27306, -17183], ![-2422803, -130178, -81918], ![-3850146, -206869, -130178]]]
  hmulB := by decide  
  f := ![![![-86, 53, -22]], ![![-3102, 398, 159]], ![![-2323, 322, 104]]]
  g := ![![![9806, 12596, -17183], ![46749, 60050, -81918], ![74290, 95427, -130178]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [158, 186, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 196], [0, 1]]
 g := ![![[71, 101], [107], [183, 154], [154], [15], [187], [11, 1]], ![[0, 96], [107], [104, 43], [154], [15], [187], [22, 196]]]
 h' := ![![[11, 196], [91, 135], [45, 111], [13, 101], [36, 101], [47, 58], [35, 160], [0, 1]], ![[0, 1], [0, 62], [84, 86], [139, 96], [162, 96], [94, 139], [22, 37], [11, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128]]
 b := ![[], [42, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [158, 186, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![440, -183, -205]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![150, 151, -205]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![86, -53, 22]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![86, -53, 22]] 
 ![![197, 0, 0], ![153, 1, 0], ![77, 0, 1]] where
  M :=![![![86, -53, 22], ![3102, -398, -159], ![-7473, 2200, -398]]]
  hmulB := by decide  
  f := ![![![508204, 27306, 17183]], ![![406995, 21868, 13761]], ![![218182, 11723, 7377]]]
  g := ![![![33, -53, 22], ![387, -398, -159], ![-1591, 2200, -398]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-508204, -27306, -17183]] ![![86, -53, 22]]
  ![![197, 0, 0]] where
 M := ![![![-197, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8110023647070170718481, -1492968117913641163464, -131002705123754606208]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![8110023647070170718481, -1492968117913641163464, -131002705123754606208]] 
 ![![199, 0, 0], ![0, 199, 0], ![91, 53, 1]] where
  M :=![![![8110023647070170718481, -1492968117913641163464, -131002705123754606208], ![-18471381422449399475328, 10992083159792772055057, -4478904353740923490392], ![-210508504625823404048424, 26688171453283639104432, 10992083159792772055057]]]
  hmulB := by decide  
  f := ![![![1207837484961287298824787859038918178270807, 64897522873564435420691989893119858278008, 40838462473356387616050567659290656459456]], ![![5758223208743250653863130039959982560783296, 309391310547446771271675370534523736162775, 194692568620693306262075969679359574834024]], ![![2131907497085638262523211848569600653072147, 114548121977579774569753359904229593424141, 72082399660902629528755293570532818794857]]]
  g := ![![![100659647303175074791, 27387815344951522440, -131002705123754606208], ![1955321179738566020856, 1248110622653576467567, -4478904353740923490392], ![-6084362171693294779189, -2793428321687101908611, 10992083159792772055057]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [73, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [176, 198], [0, 1]]
 g := ![![[93, 72], [144, 92], [72, 193], [103], [125], [180], [176, 1]], ![[29, 127], [18, 107], [11, 6], [103], [125], [180], [153, 198]]]
 h' := ![![[176, 198], [35, 79], [117, 93], [147, 81], [30, 74], [1, 181], [87, 58], [0, 1]], ![[0, 1], [9, 120], [167, 106], [75, 118], [119, 125], [17, 18], [146, 141], [176, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [157]]
 b := ![[], [57, 178]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [73, 23, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1641, 645, -123]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![48, 36, -123]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1207837484961287298824787859038918178270807, -64897522873564435420691989893119858278008, -40838462473356387616050567659290656459456]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-1207837484961287298824787859038918178270807, -64897522873564435420691989893119858278008, -40838462473356387616050567659290656459456]] 
 ![![199, 0, 0], ![40, 1, 0], ![130, 0, 1]] where
  M :=![![![-1207837484961287298824787859038918178270807, -64897522873564435420691989893119858278008, -40838462473356387616050567659290656459456], ![-5758223208743250653863130039959982560783296, -309391310547446771271675370534523736162775, -194692568620693306262075969679359574834024], ![-9150550725172585394317570574929900017199128, -491662233029332638699152902338023971478256, -309391310547446771271675370534523736162775]]]
  hmulB := by decide  
  f := ![![![-8110023647070170718481, 1492968117913641163464, 131002705123754606208]], ![![-1537334494775665473688, 244857495260064695897, 48839259088900038888]], ![![-4240173716046727584694, 841194391334119156512, 30343057820579531417]]]
  g := ![![![33653585686018193507987263981877695942607, -64897522873564435420691989893119858278008, -40838462473356387616050567659290656459456], ![160439513235400753824491260501194530724376, -309391310547446771271675370534523736162775, -194692568620693306262075969679359574834024], ![254958839030998997080232882854669068055738, -491662233029332638699152902338023971478256, -309391310547446771271675370534523736162775]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![8110023647070170718481, -1492968117913641163464, -131002705123754606208]] ![![-1207837484961287298824787859038918178270807, -64897522873564435420691989893119858278008, -40838462473356387616050567659290656459456]]
  ![![199, 0, 0]] where
 M := ![![![-199, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0]] 
 ![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [16, 33, 148, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [116, 184, 122], [158, 26, 89], [0, 1]]
 g := ![![[151, 57, 21], [149, 144, 59], [127, 170], [113, 83], [204, 174, 81], [74, 171], [1]], ![[137, 210, 72, 24], [125, 81, 93, 170], [195, 185], [153, 5], [44, 192, 184, 204], [197, 58], [209, 147, 182, 193]], ![[90, 84, 152, 74], [2, 124, 95, 127], [198, 105], [44, 170], [185, 1, 91, 187], [61, 16], [77, 50, 109, 18]]]
 h' := ![![[116, 184, 122], [148, 0, 134], [70, 166, 103], [186, 99, 35], [112, 72, 111], [127, 98, 202], [195, 178, 63], [0, 1]], ![[158, 26, 89], [106, 186, 108], [162, 177, 142], [180, 43, 117], [27, 2, 65], [192, 116, 117], [161, 125, 144], [116, 184, 122]], ![[0, 1], [123, 25, 180], [151, 79, 177], [187, 69, 59], [141, 137, 35], [16, 208, 103], [123, 119, 4], [158, 26, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 104], []]
 b := ![[], [131, 150, 96], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [16, 33, 148, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![338866, -7596, 7596]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1606, -36, 36]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def PBC211 : ContainsPrimesAboveP 211 ![I211N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![211, 0, 0]]) timesTableT_eq_Table B_one_repr 211 (by decide) 𝕀

instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![636957544140630401419342852, -110748213006171840206796458, -14384737229078061692792583]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![636957544140630401419342852, -110748213006171840206796458, -14384737229078061692792583]] 
 ![![223, 0, 0], ![16, 1, 0], ![212, 0, 1]] where
  M :=![![![636957544140630401419342852, -110748213006171840206796458, -14384737229078061692792583], ![-2028247949300006698683754203, 953421763180347758660779678, -332244639018515520620389374], ![-15615498033870229469158300578, 1760378036369111584988270675, 953421763180347758660779678]]]
  hmulB := by decide  
  f := ![![![1493889223735501790200662123730757178950550672263591134, 80267181036406984270558032842777106795746340292376999, 50510221584014824205013395648801481981657177039565566]], ![![139121833287507259444473016888668716693374317124646650, 7475063881029988367799533385388153740296117587763142, 4703879320419094798618333761924462027326250464171211]], ![![1470951515506994458765421761711892798187071643502719629, 79034730095811765690769757110409506476814762226059244, 49734669617481248381852947520192998903432351164937438]]]
  g := ![![![24477548182977259747085712, -110748213006171840206796458, -14384737229078061692792583], ![238353665075066006880118019, 953421763180347758660779678, -332244639018515520620389374], ![-1102721795560581792219981718, 1760378036369111584988270675, 953421763180347758660779678]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N0 : Nat.card (O ⧸ I223N0) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N0)

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := prime_ideal_of_norm_prime hp223.out _ NI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-458, 77, 12]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-458, 77, 12]] 
 ![![223, 0, 0], ![92, 1, 0], ![152, 0, 1]] where
  M :=![![![-458, 77, 12], ![1692, -722, 231], ![10857, -1130, -722]]]
  hmulB := by decide  
  f := ![![![782314, 42034, 26451]], ![![339473, 18240, 11478]], ![![559814, 30079, 18928]]]
  g := ![![![-42, 77, 12], ![148, -722, 231], ![1007, -1130, -722]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![418732118323985430513602458, -16857239062722326466525103, -44663170090775655855671970]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![418732118323985430513602458, -16857239062722326466525103, -44663170090775655855671970]] 
 ![![223, 0, 0], ![115, 1, 0], ![126, 0, 1]] where
  M :=![![![418732118323985430513602458, -16857239062722326466525103, -44663170090775655855671970], ![-6297506982799367475649747770, 1401321860321049859338385798, -50571717188166979399575309], ![-2376870707843848031780039523, -1728309734886564642953030324, 1401321860321049859338385798]]]
  hmulB := by decide  
  f := ![![![1876299365087408775678570957127647056466606952089426688, 100814209262032738487789677593631535495830389072505474, 63439976125894529880735766192480831302681645582163887]], ![![1007710599187458017561521987008157886579990634607036669, 54144636571531363427794605489509844618063253330134308, 34071927723156812339677049977202646665003948023167549]], ![![1123894724246457945570754641877962222509885922970811814, 60387249511966133215805863142530398039427792851579695, 38000255077042331315134935610518625614105372612710632]]]
  g := ![![![35806610053698590188245101, -16857239062722326466525103, -44663170090775655855671970], ![-722320558538166196839540922, 1401321860321049859338385798, -50571717188166979399575309], ![88843921092640375027721243, -1728309734886564642953030324, 1401321860321049859338385798]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![636957544140630401419342852, -110748213006171840206796458, -14384737229078061692792583]] ![![-458, 77, 12]]
  ![![-635287623718951993278607706783, 145260693758142819251452061070, -7553566395343769728541622648]] where
 M := ![![![-635287623718951993278607706783, 145260693758142819251452061070, -7553566395343769728541622648]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![-635287623718951993278607706783, 145260693758142819251452061070, -7553566395343769728541622648]] ![![418732118323985430513602458, -16857239062722326466525103, -44663170090775655855671970]]
  ![![223, 0, 0]] where
 M := ![![![-1162841714988186387227827768418365451571379059999636469610, 227321083289490825625206626560851033559265389531158735461, 10442898758248806562857549107618424941319862666501498776]]]
 hmul := by decide  
 g := ![![![![-5214536838512046579496985508602535657270758116590298070, 1019377055109824330157877249151798356768006231081429307, 46829142413671778308778247119365134266008352764580712]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1, I223N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
    exact isPrimeI223N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0 ⊙ MulI223N1)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![889366140741168842209, 26204324962788180964, -133882664727768117354]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![889366140741168842209, 26204324962788180964, -133882664727768117354]] 
 ![![227, 0, 0], ![0, 227, 0], ![93, 42, 1]] where
  M :=![![![889366140741168842209, 26204324962788180964, -133882664727768117354], ![-18877455726615304546914, 3834784764752067423997, 78612974888364542892], ![3694809819753133515924, -6868980391386441496846, 3834784764752067423997]]]
  hmulB := by decide  
  f := ![![![67161080066040968588223152458720618595483, 3608587897020669454477428463210229941288, 2270798250672777032329254405187106641638]], ![![320182553344861561558424871131382036470958, 17203518551239873876979555544604272479447, 10825763691062008363432285389630689823864]], ![![88997614890334405538501828984544958074369, 4781872412432435042381117668744932960904, 3009118197746310524879983266922881774247]]]
  g := ![![![58768519649443188353, 24886679486912110616, -133882664727768117354], ![-115367675732304876810, 2348193037183949879, 78612974888364542892], ![-1554802525560304567911, -739779473616622349360, 3834784764752067423997]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [221, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [221, 226], [0, 1]]
 g := ![![[226, 189], [125, 210], [44], [222], [16], [12, 175], [221, 1]], ![[0, 38], [0, 17], [44], [222], [16], [97, 52], [215, 226]]]
 h' := ![![[221, 226], [69, 125], [110, 94], [46, 147], [59, 26], [72, 4], [191, 42], [0, 1]], ![[0, 1], [0, 102], [0, 133], [72, 80], [130, 201], [48, 223], [166, 185], [221, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121]]
 b := ![[], [68, 174]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [221, 6, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-618, 563, -219]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![87, 43, -219]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67161080066040968588223152458720618595483, 3608587897020669454477428463210229941288, 2270798250672777032329254405187106641638]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![67161080066040968588223152458720618595483, 3608587897020669454477428463210229941288, 2270798250672777032329254405187106641638]] 
 ![![227, 0, 0], ![101, 1, 0], ![156, 0, 1]] where
  M :=![![![67161080066040968588223152458720618595483, 3608587897020669454477428463210229941288, 2270798250672777032329254405187106641638], ![320182553344861561558424871131382036470958, 17203518551239873876979555544604272479447, 10825763691062008363432285389630689823864], ![508810893479914393081317413312642421721608, 27338584047165792520971530853168953448650, 17203518551239873876979555544604272479447]]]
  hmulB := by decide  
  f := ![![![889366140741168842209, 26204324962788180964, -133882664727768117354]], ![![312548566027501094785, 28552517999972130843, -59222626267031785506]], ![![627471047468614418064, -12251566947980111306, -75114145078324929001]]]
  g := ![![![-2870267949947135961926699601474454808679, 3608587897020669454477428463210229941288, 2270798250672777032329254405187106641638], ![-13683665005004577113268487928000163420599, 17203518551239873876979555544604272479447, 10825763691062008363432285389630689823864], ![-21745088058490092406808889285531666887162, 27338584047165792520971530853168953448650, 17203518551239873876979555544604272479447]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![889366140741168842209, 26204324962788180964, -133882664727768117354]] ![![67161080066040968588223152458720618595483, 3608587897020669454477428463210229941288, 2270798250672777032329254405187106641638]]
  ![![227, 0, 0]] where
 M := ![![![227, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0]] 
 ![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [76, 127, 185, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [179, 85, 216], [94, 143, 13], [0, 1]]
 g := ![![[79, 65, 225], [169, 167], [146, 0, 147], [135, 187], [32, 154], [98, 41, 104], [1]], ![[175, 93, 45, 41], [177, 172], [139, 56, 209, 200], [159, 147], [222, 215], [137, 84, 129, 163], [210, 175, 13, 93]], ![[212, 60, 111, 182], [218, 135], [39, 197, 159, 106], [27, 99], [12, 181], [8, 109, 56, 116], [221, 82, 167, 136]]]
 h' := ![![[179, 85, 216], [33, 137, 214], [125, 139, 204], [210, 171, 190], [60, 49, 88], [109, 61, 200], [153, 102, 44], [0, 1]], ![[94, 143, 13], [85, 197, 196], [22, 63, 114], [33, 159, 215], [155, 16, 39], [220, 44, 98], [104, 69, 157], [179, 85, 216]], ![[0, 1], [15, 124, 48], [18, 27, 140], [21, 128, 53], [142, 164, 102], [162, 124, 160], [151, 58, 28], [94, 143, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [167, 91], []]
 b := ![[], [121, 120, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [76, 127, 185, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54502, 687, -4351]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![238, 3, -19]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 12008989 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def PBC229 : ContainsPrimesAboveP 229 ![I229N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![229, 0, 0]]) timesTableT_eq_Table B_one_repr 229 (by decide) 𝕀



lemma PB231I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 230 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 230 (by omega)

def PB231I4 : PrimesBelowBoundCertificateInterval O 193 230 231 where
  m := 6
  g := ![2, 2, 1, 3, 2, 1]
  P := ![197, 199, 211, 223, 227, 229]
  hP := PB231I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0, I199N1]
    · exact ![I211N0]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0, I227N1]
    · exact ![I229N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![39601, 199]
    · exact ![9393931]
    · exact ![223, 223, 223]
    · exact ![51529, 227]
    · exact ![12008989]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
      exact NI223N2
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
  β := ![I197N1, I199N1, I223N0, I223N1, I223N2, I227N1]
  Il := ![[I197N1], [I199N1], [], [I223N0, I223N1, I223N2], [I227N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
