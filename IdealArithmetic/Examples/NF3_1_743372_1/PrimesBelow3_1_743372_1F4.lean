
import IdealArithmetic.Examples.NF3_1_743372_1.RI3_1_743372_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14781705383200581367294654834031816701, -2109966774711500272223972120136260072, 995116733181123029855297661613866167]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![14781705383200581367294654834031816701, -2109966774711500272223972120136260072, 995116733181123029855297661613866167]] 
 ![![197, 0, 0], ![0, 197, 0], ![179, 146, 1]] where
  M :=![![![14781705383200581367294654834031816701, -2109966774711500272223972120136260072, 995116733181123029855297661613866167], ![-173270044881864661407335169917721240796, 24732872715011811665847631450170478371, -11664683915087878603488535059203694265], ![336046133454487725016430167799862345875, -47967819543005324528332758064936987229, 22622905940300311393623659330034218299]]]
  hmulB := by decide  
  f := ![![![6433396776974347052, 50619194985234905, -256886709857600441]], ![![44235133290492510757, 3864529678398342642, 46828460053808989]], ![![38619984381314769041, 2947839096774226572, -178835619407465934]]]
  g := ![![![-829158324143250969425399119770813336, -748208171670839911832981881805891982, 995116733181123029855297661613866167], ![9719331857456170602117322871470761587, 8770440224963665420178546954791420513, -11664683915087878603488535059203694265], ![-18850020456138416316965506864346511318, -17009706024501780649732929036801689639, 22622905940300311393623659330034218299]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [88, 191, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 196], [0, 1]]
 g := ![![[85, 150], [63], [73, 101], [76], [164], [143], [6, 1]], ![[0, 47], [63], [88, 96], [76], [164], [143], [12, 196]]]
 h' := ![![[6, 196], [188, 100], [77, 121], [10, 62], [0, 43], [53, 19], [63, 145], [0, 1]], ![[0, 1], [0, 97], [15, 76], [185, 135], [61, 154], [167, 178], [145, 52], [6, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [91, 101]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [88, 191, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3137, -1041, -756]
  a := ![-1, -1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![671, 555, -756]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6433396776974347052, -50619194985234905, 256886709857600441]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-6433396776974347052, -50619194985234905, 256886709857600441]] 
 ![![197, 0, 0], ![108, 1, 0], ![59, 0, 1]] where
  M :=![![![-6433396776974347052, -50619194985234905, 256886709857600441], ![-44235133290492510757, -3864529678398342642, -46828460053808989], ![1770560371305191753, -7442133116007560957, -3915148873383577547]]]
  hmulB := by decide  
  f := ![![![-14781705383200581367294654834031816701, 2109966774711500272223972120136260072, -995116733181123029855297661613866167]], ![![-7224132672608112316043084021105152096, 1031185476922996029108331764083987865, -486334635880575678278597017233978943]], ![![-6132826147529553429882308644709337722, 875410453050679393855569102299372241, -412866970548155178452214321651027016]]]
  g := ![![![-81841825381560423, -50619194985234905, 256886709857600441], ![1908106350861437690, -3864529678398342642, -46828460053808989], ![5261496042790623606, -7442133116007560957, -3915148873383577547]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![14781705383200581367294654834031816701, -2109966774711500272223972120136260072, 995116733181123029855297661613866167]] ![![-6433396776974347052, -50619194985234905, 256886709857600441]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0]] 
 ![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [164, 138, 134, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 73, 188], [14, 125, 11], [0, 1]]
 g := ![![[64, 180, 111], [112, 109, 58], [37, 165, 126], [34, 98], [89, 50], [174, 46], [1]], ![[117, 108, 21, 180], [190, 149, 14, 157], [21, 98, 191, 161], [18, 102], [43, 122], [186, 122], [129, 23, 82, 62]], ![[174, 2, 46, 142], [149, 72, 111, 191], [194, 176, 157, 176], [195, 70], [196, 81], [3, 58], [154, 52, 152, 137]]]
 h' := ![![[51, 73, 188], [139, 152, 132], [101, 31, 156], [122, 75, 46], [46, 34, 59], [151, 176, 99], [35, 61, 65], [0, 1]], ![[14, 125, 11], [77, 113, 102], [154, 11, 55], [42, 137, 149], [3, 74, 36], [182, 183, 91], [55, 198, 91], [51, 73, 188]], ![[0, 1], [19, 133, 164], [13, 157, 187], [69, 186, 4], [72, 91, 104], [133, 39, 9], [174, 139, 43], [14, 125, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127, 84], []]
 b := ![[], [134, 75, 80], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [164, 138, 134, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11979004, -1999154, 506256]
  a := ![2, -2, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![60196, -10046, 2544]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 7880599 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def PBC199 : ContainsPrimesAboveP 199 ![I199N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![199, 0, 0]]) timesTableT_eq_Table B_one_repr 199 (by decide) 𝕀

instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![533687461150690812637912619454309, 39183300686855558725943403857050, -3271927391349287177681455405029]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![533687461150690812637912619454309, 39183300686855558725943403857050, -3271927391349287177681455405029]] 
 ![![211, 0, 0], ![0, 211, 0], ![59, 196, 1]] where
  M :=![![![533687461150690812637912619454309, 39183300686855558725943403857050, -3271927391349287177681455405029], ![601954811998932953287153733522038, 500968187237197940861098065404019, 231827876729784065177978967737271], ![-6651185678572725347064866167476817, 480175046434986341056833334506283, 540151487924053499587041469261069]]]
  hmulB := by decide  
  f := ![![![-754885072346634801645510733932035504913213708524545641641848638, 107753630591723531857210515990485613633010629193286422898182387, -50819492585376303704235882462878839927671375340192137784883991]], ![![8848706355276447768985782299605646081192487187706334121898228839, -1263079998200397838687869558560823904189927461926467019490688548, 595702290964964887439027213480034841870392399819526399604210331]], ![![7927235678690810531491480367283652797426621700949920464535015545, -1131547643775563471491282175583318716599530435967135473554542668, 533668116582877922808856671726097815925627404676884633158884186]]]
  g := ![![![3444223588816581782564542598820, 3225028764887752822518998403994, -3271927391349287177681455405029], ![-61971042251461264892007608355341, -212972965174409852293946822801427, 231827876729784065177978967737271], ![-182559826853516027595736079876208, -499476381927390993260679121519731, 540151487924053499587041469261069]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [88, 139, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [72, 210], [0, 1]]
 g := ![![[191, 52], [65, 69], [144], [119], [3, 93], [180], [72, 1]], ![[137, 159], [180, 142], [144], [119], [158, 118], [180], [144, 210]]]
 h' := ![![[72, 210], [188, 91], [46, 160], [144, 199], [158, 69], [21, 127], [205, 32], [0, 1]], ![[0, 1], [199, 120], [172, 51], [124, 12], [62, 142], [92, 84], [188, 179], [72, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [171]]
 b := ![[], [87, 191]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [88, 139, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2762029, -2875963, 1059180]
  a := ![-65, 1, -326]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-309259, -997513, 1059180]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![754885072346634801645510733932035504913213708524545641641848638, -107753630591723531857210515990485613633010629193286422898182387, 50819492585376303704235882462878839927671375340192137784883991]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![754885072346634801645510733932035504913213708524545641641848638, -107753630591723531857210515990485613633010629193286422898182387, 50819492585376303704235882462878839927671375340192137784883991]] 
 ![![211, 0, 0], ![89, 1, 0], ![157, 0, 1]] where
  M :=![![![754885072346634801645510733932035504913213708524545641641848638, -107753630591723531857210515990485613633010629193286422898182387, 50819492585376303704235882462878839927671375340192137784883991], ![-8848706355276447768985782299605646081192487187706334121898228839, 1263079998200397838687869558560823904189927461926467019490688548, -595702290964964887439027213480034841870392399819526399604210331], ![17161498161971287279425839923865796866830701087060077018295502807, -2449662605722395518586473986402584814377233426118051949173691627, 1155326367608674306830659042570338290556916832733180596592506161]]]
  hmulB := by decide  
  f := ![![![-533687461150690812637912619454309, -39183300686855558725943403857050, 3271927391349287177681455405029]], ![![-227962743385831352028726904573249, -18901810181835747239194601936879, 281391758769206130974742006210]], ![![-365581733280027167000414289511136, -31431058077115208820047145687503, -125397571005760249720630192756]]]
  g := ![![![11214681796710660925934659291058186017093619802449628660442154, -107753630591723531857210515990485613633010629193286422898182387, 50819492585376303704235882462878839927671375340192137784883991], ![-131457661201954351110326542631059257727224760793821109567338804, 1263079998200397838687869558560823904189927461926467019490688548, -595702290964964887439027213480034841870392399819526399604210331], ![254953698372998209768760924313520065066201579490319179287822703, -2449662605722395518586473986402584814377233426118051949173691627, 1155326367608674306830659042570338290556916832733180596592506161]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![533687461150690812637912619454309, 39183300686855558725943403857050, -3271927391349287177681455405029]] ![![754885072346634801645510733932035504913213708524545641641848638, -107753630591723531857210515990485613633010629193286422898182387, 50819492585376303704235882462878839927671375340192137784883991]]
  ![![211, 0, 0]] where
 M := ![![![-211, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0]] 
 ![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [220, 142, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 183], [86, 39], [0, 1]]
 g := ![![[106, 39, 130], [142, 65, 62], [106, 208, 39], [133, 44, 213], [104, 28, 211], [57, 203], [1]], ![[67, 114, 164], [116, 75, 188], [100, 121, 183], [141, 204, 56], [166, 211, 201], [164, 131], [1]], ![[19, 70, 152], [221, 83, 196], [36, 117, 1], [202, 198, 177], [61, 207, 34], [121, 112], [1]]]
 h' := ![![[95, 183], [203, 206, 199], [95, 46, 109], [176, 94, 183], [89, 99, 131], [180, 137, 65], [3, 81, 181], [0, 1]], ![[86, 39], [82, 220, 179], [77, 212, 14], [0, 82, 1], [57, 149, 203], [173, 40, 82], [166, 192, 146], [95, 183]], ![[0, 1], [83, 20, 68], [56, 188, 100], [90, 47, 39], [70, 198, 112], [95, 46, 76], [63, 173, 119], [86, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [201], []]
 b := ![[], [58, 72, 130], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [220, 142, 42, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10493265, 1056128, -120197]
  a := ![-2, 1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-47055, 4736, -539]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 11089567 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def PBC223 : ContainsPrimesAboveP 223 ![I223N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![223, 0, 0]]) timesTableT_eq_Table B_one_repr 223 (by decide) 𝕀

instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0]] 
 ![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [73, 138, 124, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [75, 55, 76], [28, 171, 151], [0, 1]]
 g := ![![[170, 191, 207], [38, 91, 10], [112, 108], [27, 166], [92, 99], [212, 123, 167], [1]], ![[68, 29, 122, 205], [72, 216, 82, 112], [172, 212], [26, 214], [190, 78], [190, 187, 145, 160], [216, 164, 81, 185]], ![[104, 5, 185, 66], [11, 103, 225, 211], [50, 65], [221, 84], [1, 173], [180, 86, 36, 22], [76, 179, 70, 42]]]
 h' := ![![[75, 55, 76], [177, 225, 175], [218, 37, 64], [201, 35, 154], [105, 14, 47], [187, 9, 107], [154, 89, 103], [0, 1]], ![[28, 171, 151], [50, 194, 36], [101, 2, 136], [95, 204, 165], [152, 146, 21], [42, 79, 140], [4, 137, 88], [75, 55, 76]], ![[0, 1], [91, 35, 16], [121, 188, 27], [65, 215, 135], [9, 67, 159], [38, 139, 207], [60, 1, 36], [28, 171, 151]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 42], []]
 b := ![[], [99, 68, 101], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [73, 138, 124, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1119337, 8626, 51756]
  a := ![-1, -1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4931, 38, 228]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 11697083 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def PBC227 : ContainsPrimesAboveP 227 ![I227N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![227, 0, 0]]) timesTableT_eq_Table B_one_repr 227 (by decide) 𝕀

instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7762220943819756365232801949242827172084199082226523865117189360839, -1107993148614845864520930011361034841304702040027664383833724528562, 522559187021999505816564229027766774621476107480961123419110833694]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![7762220943819756365232801949242827172084199082226523865117189360839, -1107993148614845864520930011361034841304702040027664383833724528562, 522559187021999505816564229027766774621476107480961123419110833694]] 
 ![![229, 0, 0], ![0, 229, 0], ![200, 44, 1]] where
  M :=![![![7762220943819756365232801949242827172084199082226523865117189360839, -1107993148614845864520930011361034841304702040027664383833724528562, 522559187021999505816564229027766774621476107480961123419110833694], ![-90988173316398760864969977404136920076198592526752977611920787923930, 12987812814039751423398444239520494918298960157036135099308297697779, -6125399704667075681309015839138442273206736132685025179583236337678], ![176465723512159502040552727770348289789628895982772323687084626402926, -25189029535742445302256534297360051327826875302262594170653237795358, 11879819665424905558877514228159460076994258117008470715474573169217]]]
  hmulB := by decide  
  f := ![![![3204840766858732255149457791018211, 312010678210887656697326181801238, 19905279470656576634400525963290]], ![![-3111697390742043524419564283884642, 3403893561565298021493463050651111, 1891969348735982516818357616770718]], ![![1964411305594393587049614900619634, 937799635753064599489179293475546, 397133674577688784913007115995729]]]
  g := ![![![-422487408124804125755808051774281780577340709231291269950676757109, -105242783308221939390610288596431322815063977158034732813426206162, 522559187021999505816564229027766774621476107480961123419110833694], ![4952365797454219979898834892679264343079251676900664010064307771230, 1233648034145812582537096686295248711525743886441822021838299984959, -6125399704667075681309015839138442273206736132685025179583236337678], ![-9604795674990487378755240689351719325804466058597911875143362477906, -2392581200063049300842214673957975086094210622055176007211940861314, 11879819665424905558877514228159460076994258117008470715474573169217]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [216, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [200, 228], [0, 1]]
 g := ![![[33, 48], [85], [135, 68], [43], [45], [79, 180], [200, 1]], ![[15, 181], [85], [224, 161], [43], [45], [126, 49], [171, 228]]]
 h' := ![![[200, 228], [164, 174], [152, 139], [184, 86], [82, 57], [111, 198], [81, 167], [0, 1]], ![[0, 1], [156, 55], [14, 90], [209, 143], [32, 172], [94, 31], [47, 62], [200, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [61, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [216, 29, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-74524, 1540, 4157]
  a := ![2, 19, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3956, -792, 4157]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3204840766858732255149457791018211, -312010678210887656697326181801238, -19905279470656576634400525963290]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![-3204840766858732255149457791018211, -312010678210887656697326181801238, -19905279470656576634400525963290]] 
 ![![229, 0, 0], ![193, 1, 0], ![204, 0, 1]] where
  M :=![![![-3204840766858732255149457791018211, -312010678210887656697326181801238, -19905279470656576634400525963290], ![3111697390742043524419564283884642, -3403893561565298021493463050651111, -1891969348735982516818357616770718], ![54203279197980404521068917470821766, -2582664236401148997844447617003550, -3715904239776185678190789232452349]]]
  hmulB := by decide  
  f := ![![![-7762220943819756365232801949242827172084199082226523865117189360839, 1107993148614845864520930011361034841304702040027664383833724528562, -522559187021999505816564229027766774621476107480961123419110833694]], ![![-6144630868300498766921226195632003162166165198004218901116579732393, 877095479775657207114153047830389648268596216455472013015722866003, -413661674194667375289466726476945612352568352013713849957664430416]], ![![-7685409589744060264401940285658886606527534972737917869742319895258, 1097028960057515291111468369497865322943170705100026761889663937214, -517388182610972946486710117684820445850547528572596244074118704117]]]
  g := ![![![266698240785399681750446299533327, -312010678210887656697326181801238, -19905279470656576634400525963290], ![4567794331506484694775558457994653, -3403893561565298021493463050651111, -1891969348735982516818357616770718], ![5723589265230323316401608344859328, -2582664236401148997844447617003550, -3715904239776185678190789232452349]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![7762220943819756365232801949242827172084199082226523865117189360839, -1107993148614845864520930011361034841304702040027664383833724528562, 522559187021999505816564229027766774621476107480961123419110833694]] ![![-3204840766858732255149457791018211, -312010678210887656697326181801238, -19905279470656576634400525963290]]
  ![![229, 0, 0]] where
 M := ![![![-229, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0]] 
 ![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [226, 170, 223, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 84, 181], [175, 148, 52], [0, 1]]
 g := ![![[43, 149, 126], [128, 215], [33, 173], [133, 100, 161], [20, 124], [156, 163, 100], [1]], ![[191, 56, 202, 113], [140, 219], [155, 8], [94, 41, 121, 23], [4, 55], [151, 183, 133, 8], [81, 230, 191, 124]], ![[177, 220, 27, 123], [154, 60], [23, 66], [17, 219, 163, 66], [218, 133], [198, 204, 62, 187], [164, 38, 85, 109]]]
 h' := ![![[68, 84, 181], [198, 97, 142], [232, 76, 94], [232, 209, 147], [110, 35, 45], [160, 67, 130], [7, 63, 10], [0, 1]], ![[175, 148, 52], [189, 20, 128], [181, 124, 174], [93, 127, 170], [113, 82, 180], [205, 64, 145], [216, 204, 68], [68, 84, 181]], ![[0, 1], [183, 116, 196], [152, 33, 198], [34, 130, 149], [142, 116, 8], [108, 102, 191], [125, 199, 155], [175, 148, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [215, 63], []]
 b := ![[], [29, 160, 167], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [226, 170, 223, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5946859, -6291, 23067]
  a := ![-2, 3, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-25523, -27, 99]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def PBC233 : ContainsPrimesAboveP 233 ![I233N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![233, 0, 0]]) timesTableT_eq_Table B_one_repr 233 (by decide) 𝕀

instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0]] 
 ![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [214, 5, 231, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [167, 175, 111], [80, 63, 128], [0, 1]]
 g := ![![[217, 25, 4], [50, 97, 90], [189, 143, 11], [51, 169, 24], [174, 204], [215, 193, 64], [1]], ![[152, 235, 130, 73], [113, 164, 68, 123], [9, 162, 120, 59], [15, 50, 183, 94], [127, 180], [150, 8, 209, 238], [105, 88, 96, 73]], ![[23, 68, 137, 150], [153, 222, 215, 18], [211, 199, 205, 134], [28, 66, 162, 170], [119, 2], [173, 167, 90, 62], [3, 139, 225, 166]]]
 h' := ![![[167, 175, 111], [55, 181, 237], [184, 187, 114], [80, 236, 190], [114, 41, 195], [117, 73, 193], [25, 234, 8], [0, 1]], ![[80, 63, 128], [188, 120, 128], [159, 142, 215], [69, 140, 165], [231, 90, 106], [101, 186, 186], [66, 109, 188], [167, 175, 111]], ![[0, 1], [67, 177, 113], [213, 149, 149], [50, 102, 123], [100, 108, 177], [145, 219, 99], [137, 135, 43], [80, 63, 128]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 9], []]
 b := ![[], [156, 105, 226], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [214, 5, 231, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4898305, -1770990, 375708]
  a := ![2, 1, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![20495, -7410, 1572]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 13651919 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def PBC239 : ContainsPrimesAboveP 239 ![I239N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![239, 0, 0]]) timesTableT_eq_Table B_one_repr 239 (by decide) 𝕀

instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0]] 
 ![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [162, 105, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [189, 87, 47], [19, 153, 194], [0, 1]]
 g := ![![[39, 102, 25], [152, 196], [30, 240], [149, 12], [203, 79, 79], [136, 154, 125], [1]], ![[139, 41, 57, 6], [164, 45], [156, 236], [156, 150], [222, 211, 141, 134], [45, 79, 7, 235], [16, 221, 215, 193]], ![[89, 69, 181, 80], [120, 217], [79, 29], [196, 47], [78, 46, 55, 192], [50, 211, 118, 216], [108, 168, 147, 48]]]
 h' := ![![[189, 87, 47], [170, 165, 5], [104, 39, 227], [12, 96, 64], [131, 188, 129], [140, 30, 101], [79, 136, 208], [0, 1]], ![[19, 153, 194], [119, 188, 85], [30, 18, 173], [31, 197, 85], [203, 201, 135], [45, 190, 234], [195, 210, 138], [189, 87, 47]], ![[0, 1], [135, 129, 151], [81, 184, 82], [61, 189, 92], [1, 93, 218], [59, 21, 147], [208, 136, 136], [19, 153, 194]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [212, 40], []]
 b := ![[], [146, 238, 194], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [162, 105, 33, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-68647163, 8133750, -602500]
  a := ![-5, 0, -25]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-284843, 33750, -2500]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 13997521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def PBC241 : ContainsPrimesAboveP 241 ![I241N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![241, 0, 0]]) timesTableT_eq_Table B_one_repr 241 (by decide) 𝕀



lemma PB244I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 243 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 243 (by omega)

def PB244I4 : PrimesBelowBoundCertificateInterval O 193 243 244 where
  m := 9
  g := ![2, 1, 2, 1, 1, 2, 1, 1, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241]
  hP := PB244I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
    · exact ![I211N0, I211N1]
    · exact ![I223N0]
    · exact ![I227N0]
    · exact ![I229N0, I229N1]
    · exact ![I233N0]
    · exact ![I239N0]
    · exact ![I241N0]
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
    · exact PBC233
    · exact PBC239
    · exact PBC241
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![7880599]
    · exact ![44521, 211]
    · exact ![11089567]
    · exact ![11697083]
    · exact ![52441, 229]
    · exact ![12649337]
    · exact ![13651919]
    · exact ![13997521]
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
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
  β := ![I197N1, I211N1, I229N1]
  Il := ![[I197N1], [], [I211N1], [], [], [I229N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
