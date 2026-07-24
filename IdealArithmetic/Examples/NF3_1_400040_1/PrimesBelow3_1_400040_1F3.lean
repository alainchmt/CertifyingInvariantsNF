
import IdealArithmetic.Examples.NF3_1_400040_1.RI3_1_400040_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-225791, -25720, -24430]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-225791, -25720, -24430]] 
 ![![139, 0, 0], ![0, 139, 0], ![27, 53, 1]] where
  M :=![![![-225791, -25720, -24430], ![-2828720, -322221, -306060], ![-3917020, -446190, -423811]]]
  hmulB := by decide  
  f := ![![![771, -20, -30]], ![![-3520, 641, -260]], ![![-1217, 237, -101]]]
  g := ![![![3121, 9130, -24430], ![39100, 114381, -306060], ![54143, 158387, -423811]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [99, 128, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 138], [0, 1]]
 g := ![![[108, 66], [43, 34], [44], [34, 51], [30], [121], [1]], ![[0, 73], [0, 105], [44], [39, 88], [30], [121], [1]]]
 h' := ![![[11, 138], [52, 109], [19, 112], [109, 34], [119, 107], [46, 126], [40, 11], [0, 1]], ![[0, 1], [0, 30], [0, 27], [66, 105], [45, 32], [42, 13], [22, 128], [11, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [50, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [99, 128, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4949, 2914, -800]
  a := ![6, 1, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![191, 326, -800]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-771, 20, 30]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-771, 20, 30]] 
 ![![139, 0, 0], ![24, 1, 0], ![0, 0, 1]] where
  M :=![![![-771, 20, 30], ![3520, -641, 260], ![3420, 490, -551]]]
  hmulB := by decide  
  f := ![![![225791, 25720, 24430]], ![![59336, 6759, 6420]], ![![28180, 3210, 3049]]]
  g := ![![![-9, 20, 30], ![136, -641, 260], ![-60, 490, -551]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-225791, -25720, -24430]] ![![-771, 20, 30]]
  ![![139, 0, 0]] where
 M := ![![![-139, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [35, 46, 135, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 73, 6], [111, 75, 143], [0, 1]]
 g := ![![[139, 95, 88], [90, 129], [113, 63, 127], [95, 142], [10, 146, 1], [14, 1], []], ![[143, 114, 71, 110], [49, 143], [111, 20, 100, 53], [148, 73], [138, 78, 1, 29], [146, 112], [39, 36]], ![[32, 39, 25, 132], [13, 88], [19, 124, 30, 116], [57, 25], [134, 141, 116, 124], [12, 114], [51, 36]]]
 h' := ![![[52, 73, 6], [133, 42, 45], [68, 76, 24], [124, 78, 53], [97, 4, 80], [106, 66, 1], [0, 0, 1], [0, 1]], ![[111, 75, 143], [141, 17, 51], [98, 28, 21], [51, 60, 122], [145, 70, 64], [109, 118, 24], [147, 68, 75], [52, 73, 6]], ![[0, 1], [29, 90, 53], [22, 45, 104], [96, 11, 123], [81, 75, 5], [88, 114, 124], [106, 81, 73], [111, 75, 143]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 9], []]
 b := ![[], [140, 2, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [35, 46, 135, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6724221, 1000237, 282653]
  a := ![-7, -3, 17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![45129, 6713, 1897]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀

instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2085331722941, -11916015271, -111600747323]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![2085331722941, -11916015271, -111600747323]] 
 ![![151, 0, 0], ![0, 1, 0], ![60, 0, 1]] where
  M :=![![![2085331722941, -11916015271, -111600747323], ![-13344425617676, 1539244001597, -342361647356], ![-5224347241502, -1510389791554, 1391895208461]]]
  hmulB := by decide  
  f := ![![![1625366813289087236680993, 185146474046109597917873, 175860367508769018248307]], ![![134852041091840025153148, 15361074018455779668905, 14590632287937973613744]], ![![832575087272692268685078, 94839109871596828489336, 90082410708344779052351]]]
  g := ![![![58154811671, -11916015271, -111600747323], ![47664061084, 1539244001597, -342361647356], ![-587669269862, -1510389791554, 1391895208461]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6144635, 2612282, -1532290]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-6144635, 2612282, -1532290]] 
 ![![151, 0, 0], ![46, 1, 0], ![4, 0, 1]] where
  M :=![![![-6144635, 2612282, -1532290], ![-194323928, -16418367, 23058240], ![261375980, -6858360, -10113811]]]
  hmulB := by decide  
  f := ![![![-324193971653037, -36929122871102, -35076925733250]], ![![-125658525116194, -14313835294827, -13595918304020]], ![![-45833682821688, -5220941326968, -4959082614091]]]
  g := ![![![-795897, 2612282, -1532290], ![3103894, -16418367, 23058240], ![4088184, -6858360, -10113811]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15019651122699260589681161184979499687, -1710897148898450534378283739925352961, -1625086315713765863435260077400388647]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![-15019651122699260589681161184979499687, -1710897148898450534378283739925352961, -1625086315713765863435260077400388647]] 
 ![![151, 0, 0], ![104, 1, 0], ![76, 0, 1]] where
  M :=![![![-15019651122699260589681161184979499687, -1710897148898450534378283739925352961, -1625086315713765863435260077400388647], ![-188166769290058101474718074328345225796, -21434185552369639372479177832056089961, -20359144120412037070653357554054306904], ![-260560592602082103482192891422655569318, -29680607848771208896549799705831817216, -28191963314778756839049289129232537491]]]
  hmulB := by decide  
  f := ![![![-39667790098106368587, 6408514137174814099, -2341386419824069977]], ![![-29351328457818874084, 4031140622064762475, -1219217345229160772]], ![![-15399586021649832450, 3236103454658589618, -1449300981783645553]]]
  g := ![![![1896822598390634441104239163242958579, -1710897148898450534378283739925352961, -1625086315713765863435260077400388647], ![23763466763627147090283255591480897052, -21434185552369639372479177832056089961, -20359144120412037070653357554054306904], ![32906038646313305573024716899374346162, -29680607848771208896549799705831817216, -28191963314778756839049289129232537491]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![2085331722941, -11916015271, -111600747323]] ![![-6144635, 2612282, -1532290]]
  ![![-39667790098106368587, 6408514137174814099, -2341386419824069977]] where
 M := ![![![-39667790098106368587, 6408514137174814099, -2341386419824069977]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![-39667790098106368587, 6408514137174814099, -2341386419824069977]] ![![-15019651122699260589681161184979499687, -1710897148898450534378283739925352961, -1625086315713765863435260077400388647]]
  ![![151, 0, 0]] where
 M := ![![![151, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![354967, 29512, -41774]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![354967, 29512, -41774]] 
 ![![157, 0, 0], ![26, 1, 0], ![123, 0, 1]] where
  M :=![![![354967, 29512, -41774], ![-5130928, 116585, 211572], ![2121124, -395502, 163347]]]
  hmulB := by decide  
  f := ![![![102720959139, 11701003884, 11114134654]], ![![25207879494, 2871444137, 2727425536]], ![![91825981009, 10459950622, 9935326989]]]
  g := ![![![30101, 29512, -41774], ![-217742, 116585, 211572], ![-48965, -395502, 163347]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5083124381362337947, -858729939548537994, 327131907188736348]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![5083124381362337947, -858729939548537994, 327131907188736348]] 
 ![![157, 0, 0], ![131, 1, 0], ![55, 0, 1]] where
  M :=![![![5083124381362337947, -858729939548537994, 327131907188736348], ![42690748620842513736, 7577513856854557681, -7933035581107907244], ![-91925107901407523448, -40934904289117446, 5328455945397680047]]]
  hmulB := by decide  
  f := ![![![40051710709655157559495846746954112183, 4562313538567710279109436993334078510, 4333488605259285395960182202294539548]], ![![36614926633386427048998344204796160049, 4170827476113082298239003610776159339, 3961637706274917582508271355659328312]], ![![18456435198967991100178663727137451821, 2102383211353078515248717122483272132, 1996937214698133676887170924035599883]]]
  g := ![![![634296124629556153, -858729939548537994, 327131907188736348], ![-3271634456472418115, 7577513856854557681, -7933035581107907244], ![-2418010907238251851, -40934904289117446, 5328455945397680047]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3088714475777667969, 63920818878441712, -224205768182905266]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![3088714475777667969, 63920818878441712, -224205768182905266]] 
 ![![157, 0, 0], ![156, 1, 0], ![125, 0, 1]] where
  M :=![![![3088714475777667969, 63920818878441712, -224205768182905266], ![-27160375457462398768, 1903764815984699927, 190796652418606588], ![47502147194226396, -2595070891985559898, 1871321504437119797]]]
  hmulB := by decide  
  f := ![![![-4057686878522757430877357865367562843, -462213459878261440580174708476850404, -439030931269299682971320223895314238]], ![![-4355630643072312582236341114846306436, -496152406471336172838605342667235329, -471267654390649454237390716307185692]], ![![-3679003354547084337263156597456102471, -419077400577547026458916401354328902, -398058380857054387141915010271384897]]]
  g := ![![![134667437921044071, 63920818878441712, -224205768182905266], ![-2216543110212747840, 1903764815984699927, 190796652418606588], ![1088938683071984687, -2595070891985559898, 1871321504437119797]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![354967, 29512, -41774]] ![![5083124381362337947, -858729939548537994, 327131907188736348]]
  ![![6904310243050747163926333, -79483186816460587645322, -340589633033635069627790]] where
 M := ![![![6904310243050747163926333, -79483186816460587645322, -340589633033635069627790]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![6904310243050747163926333, -79483186816460587645322, -340589633033635069627790]] ![![3088714475777667969, 63920818878441712, -224205768182905266]]
  ![![157, 0, 0]] where
 M := ![![![23468057450580375598833179766965038650346133, 1173866112800729943565024756113308537476022, -2200504012268626068997919855902003168709544]]]
 hmul := by decide  
 g := ![![![![149478072933632965597663565394681774842969, 7476854221660700277484234115371391958446, -14015949122730102350305222012114669864392]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1841592878727821551163507906391, 209776910256280128539961465105, 199255452865583015788461160153]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![1841592878727821551163507906391, 209776910256280128539961465105, 199255452865583015788461160153]] 
 ![![163, 0, 0], ![0, 163, 0], ![48, 93, 1]] where
  M :=![![![1841592878727821551163507906391, 209776910256280128539961465105, 199255452865583015788461160153], ![23071546702844841380455493357940, 2628093232799456501565852242051, 2496280008293967316976536971356], ![31947914628183437961603055257802, 3639205438533979847949802407514, 3456679416433879902974197797519]]]
  hmulB := by decide  
  f := ![![![899214192749095, 167197408285369, -172577438366021]], ![![-21378082237063996, -130870407366379, 1326819206121648]], ![![-11845419084080954, -34067435243601, 707414806790601]]]
  g := ![![![-47378336557178915378421029331, -112398651572042578771698935148, 199255452865583015788461160153], ![-593557630032304232112995590596, -1408134647475702478388049607939, 2496280008293967316976536971356], ![-821918388715599983933487355970, -1949889449630778227783132470931, 3456679416433879902974197797519]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [136, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [141, 162], [0, 1]]
 g := ![![[132, 6], [86, 88], [9], [58], [40], [63, 158], [1]], ![[0, 157], [106, 75], [9], [58], [40], [10, 5], [1]]]
 h' := ![![[141, 162], [40, 150], [36, 96], [49, 3], [90, 104], [71, 23], [27, 141], [0, 1]], ![[0, 1], [0, 13], [43, 67], [146, 160], [84, 59], [54, 140], [22, 22], [141, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87]]
 b := ![[], [71, 125]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [136, 22, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1278166, 502700, 201738]
  a := ![66, 1, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-51566, -112018, 201738]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![899214192749095, 167197408285369, -172577438366021]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![899214192749095, 167197408285369, -172577438366021]] 
 ![![163, 0, 0], ![46, 1, 0], ![86, 0, 1]] where
  M :=![![![899214192749095, 167197408285369, -172577438366021], ![-21378082237063996, -130870407366379, 1326819206121648], ![14196056089799566, -1407519657331428, 198144379123707]]]
  hmulB := by decide  
  f := ![![![1841592878727821551163507906391, 209776910256280128539961465105, 199255452865583015788461160153]], ![![661256559044936397140962313202, 75324117206063450395117052987, 71546201473072307013777609438]], ![![1167637436802307308967268314156, 133006255954442152775377229488, 126335266029901958655103420679]]]
  g := ![![![49385233810429, 167197408285369, -172577438366021], ![-794260706899830, -130870407366379, 1326819206121648], ![379764071916604, -1407519657331428, 198144379123707]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![1841592878727821551163507906391, 209776910256280128539961465105, 199255452865583015788461160153]] ![![899214192749095, 167197408285369, -172577438366021]]
  ![![163, 0, 0]] where
 M := ![![![163, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-341154920909957783761, -34813188524759962435, 44806135063096797205]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-341154920909957783761, -34813188524759962435, 44806135063096797205]] 
 ![![167, 0, 0], ![0, 167, 0], ![13, 68, 1]] where
  M :=![![![-341154920909957783761, -34813188524759962435, 44806135063096797205], ![5515988961670655514340, -82311057069713835301, -258519615121406029940], ![-2654174030825904387230, 408413813196458551490, -141944487580896925401]]]
  hmulB := by decide  
  f := ![![![702195105483932798170043337619320772403, 79987450715632892715744348577945049545, 75975643346238090155543844335729655315]], ![![8797127398686039247802283925975778439620, 1002085871499490356232018210720023999433, 951825793848805107468531174450909806080]], ![![3709669852943651721065531035282468971027, 422570639151783421944207823830713343547, 401376414444386045535431047543808030754]]]
  g := ![![![-5530746567246803278, -18452876483924204625, 44806135063096797205], ![53154155438616370680, 104772591444226923357, -258519615121406029940], ![-4843686780085295551, 60243347117948799274, -141944487580896925401]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [134, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [141, 166], [0, 1]]
 g := ![![[65, 24], [114, 77], [83, 124], [76], [141], [80, 8], [1]], ![[109, 143], [116, 90], [32, 43], [76], [141], [39, 159], [1]]]
 h' := ![![[141, 166], [88, 58], [67, 113], [4, 142], [166, 110], [135, 108], [33, 141], [0, 1]], ![[0, 1], [83, 109], [135, 54], [153, 25], [145, 57], [166, 59], [41, 26], [141, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [69, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [134, 26, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1029, 5755, 1762]
  a := ![9, 3, -22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-131, -683, 1762]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-702195105483932798170043337619320772403, -79987450715632892715744348577945049545, -75975643346238090155543844335729655315]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-702195105483932798170043337619320772403, -79987450715632892715744348577945049545, -75975643346238090155543844335729655315]] 
 ![![167, 0, 0], ![153, 1, 0], ![12, 0, 1]] where
  M :=![![![-702195105483932798170043337619320772403, -79987450715632892715744348577945049545, -75975643346238090155543844335729655315], ![-8797127398686039247802283925975778439620, -1002085871499490356232018210720023999433, -951825793848805107468531174450909806080], ![-12181665959648042191177812536768214226110, -1387620617079259635600791719254210766820, -1318023866992627124534795100789588803383]]]
  hmulB := by decide  
  f := ![![![341154920909957783761, 34813188524759962435, -44806135063096797205]], ![![279525233158999313779, 32387598211724479568, -39501910476241939775]], ![![40407383723026334086, 55954785033898190, -2369635528001584677]]]
  g := ![![![74536482480016508198834539681646872286, -79987450715632892715744348577945049545, -75975643346238090155543844335729655315], ![933795930939650578115681894656280306267, -1002085871499490356232018210720023999433, -951825793848805107468531174450909806080], ![1293057334475390464372220728853898794838, -1387620617079259635600791719254210766820, -1318023866992627124534795100789588803383]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-341154920909957783761, -34813188524759962435, 44806135063096797205]] ![![-702195105483932798170043337619320772403, -79987450715632892715744348577945049545, -75975643346238090155543844335729655315]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [126, 96, 146, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 45, 130], [165, 127, 43], [0, 1]]
 g := ![![[67, 135, 1], [113, 169], [157, 172, 16], [87, 53, 10], [120, 23], [114, 27, 1], []], ![[10, 14, 111, 37], [59, 144], [110, 47, 55, 34], [117, 134, 58, 144], [171, 64], [0, 38, 53, 10], [35, 119]], ![[147, 27, 61, 152], [118, 1], [134, 90, 67, 130], [96, 10, 112, 43], [146, 138], [132, 102, 156, 56], [122, 119]]]
 h' := ![![[35, 45, 130], [88, 54, 1], [113, 95, 13], [110, 54, 4], [129, 157, 23], [168, 13, 14], [0, 0, 1], [0, 1]], ![[165, 127, 43], [4, 28, 54], [93, 37, 161], [159, 88, 89], [12, 86, 149], [148, 0, 8], [102, 20, 127], [35, 45, 130]], ![[0, 1], [91, 91, 118], [164, 41, 172], [34, 31, 80], [55, 103, 1], [99, 160, 151], [89, 153, 45], [165, 127, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118, 3], []]
 b := ![[], [114, 61, 161], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [126, 96, 146, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4841578, 3114, -46710]
  a := ![6, 1, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-27986, 18, -270]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def PBC173 : ContainsPrimesAboveP 173 ![I173N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![173, 0, 0]]) timesTableT_eq_Table B_one_repr 173 (by decide) 𝕀



lemma PB179I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 178 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 178 (by omega)

def PB179I3 : PrimesBelowBoundCertificateInterval O 137 178 179 where
  m := 7
  g := ![2, 1, 3, 3, 2, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173]
  hP := PB179I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
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
    · exact ![19321, 139]
    · exact ![3307949]
    · exact ![151, 151, 151]
    · exact ![157, 157, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![5177717]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
  β := ![I139N1, I151N0, I151N1, I151N2, I157N0, I157N1, I157N2, I163N1, I167N1]
  Il := ![[I139N1], [], [I151N0, I151N1, I151N2], [I157N0, I157N1, I157N2], [I163N1], [I167N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
