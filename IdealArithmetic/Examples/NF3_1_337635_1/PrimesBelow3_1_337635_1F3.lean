
import IdealArithmetic.Examples.NF3_1_337635_1.RI3_1_337635_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17759056252489793723776387, -5701289704469114531384345, -836747443632883617888089]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-17759056252489793723776387, -5701289704469114531384345, -836747443632883617888089]] 
 ![![139, 0, 0], ![0, 139, 0], ![33, 53, 1]] where
  M :=![![![-17759056252489793723776387, -5701289704469114531384345, -836747443632883617888089], ![-224248314893612809594007852, -71991697687666158092669894, -10565831965305345444880601], ![-1303697325904109884816996608, -418533284440661422698541355, -61425865722360812647789293]]]
  hmulB := by decide  
  f := ![![![28876314525967, 2231836189910, -777252187761]], ![![-208303586319948, -13972476174261, 5240924567581]], ![![-66767884966795, -4453637580352, 1675584742042]]]
  g := ![![![70889276168311983212450, 278031113727149044724348, -836747443632883617888089], ![895137697564486259619079, 3510772636500123384791381, -10565831965305345444880601], ![5204001747725157788201799, 20410342437729939911038066, -61425865722360812647789293]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [33, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 138], [0, 1]]
 g := ![![[26, 54], [104, 1], [25], [57, 125], [64], [20], [1]], ![[120, 85], [80, 138], [25], [115, 14], [64], [20], [1]]]
 h' := ![![[115, 138], [43, 38], [64, 1], [65, 134], [117, 79], [12, 131], [106, 115], [0, 1]], ![[0, 1], [104, 101], [40, 138], [46, 5], [28, 60], [65, 8], [126, 24], [115, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [30, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [33, 24, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![837, 1597, 455]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-102, -162, 455]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28876314525967, -2231836189910, 777252187761]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-28876314525967, -2231836189910, 777252187761]] 
 ![![139, 0, 0], ![34, 1, 0], ![100, 0, 1]] where
  M :=![![![-28876314525967, -2231836189910, 777252187761], ![208303586319948, 13972476174261, -5240924567581], ![-806435685215828, -47835019299875, 19213400741842]]]
  hmulB := by decide  
  f := ![![![17759056252489793723776387, 5701289704469114531384345, 836747443632883617888089]], ![![5957239046606228749657590, 1912485954241842101868616, 280685216178585528439393]], ![![22155416914770426310752772, 7112678092716351624726445, 1043889281191720679399987]]]
  g := ![![![-221000739893, -2231836189910, 777252187761], ![1851308296066, 13972476174261, -5240924567581], ![-7923633836002, -47835019299875, 19213400741842]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-17759056252489793723776387, -5701289704469114531384345, -836747443632883617888089]] ![![-28876314525967, -2231836189910, 777252187761]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4493713189577, 246106738435, -103546370781]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![4493713189577, 246106738435, -103546370781]] 
 ![![149, 0, 0], ![54, 1, 0], ![5, 0, 1]] where
  M :=![![![4493713189577, 246106738435, -103546370781], ![-27750427369308, -1265869577286, 595759847651], ![93707033269888, 3401821897225, -1861629424937]]]
  hmulB := by decide  
  f := ![![![-329911157981577677512507, -105913234444885000370870, -15544312385876214485819]], ![![-147524015103490067569630, -47360464233765591530791, -6950839096249727305303]], ![![-173613603367263375870847, -55736151480166158015945, -8180093397535371840497]]]
  g := ![![![-55559186792, 246106738435, -103546370781], ![252535104469, -1265869577286, 595759847651], ![-541498000373, 3401821897225, -1861629424937]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-624257152682833476656379, -200408784505813254901957, -29412913009027241560857]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-624257152682833476656379, -200408784505813254901957, -29412913009027241560857]] 
 ![![149, 0, 0], ![118, 1, 0], ![131, 0, 1]] where
  M :=![![![-624257152682833476656379, -200408784505813254901957, -29412913009027241560857], ![-7882660686419300738309676, -2530614891712226742088042, -371404656002599268243057], ![-45826893561138651575414800, -14712065367285029148203491, -2159210235709627473844985]]]
  hmulB := by decide  
  f := ![![![19678353742617, -1414305216142, -24785990555]], ![![15539618095034, -1007124526379, -38446787431]], ![![14801833475339, -1811451106437, 109955172841]]]
  g := ![![![180383027001246303666086, -200408784505813254901957, -29412913009027241560857], ![2277744338738013147435703, -2530614891712226742088042, -371404656002599268243057], ![13241968863466147563666377, -14712065367285029148203491, -2159210235709627473844985]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, -3, 1]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![-35, -3, 1]] 
 ![![149, 0, 0], ![126, 1, 0], ![45, 0, 1]] where
  M :=![![![-35, -3, 1], ![268, 20, -7], ![-1072, -69, 27]]]
  hmulB := by decide  
  f := ![![![57, 12, 1]], ![![50, 11, 1]], ![![37, 9, 1]]]
  g := ![![![2, -3, 1], ![-13, 20, -7], ![43, -69, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![4493713189577, 246106738435, -103546370781]] ![![-624257152682833476656379, -200408784505813254901957, -29412913009027241560857]]
  ![![57, 12, 1]] where
 M := ![![![57, 12, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![57, 12, 1]] ![![-35, -3, 1]]
  ![![149, 0, 0]] where
 M := ![![![149, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [57, 146, 139, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 122, 59], [102, 28, 92], [0, 1]]
 g := ![![[89, 83, 47], [125, 44, 94], [52, 57, 81], [80, 148], [26, 36, 4], [12, 1], []], ![[27, 121, 26, 125], [81, 138, 34, 139], [32, 70, 42, 38], [8, 116], [43, 67, 80, 99], [101, 29], [147, 8]], ![[1, 117, 73, 135], [137, 132, 91, 149], [82, 95, 43, 35], [138, 145], [10, 15, 33, 135], [5, 86], [114, 8]]]
 h' := ![![[61, 122, 59], [123, 45, 97], [56, 32, 68], [150, 75, 9], [28, 99, 86], [71, 3, 149], [0, 0, 1], [0, 1]], ![[102, 28, 92], [116, 125, 86], [99, 34, 17], [100, 53, 147], [42, 131, 95], [57, 89, 121], [23, 63, 28], [61, 122, 59]], ![[0, 1], [55, 132, 119], [148, 85, 66], [70, 23, 146], [101, 72, 121], [115, 59, 32], [131, 88, 122], [102, 28, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 121], []]
 b := ![[], [17, 140, 108], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [57, 146, 139, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1253753, 1237596, 334616]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8303, 8196, 2216]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def PBC151 : ContainsPrimesAboveP 151 ![I151N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![151, 0, 0]]) timesTableT_eq_Table B_one_repr 151 (by decide) 𝕀

instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2039684998329996490141, -654811546064479996121, -96103147819563330689]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-2039684998329996490141, -654811546064479996121, -96103147819563330689]] 
 ![![157, 0, 0], ![0, 157, 0], ![94, 37, 1]] where
  M :=![![![-2039684998329996490141, -654811546064479996121, -96103147819563330689], ![-25755643615642972624652, -8268479117929149666224, -1213519944309396661553], ![-149733850729637666335776, -48069900192793989497363, -7054959173619753004671]]]
  hmulB := by decide  
  f := ![![![-319261566545, -23828583388, 8447745939]], ![![2263995911652, 146879114529, -56104912715]], ![![287307039594, 17194878256, -6871398885]]]
  g := ![![![44547840106426475125, 18477738364709319996, -96103147819563330689], ![562517395856307729690, 233323304595659406441, -1213519944309396661553], ![3270269500577191822314, 1356455982363929118952, -7054959173619753004671]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [146, 129, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 156], [0, 1]]
 g := ![![[131, 57], [113], [22, 49], [136, 33], [47, 30], [156], [1]], ![[0, 100], [113], [138, 108], [118, 124], [102, 127], [156], [1]]]
 h' := ![![[28, 156], [147, 34], [85, 37], [83, 7], [46, 87], [110, 117], [11, 28], [0, 1]], ![[0, 1], [0, 123], [22, 120], [122, 150], [127, 70], [89, 40], [10, 129], [28, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135]]
 b := ![[], [154, 146]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [146, 129, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4282, 105, 58]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-62, -13, 58]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![319261566545, 23828583388, -8447745939]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![319261566545, 23828583388, -8447745939]] 
 ![![157, 0, 0], ![84, 1, 0], ![41, 0, 1]] where
  M :=![![![319261566545, 23828583388, -8447745939], ![-2263995911652, -146879114529, 56104912715], ![8650056259636, 495044512909, -202984027244]]]
  hmulB := by decide  
  f := ![![![2039684998329996490141, 654811546064479996121, 96103147819563330689]], ![![1255345117677469285328, 403010503104111269684, 59147671090144690697]], ![![1486375386376863200201, 477179449563297256932, 70033046077846175560]]]
  g := ![![![-8509438564, 23828583388, -8447745939], ![49513046417, -146879114529, 56104912715], ![-156760112788, 495044512909, -202984027244]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-2039684998329996490141, -654811546064479996121, -96103147819563330689]] ![![319261566545, 23828583388, -8447745939]]
  ![![157, 0, 0]] where
 M := ![![![-157, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4426635449316179, -191775742062938, 93287186014910]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-4426635449316179, -191775742062938, 93287186014910]] 
 ![![163, 0, 0], ![0, 163, 0], ![105, 1, 1]] where
  M :=![![![-4426635449316179, -191775742062938, 93287186014910], ![25000965851995880, 792245597485663, -476838670140786], ![-76396864724863264, -1327838508084854, 1269084267626449]]]
  hmulB := by decide  
  f := ![![![-2283813960174625969079158561, -733185639650246076071424994, -107605689499479713875481926]], ![![-28838324785860563318629156168, -9258129590794695449928535263, -1358765589801012438267368062]], ![![-2676651639537433589818733419, -859300529148651385315928905, -126114889498405309244503911]]]
  g := ![![![-87250245281483, -1748852319496, 93287186014910], ![460546173109070, 7785793052923, -476838670140786], ![-1286200692181843, -15932041568781, 1269084267626449]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [51, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 162], [0, 1]]
 g := ![![[5, 16], [143, 87], [145], [136], [126], [56, 151], [1]], ![[0, 147], [126, 76], [145], [136], [126], [19, 12], [1]]]
 h' := ![![[71, 162], [42, 4], [112, 24], [3, 54], [147, 25], [78, 17], [112, 71], [0, 1]], ![[0, 1], [0, 159], [23, 139], [88, 109], [129, 138], [144, 146], [100, 92], [71, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [160]]
 b := ![[], [94, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [51, 92, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1196, 3601, 993]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-647, 16, 993]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2283813960174625969079158561, -733185639650246076071424994, -107605689499479713875481926]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-2283813960174625969079158561, -733185639650246076071424994, -107605689499479713875481926]] 
 ![![163, 0, 0], ![162, 1, 0], ![0, 0, 1]] where
  M :=![![![-2283813960174625969079158561, -733185639650246076071424994, -107605689499479713875481926], ![-28838324785860563318629156168, -9258129590794695449928535263, -1358765589801012438267368062], ![-167655426640405385068512742224, -53823364497159642369068251882, -7899364000993683011661167201]]]
  hmulB := by decide  
  f := ![![![-4426635449316179, -191775742062938, 93287186014910]], ![![-4246098018019786, -185738801329511, 89789481375918]], ![![-468692421624928, -8146248515858, 7785793052923]]]
  g := ![![![714676439651320480702403009, -733185639650246076071424994, -107605689499479713875481926], ![9024409011796810426808549426, -9258129590794695449928535263, -1358765589801012438267368062], ![52464598907358629930800883820, -53823364497159642369068251882, -7899364000993683011661167201]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-4426635449316179, -191775742062938, 93287186014910]] ![![-2283813960174625969079158561, -733185639650246076071424994, -107605689499479713875481926]]
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


lemma PB165I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 164 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 164 (by omega)

def PB165I3 : PrimesBelowBoundCertificateInterval O 137 164 165 where
  m := 5
  g := ![2, 3, 1, 2, 2]
  P := ![139, 149, 151, 157, 163]
  hP := PB165I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
    · exact PBC163
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![149, 149, 149]
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![26569, 163]
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
      exact NI149N1
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
  β := ![I139N1, I149N0, I149N1, I149N2, I157N1, I163N1]
  Il := ![[I139N1], [I149N0, I149N1, I149N2], [], [I157N1], [I163N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
