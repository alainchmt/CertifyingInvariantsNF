
import IdealArithmetic.Examples.NF3_1_664563_1.RI3_1_664563_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1959430569354613359268142, 598540563726655774425730, -118009998197042035292997]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-1959430569354613359268142, 598540563726655774425730, -118009998197042035292997]] 
 ![![139, 0, 0], ![0, 139, 0], ![18, 103, 1]] where
  M :=![![![-1959430569354613359268142, 598540563726655774425730, -118009998197042035292997], ![-16639409745782926976312577, 636789390980311417177792, 1795621691179967323277190], ![84394219485458464194027930, -18714362317247402696136919, 636789390980311417177792]]]
  hmulB := by decide  
  f := ![![![244672054977809419477267866173075332742260198366, 13146313541472287714212212997731619317583341497, 8272661396835616493584370116277932383592946916]], ![![1166445256953821925595396186395188466086605515156, 62673504247425856618411723614960820303215366214, 39438940624416863142636638993194857952750024491]], ![![909363947231595830608780941169064218129930235847, 48860437186836316949913842272051085151005164454, 30746707148959739979816576992856359513245618225]]]
  g := ![![![1185247469008225007236, 91752304877856010141039, -118009998197042035292997], ![-352234533719585171189223, -1325987372665872826477502, 1795621691179967323277190], ![524690722646135673991566, -606501220059132940039205, 636789390980311417177792]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [98, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 138], [0, 1]]
 g := ![![[117, 79], [43, 52], [78], [132, 131], [66], [37], [1]], ![[27, 60], [121, 87], [78], [120, 8], [66], [37], [1]]]
 h' := ![![[71, 138], [95, 94], [82, 82], [130, 56], [66, 39], [1, 109], [41, 71], [0, 1]], ![[0, 1], [97, 45], [66, 57], [75, 83], [55, 100], [95, 30], [78, 68], [71, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121]]
 b := ![[], [111, 130]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [98, 68, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![380, -65, -87]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14, 64, -87]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![244672054977809419477267866173075332742260198366, 13146313541472287714212212997731619317583341497, 8272661396835616493584370116277932383592946916]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![244672054977809419477267866173075332742260198366, 13146313541472287714212212997731619317583341497, 8272661396835616493584370116277932383592946916]] 
 ![![139, 0, 0], ![108, 1, 0], ![4, 0, 1]] where
  M :=![![![244672054977809419477267866173075332742260198366, 13146313541472287714212212997731619317583341497, 8272661396835616493584370116277932383592946916], ![1166445256953821925595396186395188466086605515156, 62673504247425856618411723614960820303215366214, 39438940624416863142636638993194857952750024491], ![1853630209347592567703922032680158323779251151077, 99596187738883645485796709514967197042034992118, 62673504247425856618411723614960820303215366214]]]
  hmulB := by decide  
  f := ![![![-1959430569354613359268142, 598540563726655774425730, -118009998197042035292997]], ![![-1642143246302742228613467, 469634318514094496799688, -78773079957558075455874]], ![![550766166964316624150758, -117411511239861723729741, 1185247469008225007236]]]
  g := ![![![-8692233475457123162820062000338498439504406266, 13146313541472287714212212997731619317583341497, 8272661396835616493584370116277932383592946916], ![-41439201181768619005493644028729205456630605280, 62673504247425856618411723614960820303215366214, 39438940624416863142636638993194857952750024491], ![-65852173262169385404573881218677282287578341457, 99596187738883645485796709514967197042034992118, 62673504247425856618411723614960820303215366214]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-1959430569354613359268142, 598540563726655774425730, -118009998197042035292997]] ![![244672054977809419477267866173075332742260198366, 13146313541472287714212212997731619317583341497, 8272661396835616493584370116277932383592946916]]
  ![![139, 0, 0]] where
 M := ![![![139, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1417, -76, -48]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-1417, -76, -48]] 
 ![![149, 0, 0], ![0, 149, 0], ![14, 14, 1]] where
  M :=![![![-1417, -76, -48], ![-6768, -361, -228], ![-10716, -584, -361]]]
  hmulB := by decide  
  f := ![![![19, -4, 0]], ![![0, 19, -12]], ![![-2, 2, -1]]]
  g := ![![![-5, 4, -48], ![-24, 19, -228], ![-38, 30, -361]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [121, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [123, 148], [0, 1]]
 g := ![![[31, 133], [103], [3, 73], [112], [64, 110], [80], [1]], ![[0, 16], [103], [42, 76], [112], [35, 39], [80], [1]]]
 h' := ![![[123, 148], [106, 27], [84, 111], [23, 64], [4, 74], [44, 40], [28, 123], [0, 1]], ![[0, 1], [0, 122], [29, 38], [147, 85], [17, 75], [47, 109], [108, 26], [123, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [138, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [121, 26, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1596, 639, -114]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![0, 15, -114]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, 4, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-19, 4, 0]] 
 ![![149, 0, 0], ![107, 1, 0], ![8, 0, 1]] where
  M :=![![![-19, 4, 0], ![0, -19, 12], ![564, -88, -19]]]
  hmulB := by decide  
  f := ![![![1417, 76, 48]], ![![1063, 57, 36]], ![![148, 8, 5]]]
  g := ![![![-3, 4, 0], ![13, -19, 12], ![68, -88, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-1417, -76, -48]] ![![-19, 4, 0]]
  ![![149, 0, 0]] where
 M := ![![![-149, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [69, 79, 148, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [125, 103, 37], [29, 47, 114], [0, 1]]
 g := ![![[147, 20, 110], [71, 53, 34], [108, 74, 139], [58, 121], [95, 9, 68], [3, 1], []], ![[134, 51, 115, 49], [98, 138, 5, 59], [80, 40, 146, 29], [105, 124], [98, 136, 111, 25], [138, 95], [102, 10]], ![[110, 83, 52, 92], [102, 131, 76, 60], [23, 102, 115, 130], [18, 32], [19, 13, 125, 126], [150, 39], [25, 10]]]
 h' := ![![[125, 103, 37], [84, 36, 67], [98, 1, 51], [144, 17, 21], [89, 144, 11], [95, 147, 81], [0, 0, 1], [0, 1]], ![[29, 47, 114], [73, 74, 102], [109, 12, 18], [37, 17, 106], [51, 118, 107], [89, 83, 35], [131, 90, 47], [125, 103, 37]], ![[0, 1], [35, 41, 133], [41, 138, 82], [42, 117, 24], [128, 40, 33], [100, 72, 35], [22, 61, 103], [29, 47, 114]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 84], []]
 b := ![[], [90, 125, 112], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [69, 79, 148, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![335975, -7550, 7550]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2225, -50, 50]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5288987, 184002, -813914]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![5288987, 184002, -813914]] 
 ![![157, 0, 0], ![0, 157, 0], ![140, 145, 1]] where
  M :=![![![5288987, 184002, -813914], ![-114761874, 23195095, 552006], ![25944282, -42302002, 23195095]]]
  hmulB := by decide  
  f := ![![![-3575562999841, -192116227934, -120894157706]], ![![-17046076236546, -915891530309, -576348683802]], ![![-19104129059972, -1026471415307, -645933966627]]]
  g := ![![![759471, 752876, -813914], ![-1223202, -362075, 552006], ![-20518274, -21691661, 23195095]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [42, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 156], [0, 1]]
 g := ![![[152, 86], [49], [18, 16], [105, 13], [71, 68], [140], [1]], ![[0, 71], [49], [81, 141], [9, 144], [64, 89], [140], [1]]]
 h' := ![![[53, 156], [39, 20], [29, 7], [143, 153], [1, 22], [123, 142], [115, 53], [0, 1]], ![[0, 1], [0, 137], [86, 150], [88, 4], [68, 135], [113, 15], [98, 104], [53, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [71, 101]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [42, 104, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-699, 661, -513]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![453, 478, -513]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3575562999841, 192116227934, 120894157706]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![3575562999841, 192116227934, 120894157706]] 
 ![![157, 0, 0], ![36, 1, 0], ![39, 0, 1]] where
  M :=![![![3575562999841, 192116227934, 120894157706], ![17046076236546, 915891530309, 576348683802], ![27088388138694, 1455468397634, 915891530309]]]
  hmulB := by decide  
  f := ![![![-5288987, -184002, 813914]], ![![-481794, -189931, 183114]], ![![-1479075, 223732, 54443]]]
  g := ![![![-51308874881, 192116227934, 120894157706], ![-244609028808, 915891530309, 576348683802], ![-388714929033, 1455468397634, 915891530309]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![5288987, 184002, -813914]] ![![3575562999841, 192116227934, 120894157706]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [46, 127, 119, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [157, 101, 85], [50, 61, 78], [0, 1]]
 g := ![![[71, 61, 34], [131, 68, 71], [130, 151], [57, 146], [94, 133], [16, 44, 1], []], ![[74, 61, 123, 58], [99, 91, 33, 145], [30, 151], [27, 104], [93, 100], [133, 8, 122, 65], [105, 53]], ![[105, 113, 29, 72], [27, 35, 131, 124], [], [102, 97], [12, 55], [70, 75, 108, 75], [112, 53]]]
 h' := ![![[157, 101, 85], [5, 73, 94], [21, 63, 87], [40, 23, 71], [124, 105, 31], [79, 19, 123], [0, 0, 1], [0, 1]], ![[50, 61, 78], [115, 33, 40], [8, 69, 67], [35, 143, 92], [25, 128, 58], [37, 142, 153], [96, 130, 61], [157, 101, 85]], ![[0, 1], [8, 57, 29], [158, 31, 9], [22, 160], [98, 93, 74], [18, 2, 50], [119, 33, 101], [50, 61, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 92], []]
 b := ![[], [115, 16, 160], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [46, 127, 119, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![35860, 489, -3097]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![220, 3, -19]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀

instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79480975865062934496139797858446474784290, -4270540129313397468352293541444865403401, -2687348994070300721189105401532387538342]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-79480975865062934496139797858446474784290, -4270540129313397468352293541444865403401, -2687348994070300721189105401532387538342]] 
 ![![167, 0, 0], ![57, 1, 0], ![86, 0, 1]] where
  M :=![![![-79480975865062934496139797858446474784290, -4270540129313397468352293541444865403401, -2687348994070300721189105401532387538342], ![-378916208163912401687663861616066642906222, -20359297995516318629979479024733948940766, -12811620387940192405056880624334596210203], ![-602146158233189043037673389343726021879541, -32353519876409389592137495960235175427252, -20359297995516318629979479024733948940766]]]
  hmulB := by decide  
  f := ![![![-839580600142850014600, 329291474382862248982, -96393858274275250431]], ![![-367949869609672222413, 120064061806672776568, -26985482026856901363]], ![![-154334333678452240414, 99066724680312857273, -41968787602972850552]]]
  g := ![![![2365579790394290917498227536141893302437, -4270540129313397468352293541444865403401, -2687348994070300721189105401532387538342], ![11277623538583079682970408242434393537694, -20359297995516318629979479024733948940766, -12811620387940192405056880624334596210203], ![17921581451117063268816760937226338840597, -32353519876409389592137495960235175427252, -20359297995516318629979479024733948940766]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![174911232045783500161162, -25406733676855700082229, -7099758368696951924140]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![174911232045783500161162, -25406733676855700082229, -7099758368696951924140]] 
 ![![167, 0, 0], ![137, 1, 0], ![34, 0, 1]] where
  M :=![![![174911232045783500161162, -25406733676855700082229, -7099758368696951924140], ![-1001065929986270221303740, 331105916157116442492242, -76220201030567100246687], ![-3582349448436653711594289, 225259497562068661374458, 331105916157116442492242]]]
  hmulB := by decide  
  f := ![![![-126800451902468836234056020789013214528511107210, -6813031827690402567962555150077464828944951298, -4287278347541579454199063422285059871007347203]], ![![-107641725494859839922800855033754513965377590679, -5783626878144546347620040006343440592406034710, -3639498377821961634306343438941829921046954615]], ![![-31567981152025671820602544808307615777548597474, -1696158468663108174628183488912140071165776851, -1067352048341124489128411867403796005871851938]]]
  g := ![![![23335482217429405849385, -25406733676855700082229, -7099758368696951924140], ![-262102332984861924756608, 331105916157116442492242, -76220201030567100246687], ![-273655699184323469249289, 225259497562068661374458, 331105916157116442492242]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1054916, -56681, -35668]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![-1054916, -56681, -35668]] 
 ![![167, 0, 0], ![140, 1, 0], ![91, 0, 1]] where
  M :=![![![-1054916, -56681, -35668], ![-5029188, -270220, -170043], ![-7992021, -429414, -270220]]]
  hmulB := by decide  
  f := ![![![-3598, 1268, -323]], ![![-3289, 1084, -248]], ![![-890, 433, -155]]]
  g := ![![![60636, -56681, -35668], ![289075, -270220, -170043], ![459377, -429414, -270220]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-79480975865062934496139797858446474784290, -4270540129313397468352293541444865403401, -2687348994070300721189105401532387538342]] ![![174911232045783500161162, -25406733676855700082229, -7099758368696951924140]]
  ![![3598, -1268, 323]] where
 M := ![![![3598, -1268, 323]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![3598, -1268, 323]] ![![-1054916, -56681, -35668]]
  ![![167, 0, 0]] where
 M := ![![![-167, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28716247511703673, 1542933840800162, 970931446476768]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![28716247511703673, 1542933840800162, 970931446476768]] 
 ![![173, 0, 0], ![0, 173, 0], ![11, 20, 1]] where
  M :=![![![28716247511703673, 1542933840800162, 970931446476768], ![136901333953224288, 7355755689214777, 4628801522400486], ![217553671552822842, 11689233486804532, 7355755689214777]]]
  hmulB := by decide  
  f := ![![![-88258051, 16998374, 953052]], ![![134380332, -109225195, 50995122]], ![![23777681, -13449090, 5324629]]]
  g := ![![![104254344511325, -103327717275926, 970931446476768], ![497020330675254, -492602744270491, 4628801522400486], ![789828664574915, -782808556632896, 7355755689214777]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [52, 133, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 172], [0, 1]]
 g := ![![[119, 10], [158], [81, 31], [38, 92], [13], [155, 43], [1]], ![[0, 163], [158], [110, 142], [85, 81], [13], [145, 130], [1]]]
 h' := ![![[40, 172], [55, 150], [113, 37], [100, 66], [40, 28], [71, 94], [121, 40], [0, 1]], ![[0, 1], [0, 23], [36, 136], [145, 107], [122, 145], [25, 79], [164, 133], [40, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [5, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [52, 133, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5544, 1776, 1196]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-44, -128, 1196]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![88258051, -16998374, -953052]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![88258051, -16998374, -953052]] 
 ![![173, 0, 0], ![113, 1, 0], ![11, 0, 1]] where
  M :=![![![88258051, -16998374, -953052], ![-134380332, 109225195, -50995122], ![-2396770734, 329170784, 109225195]]]
  hmulB := by decide  
  f := ![![![-28716247511703673, -1542933840800162, -970931446476768]], ![![-19548192501593869, -1050331096529671, -660948294648990]], ![![-3083424243824065, -165673443558418, -104254344511325]]]
  g := ![![![11673745, -16998374, -953052], ![-68877925, 109225195, -50995122], ![-235806627, 329170784, 109225195]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![28716247511703673, 1542933840800162, 970931446476768]] ![![88258051, -16998374, -953052]]
  ![![173, 0, 0]] where
 M := ![![![-173, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [18, 114, 138, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [83, 38, 129], [137, 140, 50], [0, 1]]
 g := ![![[65, 104, 158], [22, 80, 138], [135, 17], [64, 125], [137, 145, 19], [135, 41, 1], []], ![[171, 135, 30, 145], [48, 81, 121, 59], [95, 106], [130, 75], [44, 19, 56, 155], [83, 52, 151, 25], [71, 173]], ![[80, 73, 9, 38], [173, 101, 14, 97], [70, 47], [149, 60], [120, 16, 12, 40], [30, 142, 29, 63], [150, 173]]]
 h' := ![![[83, 38, 129], [141, 132, 64], [121, 151, 106], [90, 95, 14], [40, 78, 150], [76, 161, 127], [0, 0, 1], [0, 1]], ![[137, 140, 50], [29, 12, 33], [73, 68, 130], [72, 166, 74], [62, 74, 95], [12, 115, 64], [62, 112, 140], [83, 38, 129]], ![[0, 1], [28, 35, 82], [173, 139, 122], [1, 97, 91], [101, 27, 113], [100, 82, 167], [138, 67, 38], [137, 140, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96, 20], []]
 b := ![[], [128, 3, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [18, 114, 138, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-137293, 24523, 3401]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-767, 137, 19]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def PBC179 : ContainsPrimesAboveP 179 ![I179N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![179, 0, 0]]) timesTableT_eq_Table B_one_repr 179 (by decide) 𝕀

instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59996877069466216, 3223652809618600, 2028567786003515]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![59996877069466216, 3223652809618600, 2028567786003515]] 
 ![![181, 0, 0], ![0, 181, 0], ![157, 81, 1]] where
  M :=![![![59996877069466216, 3223652809618600, 2028567786003515], ![286028057826495615, 15368385777388886, 9670958428855800], ![454535046156222600, 24422324130556005, 15368385777388886]]]
  hmulB := by decide  
  f := ![![![55841116, 1632475, -8398090]], ![![-1184130690, 240599096, 4897425]], ![![-480206363, 106708291, -3763589]]]
  g := ![![![-1428111963166219, -890001866611415, 2028567786003515], ![-6808355886761685, -4242979264971994, 9670958428855800], ![-10819345419302942, -6742634938331181, 15368385777388886]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [140, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [123, 180], [0, 1]]
 g := ![![[3, 65], [121], [20, 75], [27], [109, 116], [137, 106], [1]], ![[34, 116], [121], [14, 106], [27], [78, 65], [143, 75], [1]]]
 h' := ![![[123, 180], [59, 101], [96, 170], [80, 16], [125, 99], [6, 72], [41, 123], [0, 1]], ![[0, 1], [174, 80], [10, 11], [57, 165], [175, 82], [174, 109], [147, 58], [123, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [99, 122]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [140, 58, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![704, 158, 31]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23, -13, 31]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55841116, -1632475, 8398090]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-55841116, -1632475, 8398090]] 
 ![![181, 0, 0], ![119, 1, 0], ![46, 0, 1]] where
  M :=![![![-55841116, -1632475, 8398090], ![1184130690, -240599096, -4897425], ![-230178975, 430624680, -240599096]]]
  hmulB := by decide  
  f := ![![![-59996877069466216, -3223652809618600, -2028567786003515]], ![![-41025726127585499, -2204326354265206, -1387129972172785]], ![![-17759068460506456, -954200847364705, -600455822837296]]]
  g := ![![![-1369551, -1632475, 8398090], ![165970744, -240599096, -4897425], ![-223242859, 430624680, -240599096]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![59996877069466216, 3223652809618600, 2028567786003515]] ![![-55841116, -1632475, 8398090]]
  ![![181, 0, 0]] where
 M := ![![![-181, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1882736, -351990, -27015]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![1882736, -351990, -27015]] 
 ![![191, 0, 0], ![69, 1, 0], ![132, 0, 1]] where
  M :=![![![1882736, -351990, -27015], ![-3809115, 2477066, -1055970], ![-49630590, 6474075, 2477066]]]
  hmulB := by decide  
  f := ![![![12972284946106, 697005325215, 438608818290]], ![![5010112589844, 269195070071, 169398033705]], ![![9479682532677, 509346598080, 320519659466]]]
  g := ![![![155686, -351990, -27015], ![-185019, 2477066, -1055970], ![-4310547, 6474075, 2477066]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N0 : Nat.card (O ⧸ I191N0) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N0)

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := prime_ideal_of_norm_prime hp191.out _ NI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-98018, -4502, 15771]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-98018, -4502, 15771]] 
 ![![191, 0, 0], ![129, 1, 0], ![183, 0, 1]] where
  M :=![![![-98018, -4502, 15771], ![2223711, -444980, -13506], ![-634782, 840281, -444980]]]
  hmulB := by decide  
  f := ![![![-209356035586, -11248771691, -7078583592]], ![![-146623083126, -7878108611, -4957505751]], ![![-208891263459, -11223799325, -7062869078]]]
  g := ![![![-12583, -4502, 15771], ![325119, -444980, -13506], ![-144501, 840281, -444980]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21503459152538702471846, -1155388245180490613416, -727058251281587057997]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![-21503459152538702471846, -1155388245180490613416, -727058251281587057997]] 
 ![![191, 0, 0], ![184, 1, 0], ![111, 0, 1]] where
  M :=![![![-21503459152538702471846, -1155388245180490613416, -727058251281587057997], ![-102515213430703775177577, -5508177624343787195912, -3466164735541471840248], ![-162909742570449176491656, -8753196416263798230707, -5508177624343787195912]]]
  hmulB := by decide  
  f := ![![![-950117416408, 125452241513, 46467741096]], ![![-880992948296, 110527773392, 46735188933]], ![![-459551137005, 69891273959, 16678070896]]]
  g := ![![![1422991852633129496515, -1155388245180490613416, -727058251281587057997], ![6783946361746892372449, -5508177624343787195912, -3466164735541471840248], ![10780555572378272652904, -8753196416263798230707, -5508177624343787195912]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![1882736, -351990, -27015]] ![![-98018, -4502, 15771]]
  ![![-950117416408, 125452241513, 46467741096]] where
 M := ![![![-950117416408, 125452241513, 46467741096]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![-950117416408, 125452241513, 46467741096]] ![![-21503459152538702471846, -1155388245180490613416, -727058251281587057997]]
  ![![191, 0, 0]] where
 M := ![![![191, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0]] 
 ![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [111, 58, 82, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [169, 147, 94], [135, 45, 99], [0, 1]]
 g := ![![[188, 142, 185], [81, 134], [142, 59], [61, 25], [114, 177], [88, 162], [1]], ![[19, 153, 62, 148], [103, 126], [134, 9], [161, 67], [79, 170], [144, 23], [91, 91, 81, 105]], ![[3, 10, 57, 183], [182, 184], [116, 69], [93, 56], [83, 165], [11, 56], [155, 95, 45, 88]]]
 h' := ![![[169, 147, 94], [76, 158, 68], [162, 74, 110], [171, 79, 161], [90, 117, 188], [44, 19, 131], [82, 135, 111], [0, 1]], ![[135, 45, 99], [179, 157, 156], [15, 98, 133], [75, 81, 3], [24, 126, 158], [84, 184, 154], [7, 89, 122], [169, 147, 94]], ![[0, 1], [181, 71, 162], [73, 21, 143], [37, 33, 29], [175, 143, 40], [33, 183, 101], [176, 162, 153], [135, 45, 99]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 180], []]
 b := ![[], [38, 90, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [111, 58, 82, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-493501, 165980, -33196]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2557, 860, -172]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def PBC193 : ContainsPrimesAboveP 193 ![I193N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![193, 0, 0]]) timesTableT_eq_Table B_one_repr 193 (by decide) 𝕀



lemma PB231I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB231I3 : PrimesBelowBoundCertificateInterval O 137 193 231 where
  m := 11
  g := ![2, 2, 1, 2, 1, 3, 2, 1, 2, 3, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB231I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1, I191N2]
    · exact ![I193N0]
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
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![4330747]
    · exact ![167, 167, 167]
    · exact ![29929, 173]
    · exact ![5735339]
    · exact ![32761, 181]
    · exact ![191, 191, 191]
    · exact ![7189057]
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
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I139N1, I149N1, I157N1, I167N0, I167N1, I167N2, I173N1, I181N1, I191N0, I191N1, I191N2]
  Il := ![[I139N1], [I149N1], [], [I157N1], [], [I167N0, I167N1, I167N2], [I173N1], [], [I181N1], [I191N0, I191N1, I191N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
