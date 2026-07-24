
import IdealArithmetic.Examples.NF3_1_720575_1.RI3_1_720575_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [63, 27, 116, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 99, 116], [98, 39, 23], [0, 1]]
 g := ![![[74, 96, 113], [35, 16, 42], [136, 120], [1, 83, 96], [133, 136], [23, 1], []], ![[21, 135, 51, 4], [6, 85, 78, 47], [33, 89], [65, 27, 11, 30], [6, 16], [130, 131], [107, 112]], ![[23, 51, 98, 126], [110, 13, 109, 21], [95, 4], [121, 18, 84, 128], [43, 137], [34, 71], [61, 112]]]
 h' := ![![[64, 99, 116], [19, 137, 35], [127, 66, 96], [76, 3, 26], [106, 26, 42], [80, 11, 85], [0, 0, 1], [0, 1]], ![[98, 39, 23], [29, 32, 21], [75, 56, 2], [25, 31, 111], [73, 70, 67], [27, 59, 4], [135, 86, 39], [64, 99, 116]], ![[0, 1], [47, 109, 83], [37, 17, 41], [36, 105, 2], [115, 43, 30], [34, 69, 50], [62, 53, 99], [98, 39, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 53], []]
 b := ![[], [118, 20, 99], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [63, 27, 116, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-432985, 11120, 16680]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3115, 80, 120]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-10, -21, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-10, -21, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![139, 128, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-10, -21, 1], ![-176, -12, -42], ![3784, -487, 9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-139, -128, 149]], ![![-1, -1, 1], ![38, 36, -42], ![17, -11, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [13, 141, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 148], [0, 1]]
 g := ![![[114, 73], [49], [121, 24], [125], [80, 36], [64], [1]], ![[102, 76], [49], [15, 125], [125], [70, 113], [64], [1]]]
 h' := ![![[8, 148], [143, 64], [66, 142], [23, 60], [3, 42], [82, 6], [136, 8], [0, 1]], ![[0, 1], [59, 85], [10, 7], [56, 89], [41, 107], [130, 143], [51, 141], [8, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [100, 124]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [13, 141, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-127, -1116, 862]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-805, -748, 862]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![42, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![42, 1, 0]] 
 ![![149, 0, 0], ![42, 1, 0], ![140, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![42, 1, 0], ![0, 43, 2], ![-176, 19, 42]]]
  hmulB := by decide  
  f := ![![![3697, 88, 0], ![-13112, 0, 0]], ![![1050, 25, 0], ![-3724, 0, 0]], ![![3472, 61, -1], ![-12314, 75, 0]]]
  g := ![![![1, 0, 0], ![-42, 149, 0], ![-140, 0, 149]], ![![0, 1, 0], ![-14, 43, 2], ![-46, 19, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-10, -21, 1]] ![![149, 0, 0], ![42, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![6258, 149, 0]], ![![-1490, -3129, 149], ![-596, -894, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![42, 1, 0]]], ![![![-10, -21, 1]], ![![-4, -6, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![26, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![26, 1, 0]] 
 ![![151, 0, 0], ![26, 1, 0], ![102, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![26, 1, 0], ![0, 27, 2], ![-176, 19, 26]]]
  hmulB := by decide  
  f := ![![![2965, 114, 0], ![-17214, 0, 0]], ![![494, 19, 0], ![-2868, 0, 0]], ![![1966, 62, -1], ![-11414, 76, 0]]]
  g := ![![![1, 0, 0], ![-26, 151, 0], ![-102, 0, 151]], ![![0, 1, 0], ![-6, 27, 2], ![-22, 19, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![59, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![59, 1, 0]] 
 ![![151, 0, 0], ![59, 1, 0], ![42, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![59, 1, 0], ![0, 60, 2], ![-176, 19, 59]]]
  hmulB := by decide  
  f := ![![![2479, 42, 0], ![-6342, 0, 0]], ![![885, 15, 0], ![-2264, 0, 0]], ![![602, -20, -1], ![-1540, 76, 0]]]
  g := ![![![1, 0, 0], ![-59, 151, 0], ![-42, 0, 151]], ![![0, 1, 0], ![-24, 60, 2], ![-25, 19, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10361197341080941113265, -1645350096153681160002, -88530596159724289362]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![-10361197341080941113265, -1645350096153681160002, -88530596159724289362]] 
 ![![151, 0, 0], ![65, 1, 0], ![120, 0, 1]] where
  M :=![![![-10361197341080941113265, -1645350096153681160002, -88530596159724289362], ![15581384924111474927712, -13688628764269383771145, -3290700192307362320004], ![281790924460992146696496, -23470959364864204576182, -12043278668115702611143]]]
  hmulB := by decide  
  f := ![![![-87620080296883555691655459289939651758324007, 17737511689577656670902314656525658229926402, -4202491412715937125972610046247329883220518]], ![![-32818984971254478051565731693420843078438737, 6643763936249264762876938524252016712818733, -1574085552631659601631887574125994211585966]], ![![-92755171770269514729556636943119464166816776, 18777042179935740028748420008786963733001162, -4448784017645025272859922223300122553152159]]]
  g := ![![![710001526146193702055, -1645350096153681160002, -88530596159724289362], ![8610770050851025817567, -13688628764269383771145, -3290700192307362320004], ![21540375651331455347586, -23470959364864204576182, -12043278668115702611143]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![26, 1, 0]] ![![151, 0, 0], ![59, 1, 0]]
  ![![87620080296883555691655459289939651758324007, -17737511689577656670902314656525658229926402, 4202491412715937125972610046247329883220518]] where
 M := ![![![22801, 0, 0], ![8909, 151, 0]], ![![3926, 151, 0], ![1534, 86, 2]]]
 hmul := by decide  
 g := ![![![![1564540798503222108103015, 248447864519205855160302, 13368120020118367693662]], ![![595729258199664050754923, 110764284437336572211263, 8514005365731095392362]]], ![![![253809745943992994017178, 56467731264265093931197, 5592495692460193843416]], ![![92652289859752268414386, 24822059867262531873602, 2933064293931666388238]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![87620080296883555691655459289939651758324007, -17737511689577656670902314656525658229926402, 4202491412715937125972610046247329883220518]] ![![-10361197341080941113265, -1645350096153681160002, -88530596159724289362]]
  ![![151, 0, 0]] where
 M := ![![![-151, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10538453, 1123794, -26400]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![10538453, 1123794, -26400]] 
 ![![157, 0, 0], ![0, 157, 0], ![138, 79, 1]] where
  M :=![![![10538453, 1123794, -26400], ![4646400, 11160647, 2247588], ![-200110944, 23675286, 10036853]]]
  hmulB := by decide  
  f := ![![![-374557226839, 75824093826, -17964757896]], ![![3161797389696, -640063533037, 151648187652]], ![![1166669791554, -236176673149, 55956577121]]]
  g := ![![![90329, 20442, -26400], ![-1945992, -1059865, 2247588], ![-10096794, -4899593, 10036853]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [50, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [148, 156], [0, 1]]
 g := ![![[41, 113], [100], [134, 101], [140, 58], [52, 39], [81], [1]], ![[123, 44], [100], [10, 56], [89, 99], [15, 118], [81], [1]]]
 h' := ![![[148, 156], [113, 120], [51, 10], [65, 130], [69, 23], [20, 14], [107, 148], [0, 1]], ![[0, 1], [132, 37], [118, 147], [151, 27], [19, 134], [51, 143], [31, 9], [148, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [70, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [50, 9, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3658, -88, 138]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-98, -70, 138]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-374557226839, 75824093826, -17964757896]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-374557226839, 75824093826, -17964757896]] 
 ![![157, 0, 0], ![156, 1, 0], ![0, 0, 1]] where
  M :=![![![-374557226839, 75824093826, -17964757896], ![3161797389696, -640063533037, 151648187652], ![-14925939208224, 3021556477542, -715887626863]]]
  hmulB := by decide  
  f := ![![![10538453, 1123794, -26400]], ![![10500924, 1187723, -11916]], ![![-1274592, 150798, 63929]]]
  g := ![![![-77726852635, 75824093826, -17964757896], ![656125532124, -640063533037, 151648187652], ![-3097380571368, 3021556477542, -715887626863]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![10538453, 1123794, -26400]] ![![-374557226839, 75824093826, -17964757896]]
  ![![157, 0, 0]] where
 M := ![![![157, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6311868633072937881, 1347018154251231232, 443734521691691158]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-6311868633072937881, 1347018154251231232, 443734521691691158]] 
 ![![163, 0, 0], ![0, 163, 0], ![109, 62, 1]] where
  M :=![![![-6311868633072937881, 1347018154251231232, 443734521691691158], ![-78097275817737643808, 3466105433320425353, 2694036308502462464], ![-198026557239347874928, -13455292978095428496, 2119087279069194121]]]
  hmulB := by decide  
  f := ![![![-267448023044105784882336657839772539, 54141270117826964712782577136014880, -12827516436671022632491837211014398]], ![![2257642892854099983318563349138534048, -457029565223028250186898987713031221, 108282540235653929425565154272029760]], ![![614505152502957500812682310991079867, -124398337560238343783388255768274626, 29473296734187404555483114993964599]]]
  g := ![![![-335453567469124381, -160518541046832028, 443734521691691158], ![-2280657873892675168, -1003461016526578205, 2694036308502462464], ![-2631945218760061559, -888581007855125546, 2119087279069194121]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [78, 117, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 162], [0, 1]]
 g := ![![[83, 53], [156, 81], [53], [25], [156], [21, 160], [1]], ![[76, 110], [133, 82], [53], [25], [156], [46, 3], [1]]]
 h' := ![![[46, 162], [57, 78], [144, 154], [140, 78], [121, 5], [155, 112], [85, 46], [0, 1]], ![[0, 1], [59, 85], [56, 9], [142, 85], [25, 158], [91, 51], [82, 117], [46, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [133]]
 b := ![[], [19, 148]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [78, 117, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1124, -2054, -112]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![68, 30, -112]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-267448023044105784882336657839772539, 54141270117826964712782577136014880, -12827516436671022632491837211014398]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-267448023044105784882336657839772539, 54141270117826964712782577136014880, -12827516436671022632491837211014398]] 
 ![![163, 0, 0], ![39, 1, 0], ![35, 0, 1]] where
  M :=![![![-267448023044105784882336657839772539, 54141270117826964712782577136014880, -12827516436671022632491837211014398], ![2257642892854099983318563349138534048, -457029565223028250186898987713031221, 108282540235653929425565154272029760], ![-10657684987164595781109015250507885904, 2157505578665762321202150640153549744, -511170835340855214899681564849046101]]]
  hmulB := by decide  
  f := ![![![-6311868633072937881, 1347018154251231232, 443734521691691158]], ![![-1989326089003571909, 343557137724653027, 122697439598027102]], ![![-2570196069919636201, 206689217304893648, 108280954222566777]]]
  g := ![![![-11840456946968537524807624931035883, 54141270117826964712782577136014880, -12827516436671022632491837211014398], ![99950349866897633194557321904452209, -457029565223028250186898987713031221, 108282540235653929425565154272029760], ![-471836952872388918935607579428096395, 2157505578665762321202150640153549744, -511170835340855214899681564849046101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-6311868633072937881, 1347018154251231232, 443734521691691158]] ![![-267448023044105784882336657839772539, 54141270117826964712782577136014880, -12827516436671022632491837211014398]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![336000463928193, -68018793596584, 16115473297244]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![336000463928193, -68018793596584, 16115473297244]] 
 ![![167, 0, 0], ![0, 167, 0], ![110, 66, 1]] where
  M :=![![![336000463928193, -68018793596584, 16115473297244], ![-2836323300314944, 574175662979245, -136037587193168], ![13389469323156256, -2710518728492568, 642194456575829]]]
  hmulB := by decide  
  f := ![![![27109543, -2859368, -1286004]], ![![226336704, -183901, -5718736]], ![![109642830, -1603758, -3091147]]]
  g := ![![![-8603003585441, -6776287612064, 16115473297244], ![72621624496608, 57201535435499, -136037587193168], ![-342825873653802, -270032053068846, 642194456575829]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [166, 133, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 166], [0, 1]]
 g := ![![[34, 147], [115, 141], [58, 132], [122], [127], [127, 154], [1]], ![[22, 20], [66, 26], [37, 35], [122], [127], [19, 13], [1]]]
 h' := ![![[34, 166], [115, 67], [58, 59], [31, 74], [57, 17], [127, 131], [1, 34], [0, 1]], ![[0, 1], [55, 100], [60, 108], [42, 93], [134, 150], [72, 36], [155, 133], [34, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [89, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [166, 133, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1154, -826, -220]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![138, 82, -220]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27109543, 2859368, 1286004]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-27109543, 2859368, 1286004]] 
 ![![167, 0, 0], ![35, 1, 0], ![38, 0, 1]] where
  M :=![![![-27109543, 2859368, 1286004], ![-226336704, 183901, 5718736], ![-390080416, -58840360, -2675467]]]
  hmulB := by decide  
  f := ![![![-336000463928193, 68018793596584, -16115473297244]], ![![-53435287048933, 10817258161085, -2562898073116]], ![![-156631658397770, 31707981348280, -7512469711803]]]
  g := ![![![-1054225, 2859368, 1286004], ![-2695121, 183901, 5718736], ![10604790, -58840360, -2675467]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![336000463928193, -68018793596584, 16115473297244]] ![![-27109543, 2859368, 1286004]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-54, -24, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-54, -24, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![119, 149, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-54, -24, 1], ![-176, -59, -48], ![4312, -544, -35]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-119, -149, 173]], ![![-1, -1, 1], ![32, 41, -48], ![49, 27, -35]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [26, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 172], [0, 1]]
 g := ![![[43, 132], [35], [133, 109], [114, 60], [163], [88, 172], [1]], ![[36, 41], [35], [63, 64], [158, 113], [163], [168, 1], [1]]]
 h' := ![![[93, 172], [132, 88], [2, 30], [150, 52], [51, 38], [134, 63], [147, 93], [0, 1]], ![[0, 1], [12, 85], [24, 143], [142, 121], [125, 135], [111, 110], [146, 80], [93, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [9, 117]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [26, 80, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-108925, -20808, 10901]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8128, -9509, 10901]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![48, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![48, 1, 0]] 
 ![![173, 0, 0], ![48, 1, 0], ![35, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![48, 1, 0], ![0, 49, 2], ![-176, 19, 48]]]
  hmulB := by decide  
  f := ![![![4849, 101, 0], ![-17473, 0, 0]], ![![1296, 27, 0], ![-4670, 0, 0]], ![![895, -6, -1], ![-3225, 87, 0]]]
  g := ![![![1, 0, 0], ![-48, 173, 0], ![-35, 0, 173]], ![![0, 1, 0], ![-14, 49, 2], ![-16, 19, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-54, -24, 1]] ![![173, 0, 0], ![48, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![8304, 173, 0]], ![![-9342, -4152, 173], ![-2768, -1211, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![48, 1, 0]]], ![![![-54, -24, 1]], ![![-16, -7, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-53465279351049588339, 21033451582297986518, 5797244506223904442]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-53465279351049588339, 21033451582297986518, 5797244506223904442]] 
 ![![179, 0, 0], ![0, 179, 0], ![142, 133, 1]] where
  M :=![![![-53465279351049588339, 21033451582297986518, 5797244506223904442], ![-1020315033095407181792, 77715817849502582577, 42066903164595973036], ![-3191729961936742036272, -110521936484041847054, 56682366267204596059]]]
  hmulB := by decide  
  f := ![![![-50583419283456296786710654064583219553, 10239935729333337618301240712315604170, -2426114932150954452147785419789706266]], ![![426996228058567983578010233882988302816, -86439667264991093759217336328272034437, 20479871458666675236602481424631208340]], ![![265876681514786571282415780709260260406, -53823173071462928053856988044893151717, 12752150729848647166958804038129747379]]]
  g := ![![![-4897620107457229157, -4189944512544588292, 5797244506223904442], ![-39071593756804666776, -30822247503026602409, 42066903164595973036], ![-62796793138993266350, -42733389106269570519, 56682366267204596059]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [96, 118, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 178], [0, 1]]
 g := ![![[87, 13], [27, 45], [74], [144], [44, 161], [111, 141], [1]], ![[164, 166], [87, 134], [74], [144], [20, 18], [120, 38], [1]]]
 h' := ![![[61, 178], [93, 27], [33, 89], [131, 130], [72, 12], [84, 124], [83, 61], [0, 1]], ![[0, 1], [129, 152], [92, 90], [6, 49], [88, 167], [130, 55], [45, 118], [61, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [41, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [96, 118, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-637, 224, 143]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-117, -105, 143]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-50583419283456296786710654064583219553, 10239935729333337618301240712315604170, -2426114932150954452147785419789706266]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-50583419283456296786710654064583219553, 10239935729333337618301240712315604170, -2426114932150954452147785419789706266]] 
 ![![179, 0, 0], ![92, 1, 0], ![18, 0, 1]] where
  M :=![![![-50583419283456296786710654064583219553, 10239935729333337618301240712315604170, -2426114932150954452147785419789706266], ![426996228058567983578010233882988302816, -86439667264991093759217336328272034437, 20479871458666675236602481424631208340], ![-2015726802391951412610023482309040485328, 408056892886617406536728690475490630638, -96679602994324431377518577040587638607]]]
  hmulB := by decide  
  f := ![![![-53465279351049588339, 21033451582297986518, 5797244506223904442]], ![![-33179445437943962620, 11244655661569370627, 3214599987358632300]], ![![-23207290448355500706, 1497654703895653130, 899624398766675285]]]
  g := ![![![-5301605796667073617495891966711754695, 10239935729333337618301240712315604170, -2426114932150954452147785419789706266], ![44753116928389656174118215142126557100, -86439667264991093759217336328272034437, 20479871458666675236602481424631208340], ![-211266637396999514241305746476668162062, 408056892886617406536728690475490630638, -96679602994324431377518577040587638607]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-53465279351049588339, 21033451582297986518, 5797244506223904442]] ![![-50583419283456296786710654064583219553, 10239935729333337618301240712315604170, -2426114932150954452147785419789706266]]
  ![![179, 0, 0]] where
 M := ![![![179, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2802030455533, -554559257282, -47158389522]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-2802030455533, -554559257282, -47158389522]] 
 ![![181, 0, 0], ![39, 1, 0], ![125, 0, 1]] where
  M :=![![![-2802030455533, -554559257282, -47158389522], ![8299876555872, -4252599113733, -1109118514564], ![93452491003696, -6386687610422, -3698039856451]]]
  hmulB := by decide  
  f := ![![![8642687540637281777555575, -1749596334105088393627898, 414526214187994146549422]], ![![1459161328109210052662813, -295387667149140139133267, 69985246879124833857302]], ![![7871509415639222455079039, -1593481651710918307065008, 377538466208333916467803]]]
  g := ![![![136577786015, -554559257282, -47158389522], ![1728127382939, -4252599113733, -1109118514564], ![4446344142909, -6386687610422, -3698039856451]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![440998551, -89274250, 21151460]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![440998551, -89274250, 21151460]] 
 ![![181, 0, 0], ![47, 1, 0], ![139, 0, 1]] where
  M :=![![![440998551, -89274250, 21151460], ![-3722656960, 753602041, -178548500], ![17573596480, -3557539230, 842876291]]]
  hmulB := by decide  
  f := ![![![454931, 30950, -4860]], ![![122857, 10211, -920]], ![![316909, 29380, -1729]]]
  g := ![![![9374781, -89274250, 21151460], ![-79136527, 753602041, -178548500], ![373580861, -3557539230, 842876291]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4241857963028385, -858707329984268, 203450756986142]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![4241857963028385, -858707329984268, 203450756986142]] 
 ![![181, 0, 0], ![94, 1, 0], ![60, 0, 1]] where
  M :=![![![4241857963028385, -858707329984268, 203450756986142], ![-35807333229560992, 7248715015780815, -1717414659968536], ![169036156692011664, -34219105884481588, 8107422345765083]]]
  hmulB := by decide  
  f := ![![![-943032523, -156439252, -9474082]], ![![-480539330, -88313641, -6648852]], ![![-165095924, -63673932, -9345221]]]
  g := ![![![401951942333597, -858707329984268, 203450756986142], ![-3393047873562682, 7248715015780815, -1717414659968536], ![16017606459046276, -34219105884481588, 8107422345765083]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-2802030455533, -554559257282, -47158389522]] ![![440998551, -89274250, 21151460]]
  ![![-943032523, -156439252, -9474082]] where
 M := ![![![-943032523, -156439252, -9474082]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![-943032523, -156439252, -9474082]] ![![4241857963028385, -858707329984268, 203450756986142]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0]] 
 ![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [78, 172, 189, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [188, 190, 114], [5, 0, 77], [0, 1]]
 g := ![![[169, 18, 78], [157, 174, 104], [36, 166, 120], [27, 105, 18], [65, 6, 36], [23, 2, 1], []], ![[84, 54, 173, 42], [53, 70, 136, 66], [101, 135, 130, 14], [0, 63, 188, 141], [161, 28, 90, 84], [53, 62], [170, 8]], ![[50, 165, 88, 1], [153, 31, 154, 1], [161, 155, 171, 77], [17, 140, 120, 120], [35, 158, 126, 160], [151, 15, 156, 77], [16, 8]]]
 h' := ![![[188, 190, 114], [169, 109, 101], [57, 176, 103], [186, 83, 87], [87, 89, 171], [116, 90, 6], [0, 0, 1], [0, 1]], ![[5, 0, 77], [19, 123, 11], [135, 123, 9], [167, 62, 103], [114, 5, 23], [178, 111, 137], [119, 129], [188, 190, 114]], ![[0, 1], [4, 150, 79], [73, 83, 79], [14, 46, 1], [162, 97, 188], [104, 181, 48], [114, 62, 190], [5, 0, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 169], []]
 b := ![[], [13, 25, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [78, 172, 189, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![801054, -662770, 115746]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4194, -3470, 606]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def PBC191 : ContainsPrimesAboveP 191 ![I191N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![191, 0, 0]]) timesTableT_eq_Table B_one_repr 191 (by decide) 𝕀

instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-102, 16, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-102, 16, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![91, 16, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-102, 16, 1], ![-176, -67, 32], ![-2728, 216, -83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-91, -16, 193]], ![![-1, 0, 1], ![-16, -3, 32], ![25, 8, -83]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [152, 88, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [105, 192], [0, 1]]
 g := ![![[92, 2], [9], [110], [24], [54], [172], [105, 1]], ![[109, 191], [9], [110], [24], [54], [172], [17, 192]]]
 h' := ![![[105, 192], [183, 141], [59, 3], [145, 66], [60, 105], [111, 61], [59, 65], [0, 1]], ![[0, 1], [127, 52], [181, 190], [127, 127], [84, 88], [147, 132], [129, 128], [105, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78]]
 b := ![[], [172, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [152, 88, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13396, -2016, 260]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-192, -32, 260]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-32, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-32, 1, 0]] 
 ![![193, 0, 0], ![161, 1, 0], ![83, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-32, 1, 0], ![0, -31, 2], ![-176, 19, -32]]]
  hmulB := by decide  
  f := ![![![6049, -189, 0], ![36477, 0, 0]], ![![5057, -158, 0], ![30495, 0, 0]], ![![2611, -66, -1], ![15745, 97, 0]]]
  g := ![![![1, 0, 0], ![-161, 193, 0], ![-83, 0, 193]], ![![-1, 1, 0], ![25, -31, 2], ![-3, 19, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-102, 16, 1]] ![![193, 0, 0], ![-32, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-6176, 193, 0]], ![![-19686, 3088, 193], ![3088, -579, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-32, 1, 0]]], ![![![-102, 16, 1]], ![![16, -3, 0]]]]
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


lemma PB241I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB241I3 : PrimesBelowBoundCertificateInterval O 137 193 241 where
  m := 11
  g := ![1, 2, 3, 2, 2, 2, 2, 2, 3, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB241I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0]
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
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![181, 181, 181]
    · exact ![6967871]
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
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
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
      exact NI173N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I149N1, I151N0, I151N1, I151N2, I157N1, I163N1, I167N1, I173N1, I179N1, I181N0, I181N1, I181N2, I193N1]
  Il := ![[], [I149N1], [I151N0, I151N1, I151N2], [I157N1], [I163N1], [I167N1], [I173N1], [I179N1], [I181N0, I181N1, I181N2], [], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
