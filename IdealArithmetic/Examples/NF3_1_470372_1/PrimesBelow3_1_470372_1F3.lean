
import IdealArithmetic.Examples.NF3_1_470372_1.RI3_1_470372_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [94, 59, 120, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [109, 66, 132], [49, 72, 7], [0, 1]]
 g := ![![[92, 54, 31], [79, 99, 44], [20, 125], [18, 101, 51], [23, 20], [19, 1], []], ![[26, 17, 39, 104], [101, 46, 128, 72], [11, 64], [61, 39, 1, 58], [18, 29], [86, 41], [7, 49]], ![[48, 136, 136, 30], [78, 17, 113, 81], [108, 63], [77, 80, 88, 136], [98, 7], [34, 47], [132, 49]]]
 h' := ![![[109, 66, 132], [80, 101, 93], [86, 28, 34], [115, 37, 79], [86, 82, 32], [21, 36, 24], [0, 0, 1], [0, 1]], ![[49, 72, 7], [96, 59, 12], [107, 138, 28], [53, 55, 8], [88, 115, 62], [23, 106, 86], [103, 56, 72], [109, 66, 132]], ![[0, 1], [118, 118, 34], [102, 112, 77], [61, 47, 52], [105, 81, 45], [2, 136, 29], [1, 83, 66], [49, 72, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 136], []]
 b := ![[], [137, 95, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [94, 59, 120, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![127602, 18904, -83400]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![918, 136, -600]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5608610731, 1924418276, -2325809014]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-5608610731, 1924418276, -2325809014]] 
 ![![149, 0, 0], ![0, 149, 0], ![8, 96, 1]] where
  M :=![![![-5608610731, 1924418276, -2325809014], ![-255036210064, 35453170045, 23895800788], ![300869534368, -63352018612, 25429687927]]]
  hmulB := by decide  
  f := ![![![-16210807157968018879, -660451944585167884, -862032337057840182]], ![![-91778588513076403888, -3739193654212911735, -4880454771735998476]], ![![-60250191080885660728, -2454680724607838564, -3203888154335897017]]]
  g := ![![![87233969, 1511423380, -2325809014], ![-2994648432, -15158011447, 23895800788], ![653906248, -16809409796, 25429687927]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [78, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [111, 148], [0, 1]]
 g := ![![[96, 118], [25], [59, 1], [114], [70, 118], [103], [1]], ![[82, 31], [25], [21, 148], [114], [56, 31], [103], [1]]]
 h' := ![![[111, 148], [127, 72], [17, 144], [26, 148], [53, 76], [136, 77], [71, 111], [0, 1]], ![[0, 1], [73, 77], [58, 5], [64, 1], [145, 73], [41, 72], [25, 38], [111, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [95, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [78, 38, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7867, 2744, -2492]
  a := ![-3, 0, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![81, 1624, -2492]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16210807157968018879, -660451944585167884, -862032337057840182]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-16210807157968018879, -660451944585167884, -862032337057840182]] 
 ![![149, 0, 0], ![85, 1, 0], ![50, 0, 1]] where
  M :=![![![-16210807157968018879, -660451944585167884, -862032337057840182], ![-91778588513076403888, -3739193654212911735, -4880454771735998476], ![-36847516532884524192, -1501221605447076404, -1959418212930080381]]]
  hmulB := by decide  
  f := ![![![-5608610731, 1924418276, -2325809014]], ![![-4911195451, 1335763245, -1166429298]], ![![137174482, 220596612, -609803777]]]
  g := ![![![557243120702437989, -660451944585167884, -862032337057840182], ![3154869870347792063, -3739193654212911735, -4880454771735998476], ![1266625708567926102, -1501221605447076404, -1959418212930080381]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-5608610731, 1924418276, -2325809014]] ![![-16210807157968018879, -660451944585167884, -862032337057840182]]
  ![![149, 0, 0]] where
 M := ![![![149, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [28, 125, 123, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 126, 50], [28, 24, 101], [0, 1]]
 g := ![![[0, 53, 78], [119, 76, 72], [102, 142, 37], [72, 81], [132, 130, 5], [28, 1], []], ![[150, 77, 115, 105], [139, 142, 81, 80], [29, 40, 3, 10], [39, 25], [8, 125, 100, 31], [143, 123], [3, 84]], ![[39, 31, 102, 30], [74, 2, 86, 70], [19, 2, 68, 140], [40, 45], [147, 60, 136, 35], [138, 21], [103, 84]]]
 h' := ![![[0, 126, 50], [141, 78, 57], [13, 44, 26], [148, 109, 43], [79, 29, 9], [122, 96, 55], [0, 0, 1], [0, 1]], ![[28, 24, 101], [34, 104, 134], [94, 25, 106], [9, 59, 140], [78, 100, 5], [32, 125, 80], [67, 142, 24], [0, 126, 50]], ![[0, 1], [103, 120, 111], [99, 82, 19], [27, 134, 119], [111, 22, 137], [107, 81, 16], [14, 9, 126], [28, 24, 101]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 69], []]
 b := ![[], [117, 34, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [28, 125, 123, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![781745573, -124394706, -80795721]
  a := ![1, -64, -69]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5177123, -823806, -535071]
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


def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13679854515642951603, -2725638776597843344, 770575574209256434]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![13679854515642951603, -2725638776597843344, 770575574209256434]] 
 ![![157, 0, 0], ![88, 1, 0], ![87, 0, 1]] where
  M :=![![![13679854515642951603, -2725638776597843344, 770575574209256434], ![88673439567795381560, -4100632224900838029, -28797538914396946308], ![-325192010840937338512, 54398278464495083580, 7572498455699791781]]]
  hmulB := by decide  
  f := ![![![1535484509767044135324072569443525982991, 62557880090355965909665811154939509384, 81651535766989622510433978147723302538]], ![![916024757720726440814177860692194421392, 37320185640937879662592687407799420299, 48710897304870491687859746702252223644]], ![![873104088973322924783572369556759843517, 35571534950019925444155084624642238228, 46428530731271242192713295374329456987]]]
  g := ![![![1187872559872916281, -2725638776597843344, 770575574209256434], ![18821114400710850044, -4100632224900838029, -28797538914396946308], ![-36758266760269978207, 54398278464495083580, 7572498455699791781]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33706185672679634079, -1373239201178702165, -1792373552136412136]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-33706185672679634079, -1373239201178702165, -1792373552136412136]] 
 ![![157, 0, 0], ![113, 1, 0], ![129, 0, 1]] where
  M :=![![![-33706185672679634079, -1373239201178702165, -1792373552136412136], ![-190829865228375106358, -7774687240854444233, -10147644907514197378], ![-76614891641843348380, -3121402511050535264, -4074103988276047709]]]
  hmulB := by decide  
  f := ![![![-30742574405, 4936026081, 1230488318]], ![![-21343249819, 3294347846, 1184359644]], ![![-22177839581, 3662406265, 634783705]]]
  g := ![![![2246407848956120230, -1373239201178702165, -1792373552136412136], ![12718190993996869769, -7774687240854444233, -10147644907514197378], ![5106133799964823509, -3121402511050535264, -4074103988276047709]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![13679854515642951603, -2725638776597843344, 770575574209256434]] ![![-33706185672679634079, -1373239201178702165, -1792373552136412136]]
  ![![-30742574405, 4936026081, 1230488318]] where
 M := ![![![-30742574405, 4936026081, 1230488318]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![-30742574405, 4936026081, 1230488318]] ![![-33706185672679634079, -1373239201178702165, -1792373552136412136]]
  ![![157, 0, 0]] where
 M := ![![![157, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [78, 51, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [119, 10, 60], [161, 152, 103], [0, 1]]
 g := ![![[34, 103, 35], [88, 24, 58], [102, 150], [41, 1], [3, 136], [109, 117, 1], []], ![[158, 18, 62, 10], [41, 125, 62, 61], [112, 81], [34, 81], [104, 15], [104, 132, 93, 88], [67, 14]], ![[68, 76, 107, 59], [116, 155, 156, 123], [37, 97], [155, 64], [158, 81], [95, 45, 144, 31], [24, 14]]]
 h' := ![![[119, 10, 60], [145, 118, 19], [152, 154, 104], [152, 99, 65], [116, 125, 1], [137, 148, 25], [0, 0, 1], [0, 1]], ![[161, 152, 103], [88, 12, 25], [36, 11, 109], [40, 14, 9], [128, 99, 154], [47, 89, 129], [133, 153, 152], [119, 10, 60]], ![[0, 1], [114, 33, 119], [31, 161, 113], [132, 50, 89], [117, 102, 8], [85, 89, 9], [88, 10, 10], [161, 152, 103]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81, 104], []]
 b := ![[], [88, 11, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [78, 51, 46, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5083970, 1178490, -693402]
  a := ![3, -1, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-31190, 7230, -4254]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25786599406355057248638379827185, -1050583697419092582892271408709, -1371238479023452583986053120382]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-25786599406355057248638379827185, -1050583697419092582892271408709, -1371238479023452583986053120382]] 
 ![![167, 0, 0], ![0, 167, 0], ![21, 59, 1]] where
  M :=![![![-25786599406355057248638379827185, -1050583697419092582892271408709, -1371238479023452583986053120382], ![-145992588339694693904709194183838, -5947951136818001070646072718491, -7763360016144020660950607846326], ![-58613500160323895592923187325292, -2387999547622854849528401146004, -3116854826165083323063040204037]]]
  hmulB := by decide  
  f := ![![![-289618917256089, 154022322206615, -256217943650716]], ![![-27979582558690558, 4117912825568597, 2052659109367582]], ![![-9760444548986693, 1437963575499822, 712406684006669]]]
  g := ![![![18020411096631419251908597011, 478158602185416825582544087987, -1371238479023452583986053120382], ![102023784427124191468584255024, 2707127483926222861828980779729, -7763360016144020660950607846326], ![40960785563729665816770400955, 1086864881413874618031083658037, -3116854826165083323063040204037]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [55, 62, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [105, 166], [0, 1]]
 g := ![![[74, 122], [110, 14], [106, 77], [1], [154], [121, 3], [1]], ![[25, 45], [77, 153], [8, 90], [1], [154], [102, 164], [1]]]
 h' := ![![[105, 166], [129, 150], [15, 66], [128, 113], [4, 1], [25, 34], [112, 105], [0, 1]], ![[0, 1], [14, 17], [98, 101], [136, 54], [109, 166], [88, 133], [115, 62], [105, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127]]
 b := ![[], [48, 147]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [55, 62, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1270, -90, -695]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![95, 245, -695]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![289618917256089, -154022322206615, 256217943650716]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![289618917256089, -154022322206615, 256217943650716]] 
 ![![167, 0, 0], ![80, 1, 0], ![112, 0, 1]] where
  M :=![![![289618917256089, -154022322206615, 256217943650716], ![27979582558690558, -4117912825568597, -2052659109367582], ![-26883128544343060, 6051408366415864, -3245605593091421]]]
  hmulB := by decide  
  f := ![![![25786599406355057248638379827185, 1050583697419092582892271408709, 1371238479023452583986053120382]], ![![13227069106874845950872931618914, 538890101379313818575016679133, 703367894239642080118771601658]], ![![17644985830371798248146237892036, 718882476997372599601573646236, 938296793274202231913179578963]]]
  g := ![![![-96317395180209, -154022322206615, 256217943650716], ![3516828915289506, -4117912825568597, -2052659109367582], ![-883161505577084, 6051408366415864, -3245605593091421]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-25786599406355057248638379827185, -1050583697419092582892271408709, -1371238479023452583986053120382]] ![![289618917256089, -154022322206615, 256217943650716]]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [125, 154, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [112, 62, 1], [45, 110, 172], [0, 1]]
 g := ![![[60, 86, 64], [140, 64], [18, 171, 140], [51, 2, 157], [14, 52], [102, 157, 1], []], ![[96, 124, 61, 164], [19, 34], [21, 143, 96, 85], [75, 119, 16, 157], [5, 109], [64, 1, 156, 163], [108, 1]], ![[137, 92, 94, 152], [30, 118], [104, 142, 102, 126], [152, 16], [114, 164], [23, 86, 49, 135], [110, 1]]]
 h' := ![![[112, 62, 1], [147, 82, 165], [172, 57, 165], [26, 163, 113], [89, 55, 26], [52, 132, 15], [0, 0, 1], [0, 1]], ![[45, 110, 172], [25, 10, 67], [18, 17, 42], [41, 77, 137], [77, 92, 147], [150, 95, 52], [82, 72, 110], [112, 62, 1]], ![[0, 1], [65, 81, 114], [3, 99, 139], [4, 106, 96], [118, 26], [3, 119, 106], [39, 101, 62], [45, 110, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [125, 53], []]
 b := ![[], [120, 11, 120], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [125, 154, 16, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5546380, -214347, -774348]
  a := ![-1, 21, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![32060, -1239, -4476]
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

instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3463836564789, 141121757396, 184194352572]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![3463836564789, 141121757396, 184194352572]] 
 ![![179, 0, 0], ![0, 179, 0], ![76, 29, 1]] where
  M :=![![![3463836564789, 141121757396, 184194352572], ![19610746562984, 798970438429, 1042828868816], ![7873375695888, 320772817672, 418677761417]]]
  hmulB := by decide  
  f := ![![![-135321, -16412, 100412]], ![![10877320, -1774737, -364944]], ![![1672452, -285175, -25479]]]
  g := ![![![-58854381177, -29053153448, 184194352572], ![-333208086408, -164486406465, 1042828868816], ![-133777285876, -66038448399, 418677761417]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [1, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [97, 178], [0, 1]]
 g := ![![[82, 1], [97, 82], [31], [161], [34, 52], [116, 101], [1]], ![[0, 178], [175, 97], [31], [161], [66, 127], [68, 78], [1]]]
 h' := ![![[97, 178], [82, 1], [124, 34], [100, 63], [145, 55], [63, 54], [178, 97], [0, 1]], ![[0, 1], [0, 178], [21, 145], [125, 116], [110, 124], [110, 125], [100, 82], [97, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [1, 131]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [1, 82, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2654, 782, -1010]
  a := ![1, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![414, 168, -1010]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![135321, 16412, -100412]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![135321, 16412, -100412]] 
 ![![179, 0, 0], ![70, 1, 0], ![176, 0, 1]] where
  M :=![![![135321, 16412, -100412], ![-10877320, 1774737, 364944], ![5788976, -1668360, 1608677]]]
  hmulB := by decide  
  f := ![![![-3463836564789, -141121757396, -184194352572]], ![![-1464130201666, -59650801431, -77857170664]], ![![-3449768777088, -140548615192, -183446278291]]]
  g := ![![![93067, 16412, -100412], ![-1113626, 1774737, 364944], ![-896944, -1668360, 1608677]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![3463836564789, 141121757396, 184194352572]] ![![135321, 16412, -100412]]
  ![![179, 0, 0]] where
 M := ![![![-179, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-38324098034229480147749544267, -1561379691000664775868901436, -2037937498864286539006334678]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-38324098034229480147749544267, -1561379691000664775868901436, -2037937498864286539006334678]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 54, 1]] where
  M :=![![![-38324098034229480147749544267, -1561379691000664775868901436, -2037937498864286539006334678], ![-216974490495341616660946342352, -8839857434402225075385992291, -11537921912278074680676345004], ![-87111506673500334233587967968, -3549049928089375132186262516, -4632276169263852510916721225]]]
  hmulB := by decide  
  f := ![![![78168614823169, -14284028995308, 1188456723434]], ![![156921384121488, 30585249257609, -145217203399948]], ![![38030615149888, 10479482419690, -42833255036657]]]
  g := ![![![-211735348255411492529003007, 599377045567242034974989896, -2037937498864286539006334678], ![-1198754091134484069949979792, 3393413954854219931939981425, -11537921912278074680676345004], ![-481279042395029470903800928, 1362397034321318566062523114, -4632276169263852510916721225]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [16, 155, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 180], [0, 1]]
 g := ![![[21, 34], [4], [49, 38], [67], [16, 167], [92, 133], [1]], ![[0, 147], [4], [132, 143], [67], [14, 14], [111, 48], [1]]]
 h' := ![![[26, 180], [97, 45], [121, 2], [28, 161], [106, 130], [157, 158], [165, 26], [0, 1]], ![[0, 1], [0, 136], [173, 179], [51, 20], [47, 51], [102, 23], [117, 155], [26, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97]]
 b := ![[], [3, 139]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [16, 155, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2172, 911, -20]
  a := ![-2, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12, 11, -20]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![78168614823169, -14284028995308, 1188456723434]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![78168614823169, -14284028995308, 1188456723434]] 
 ![![181, 0, 0], ![5, 1, 0], ![123, 0, 1]] where
  M :=![![![78168614823169, -14284028995308, 1188456723434], ![156921384121488, 30585249257609, -145217203399948], ![-1590213400430624, 245182858053004, 88909821962275]]]
  hmulB := by decide  
  f := ![![![-38324098034229480147749544267, -1561379691000664775868901436, -2037937498864286539006334678]], ![![-2257430832411541532594994827, -91971027013290325716743091, -120042040920439267269105074]], ![![-26524726877810643051971170789, -1080656087962271505878790824, -1410489439389895562478982799]]]
  g := ![![![18831949267, -14284028995308, 1188456723434], ![98705586497387, 30585249257609, -145217203399948], ![-75978098298649, 245182858053004, 88909821962275]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-38324098034229480147749544267, -1561379691000664775868901436, -2037937498864286539006334678]] ![![78168614823169, -14284028995308, 1188456723434]]
  ![![181, 0, 0]] where
 M := ![![![181, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7637055, -1025816, -804800]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![7637055, -1025816, -804800]] 
 ![![191, 0, 0], ![0, 191, 0], ![97, 29, 1]] where
  M :=![![![7637055, -1025816, -804800], ![-84866768, 18462223, -8648560], ![-78596128, 5145856, 21760687]]]
  hmulB := by decide  
  f := ![![![-2336413091071, -95188879512, -124242032960]], ![![-13227761800656, -538918322735, -703404729200]], ![![-3222763768177, -131300099797, -171374969537]]]
  g := ![![![448705, 116824, -804800], ![3947872, 1409793, -8648560], ![-11462737, -3277037, 21760687]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [153, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [187, 190], [0, 1]]
 g := ![![[20, 5], [89, 134], [166, 81], [30, 48], [36, 138], [14, 16], [1]], ![[0, 186], [126, 57], [33, 110], [29, 143], [57, 53], [141, 175], [1]]]
 h' := ![![[187, 190], [135, 177], [5, 158], [185, 182], [31, 96], [150, 86], [38, 187], [0, 1]], ![[0, 1], [0, 14], [137, 33], [30, 9], [29, 95], [188, 105], [54, 4], [187, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [50, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [153, 4, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4503, -420, -245]
  a := ![0, -5, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![148, 35, -245]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2336413091071, -95188879512, -124242032960]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-2336413091071, -95188879512, -124242032960]] 
 ![![191, 0, 0], ![94, 1, 0], ![167, 0, 1]] where
  M :=![![![-2336413091071, -95188879512, -124242032960], ![-13227761800656, -538918322735, -703404729200], ![-5310717668896, -216366389248, -282404837647]]]
  hmulB := by decide  
  f := ![![![7637055, -1025816, -804800]], ![![3314222, -408191, -441360]], ![![6265927, -869976, -589743]]]
  g := ![![![143244822447, -95188879512, -124242032960], ![810990315774, -538918322735, -703404729200], ![325598590615, -216366389248, -282404837647]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![7637055, -1025816, -804800]] ![![-2336413091071, -95188879512, -124242032960]]
  ![![191, 0, 0]] where
 M := ![![![191, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1000228819, 40750782, 53188566]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![1000228819, 40750782, 53188566]] 
 ![![193, 0, 0], ![25, 1, 0], ![106, 0, 1]] where
  M :=![![![1000228819, 40750782, 53188566], ![5662863564, 230713327, 301130688], ![2273541816, 92627412, 120898765]]]
  hmulB := by decide  
  f := ![![![121699, -13038, -21066]], ![![4111, 553, -3186]], ![![63910, -7608, -9167]]]
  g := ![![![-29308439, 40750782, 53188566], ![-165931723, 230713327, 301130688], ![-66618718, 92627412, 120898765]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N0 : Nat.card (O ⧸ I193N0) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N0)

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := prime_ideal_of_norm_prime hp193.out _ NI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137689881311873476322613, 5609686734039625806830, 7321851960847629464524]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![137689881311873476322613, 5609686734039625806830, 7321851960847629464524]] 
 ![![193, 0, 0], ![58, 1, 0], ![115, 0, 1]] where
  M :=![![![137689881311873476322613, 5609686734039625806830, 7321851960847629464524], ![779540638303464730554932, 31759623406390656503889, 41453163418700999139252], ![312972088842374408556680, 12750939707232799594056, 16642728431079782741093]]]
  hmulB := by decide  
  f := ![![![-398380875435, 172732204154, -254970842676]], ![![-264188633122, 72772460397, -65031322012]], ![![-87875072121, 70108271574, -135963365551]]]
  g := ![![![-5335155050569441496859, 5609686734039625806830, 7321851960847629464524], ![-30205343587657037552770, 31759623406390656503889, 41453163418700999139252], ![-12126923231872036181991, 12750939707232799594056, 16642728431079782741093]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1517043682868313, 528185235603584, -648173745512454]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![-1517043682868313, 528185235603584, -648173745512454]] 
 ![![193, 0, 0], ![110, 1, 0], ![3, 0, 1]] where
  M :=![![![-1517043682868313, 528185235603584, -648173745512454], ![-71059134986552200, 9910106716538119, 6578199847060748], ![82970955265685232, -17525396206831700, 7149192028611329]]]
  hmulB := by decide  
  f := ![![![186134814588021213805352375861751, 7583404024964517508567576588664, 9897979024953881272946574754858]], ![![111547380991333801352589928834922, 4544603113910803494288993563287, 5931687953081162448517646836328]], ![![5085455530891586950380789683765, 207188880957593835284318916660, 270426208490391728045898060239]]]
  g := ![![![-298823307578887, 528185235603584, -648173745512454], ![-6118681209051438, 9910106716538119, 6578199847060748], ![10307341771664965, -17525396206831700, 7149192028611329]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![1000228819, 40750782, 53188566]] ![![137689881311873476322613, 5609686734039625806830, 7321851960847629464524]]
  ![![186134814588021213805352375861751, 7583404024964517508567576588664, 9897979024953881272946574754858]] where
 M := ![![![186134814588021213805352375861751, 7583404024964517508567576588664, 9897979024953881272946574754858]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![186134814588021213805352375861751, 7583404024964517508567576588664, 9897979024953881272946574754858]] ![![-1517043682868313, 528185235603584, -648173745512454]]
  ![![193, 0, 0]] where
 M := ![![![193, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1, I193N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
    exact isPrimeI193N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0 ⊙ MulI193N1)


lemma PB195I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 194 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 194 (by omega)

def PB195I3 : PrimesBelowBoundCertificateInterval O 137 194 195 where
  m := 11
  g := ![1, 2, 1, 3, 1, 2, 1, 2, 2, 2, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB195I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0, I157N1, I157N1]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1, I193N2]
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
    · exact ![3442951]
    · exact ![157, 157, 157]
    · exact ![4330747]
    · exact ![27889, 167]
    · exact ![5177717]
    · exact ![32041, 179]
    · exact ![32761, 181]
    · exact ![36481, 191]
    · exact ![193, 193, 193]
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
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
  β := ![I149N1, I157N0, I157N1, I167N1, I179N1, I181N1, I191N1, I193N0, I193N1, I193N2]
  Il := ![[], [I149N1], [], [I157N0, I157N1, I157N1], [], [I167N1], [], [I179N1], [I181N1], [I191N1], [I193N0, I193N1, I193N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
