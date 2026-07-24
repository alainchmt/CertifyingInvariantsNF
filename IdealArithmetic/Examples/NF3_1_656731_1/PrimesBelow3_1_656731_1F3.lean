
import IdealArithmetic.Examples.NF3_1_656731_1.RI3_1_656731_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [38, 72, 128, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [127, 65, 23], [23, 73, 116], [0, 1]]
 g := ![![[132, 43, 127], [70, 125, 71], [67, 100], [55, 38, 20], [115, 38], [11, 1], []], ![[2, 7, 106, 115], [10, 65, 125, 15], [31, 44], [95, 109, 24, 56], [32, 106], [39, 47], [52, 112]], ![[133, 89, 126, 7], [50, 101, 100, 67], [126, 20], [7, 96, 20, 107], [4, 113], [50, 55], [98, 112]]]
 h' := ![![[127, 65, 23], [120, 23, 31], [120, 103, 40], [134, 3, 129], [79, 137, 115], [138, 4, 49], [0, 0, 1], [0, 1]], ![[23, 73, 116], [42, 93, 12], [108, 12, 7], [70, 24, 34], [8, 99, 9], [116, 111, 55], [114, 31, 73], [127, 65, 23]], ![[0, 1], [16, 23, 96], [67, 24, 92], [44, 112, 115], [124, 42, 15], [50, 24, 35], [2, 108, 65], [23, 73, 116]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 129], []]
 b := ![[], [110, 32, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [38, 72, 128, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![448553, 118845, -671787]
  a := ![-1, -1, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3227, 855, -4833]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [17, 57, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 14, 108], [96, 134, 41], [0, 1]]
 g := ![![[24, 77, 121], [52, 53], [31, 32, 85], [90, 121], [103, 115, 100], [135, 1], []], ![[33, 126, 96, 57], [137, 103], [53, 56, 119, 137], [39, 25], [50, 8, 32, 13], [79, 76], [52, 42]], ![[148, 77, 142, 126], [96, 133], [117, 17, 7, 50], [104, 107], [33, 48, 70, 131], [81, 47], [119, 42]]]
 h' := ![![[39, 14, 108], [3, 6, 11], [69, 68, 65], [137, 141, 54], [37, 95, 138], [89, 36, 139], [0, 0, 1], [0, 1]], ![[96, 134, 41], [92, 97, 36], [22, 40, 111], [102, 6, 114], [13, 125, 144], [40, 140, 15], [41, 96, 134], [39, 14, 108]], ![[0, 1], [136, 46, 102], [24, 41, 122], [93, 2, 130], [64, 78, 16], [6, 122, 144], [41, 53, 14], [96, 134, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128, 92], []]
 b := ![[], [13, 13, 104], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [17, 57, 14, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7458940, -3464548, 3741539]
  a := ![2, -2, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![50060, -23252, 25111]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3036647114394, 33720074260, 121615911557]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![3036647114394, 33720074260, 121615911557]] 
 ![![151, 0, 0], ![0, 151, 0], ![21, 63, 1]] where
  M :=![![![3036647114394, 33720074260, 121615911557], ![10614304379719, 117865237026, 425096579897], ![3784957841519, 42029598659, 151585311286]]]
  hmulB := by decide  
  f := ![![![-362137, 90753, 36038]], ![![3226059, -1227049, 852815]], ![![1349567, -512080, 353297]]]
  g := ![![![3196774647, -50517101681, 121615911557], ![11174014582, -176577611235, 425096579897], ![3984545063, -62965861009, 151585311286]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [13, 148, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 150], [0, 1]]
 g := ![![[23, 121], [92, 97], [96, 78], [116], [83, 34], [9], [1]], ![[84, 30], [81, 54], [28, 73], [116], [34, 117], [9], [1]]]
 h' := ![![[3, 150], [12, 11], [111, 61], [33, 94], [129, 95], [52, 100], [138, 3], [0, 1]], ![[0, 1], [45, 140], [143, 90], [13, 57], [112, 56], [50, 51], [147, 148], [3, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123]]
 b := ![[], [21, 137]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [13, 148, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1804052, 1925113, -6524995]
  a := ![-65, 1, -521]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![919397, 2735098, -6524995]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![362137, -90753, -36038]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![362137, -90753, -36038]] 
 ![![151, 0, 0], ![36, 1, 0], ![91, 0, 1]] where
  M :=![![![362137, -90753, -36038], ![-3226059, 1227049, -852815], ![-8147777, 1925806, 1136296]]]
  hmulB := by decide  
  f := ![![![-3036647114394, -33720074260, -121615911557]], ![![-794262254953, -8819787486, -31809731099]], ![![-1855098312923, -20599710969, -74295584523]]]
  g := ![![![45753, -90753, -36038], ![200042, 1227049, -852815], ![-1197879, 1925806, 1136296]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![3036647114394, 33720074260, 121615911557]] ![![362137, -90753, -36038]]
  ![![151, 0, 0]] where
 M := ![![![-151, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-70702024354, 180447137718, -449311146163]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-70702024354, 180447137718, -449311146163]] 
 ![![157, 0, 0], ![37, 1, 0], ![5, 0, 1]] where
  M :=![![![-70702024354, 180447137718, -449311146163], ![-38909622578463, 10712765483558, 1174713093299], ![12553722958325, -7475909328373, 10893212621276]]]
  hmulB := by decide  
  f := ![![![125478480746619793235852535, 1393360350879090017094631, 5025338553318532347239636]], ![![32364978357417348751296094, 359392920060518137163074, 1296198141299465218783171]], ![![4992306523138914166224032, 55436453544758064368659, 199938908181189609270026]]]
  g := ![![![-28666817765, 180447137718, -449311146163], ![-2809907712972, 10712765483558, 1174713093299], ![1494880923578, -7475909328373, 10893212621276]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, -4]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![5, 0, -4]] 
 ![![157, 0, 0], ![82, 1, 0], ![38, 0, 1]] where
  M :=![![![5, 0, -4], ![-348, 101, -4], ![-28, -28, 101]]]
  hmulB := by decide  
  f := ![![![10089, 112, 404]], ![![5494, 61, 220]], ![![2522, 28, 101]]]
  g := ![![![1, 0, -4], ![-54, 101, -4], ![-10, -28, 101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-70702024354, 180447137718, -449311146163]] ![![-70702024354, 180447137718, -449311146163]]
  ![![-12656658898741334445307093, 5279339279568615828639271, -4650701025338574683958604]] where
 M := ![![![-12656658898741334445307093, 5279339279568615828639271, -4650701025338574683958604]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI157N1 : IdealMulLeCertificate' Table 
  ![![-12656658898741334445307093, 5279339279568615828639271, -4650701025338574683958604]] ![![5, 0, -4]]
  ![![157, 0, 0]] where
 M := ![![![-1770273735074104889442160861, 663432895945910289843407283, -440211525082505168613147716]]]
 hmul := by decide  
 g := ![![![![-11275628885822324136574273, 4225687235324269362059919, -2803895064219778144032788]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-55, 3, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-55, 3, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![108, 3, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-55, 3, 1], ![90, -79, 28], ![268, -65, -76]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-108, -3, 163]], ![![-1, 0, 1], ![-18, -1, 28], ![52, 1, -76]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [106, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 162], [0, 1]]
 g := ![![[13, 16], [23, 158], [134], [134], [60], [34, 97], [1]], ![[133, 147], [67, 5], [134], [134], [60], [28, 66], [1]]]
 h' := ![![[89, 162], [7, 4], [144, 22], [2, 121], [158, 121], [145, 68], [57, 89], [0, 1]], ![[0, 1], [37, 159], [146, 141], [13, 42], [6, 42], [3, 95], [154, 74], [89, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [74, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [106, 74, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-816, 3509, -10023]
  a := ![-2, 1, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6636, 206, -10023]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-28, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-28, 1, 0]] 
 ![![163, 0, 0], ![135, 1, 0], ![76, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-28, 1, 0], ![1, -28, 9], ![87, -24, -27]]]
  hmulB := by decide  
  f := ![![![-6071, 180978, -58176], ![2282, 1053632, 0]], ![![-5044, 149873, -48177], ![1794, 872539, 0]], ![![-2820, 84382, -27125], ![1126, 491264, 0]]]
  g := ![![![1, 0, 0], ![-135, 163, 0], ![-76, 0, 163]], ![![-1, 1, 0], ![19, -28, 9], ![33, -24, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-55, 3, 1]] ![![163, 0, 0], ![-28, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-4564, 163, 0]], ![![-8965, 489, 163], ![1630, -163, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-28, 1, 0]]], ![![![-55, 3, 1]], ![![10, -1, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-45, 26, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-45, 26, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![122, 26, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-45, 26, 1], ![113, -69, 235], ![2269, -617, -43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-122, -26, 167]], ![![-1, 0, 1], ![-171, -37, 235], ![45, 3, -43]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [83, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 166], [0, 1]]
 g := ![![[53, 58], [146, 141], [0, 33], [29], [54], [120, 76], [1]], ![[87, 109], [125, 26], [123, 134], [29], [54], [130, 91], [1]]]
 h' := ![![[110, 166], [73, 15], [0, 59], [136, 37], [120, 14], [60, 87], [84, 110], [0, 1]], ![[0, 1], [53, 152], [144, 108], [31, 130], [157, 153], [111, 80], [160, 57], [110, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [147, 137]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [83, 57, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2161, 80, -2412]
  a := ![-1, -1, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1775, 376, -2412]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-68, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-68, 1, 0]] 
 ![![167, 0, 0], ![99, 1, 0], ![43, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-68, 1, 0], ![1, -68, 9], ![87, -24, -67]]]
  hmulB := by decide  
  f := ![![![-2058, 200111, -26487], ![2171, 491481, 0]], ![![-1199, 118584, -15696], ![1337, 291248, 0]], ![![-490, 51525, -6820], ![657, 126549, 0]]]
  g := ![![![1, 0, 0], ![-99, 167, 0], ![-43, 0, 167]], ![![-1, 1, 0], ![38, -68, 9], ![32, -24, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-45, 26, 1]] ![![167, 0, 0], ![-68, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-11356, 167, 0]], ![![-7515, 4342, 167], ![3173, -1837, 167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-68, 1, 0]]], ![![![-45, 26, 1]], ![![19, -11, 1]]]]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [26, 108, 99, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [144, 7, 116], [103, 165, 57], [0, 1]]
 g := ![![[61, 117, 4], [47, 24], [76, 123, 37], [78, 100, 122], [145, 85], [5, 74, 1], []], ![[42, 69, 38, 135], [0, 85], [48, 138, 170, 56], [102, 154, 172, 21], [121, 130], [139, 106, 77, 158], [23, 135]], ![[13, 150, 48, 23], [145, 14], [85, 154, 2, 73], [91, 5, 17, 150], [41, 6], [25, 148, 141, 25], [82, 135]]]
 h' := ![![[144, 7, 116], [128, 88, 171], [100, 67, 102], [48, 26, 146], [155, 143, 45], [43, 131, 137], [0, 0, 1], [0, 1]], ![[103, 165, 57], [31, 95, 17], [107, 52, 36], [172, 155, 118], [23, 8, 139], [125, 16, 87], [70, 1, 165], [144, 7, 116]], ![[0, 1], [23, 163, 158], [81, 54, 35], [131, 165, 82], [6, 22, 162], [42, 26, 122], [0, 172, 7], [103, 165, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 62], []]
 b := ![[], [41, 45, 80], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [26, 108, 99, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19431014, 6232498, -666050]
  a := ![2, 19, 17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-112318, 36026, -3850]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [18, 83, 82, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 41, 68], [96, 137, 111], [0, 1]]
 g := ![![[169, 2, 66], [136, 56, 16], [138, 158], [35, 155], [97, 110, 142], [18, 97, 1], []], ![[49, 168, 132, 46], [47, 34, 72, 14], [48, 89], [123, 64], [14, 70, 174, 106], [13, 16, 94, 22], [160, 149]], ![[22, 119, 87, 26], [168, 134, 172, 123], [132, 88], [141, 29], [23, 57, 88, 128], [80, 107, 148, 73], [117, 149]]]
 h' := ![![[1, 41, 68], [58, 70, 31], [146, 8, 175], [53, 10, 64], [44, 75, 79], [34, 161, 121], [0, 0, 1], [0, 1]], ![[96, 137, 111], [21, 155, 57], [35, 124, 175], [177, 94, 140], [8, 123, 171], [170, 63, 138], [164, 51, 137], [1, 41, 68]], ![[0, 1], [37, 133, 91], [40, 47, 8], [140, 75, 154], [72, 160, 108], [132, 134, 99], [129, 128, 41], [96, 137, 111]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74, 118], []]
 b := ![[], [101, 45, 172], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [18, 83, 82, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8106910, 3471526, -3223074]
  a := ![-2, 3, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-45290, 19394, -18006]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-41, -16, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-41, -16, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![140, 165, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-41, -16, 1], ![71, -65, -143], ![-1385, 391, -81]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-140, -165, 181]], ![![-1, -1, 1], ![111, 130, -143], ![55, 76, -81]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [116, 163, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 180], [0, 1]]
 g := ![![[159, 142], [138], [165, 5], [38], [97, 55], [27, 143], [1]], ![[0, 39], [138], [74, 176], [38], [1, 126], [67, 38], [1]]]
 h' := ![![[18, 180], [45, 88], [46, 92], [112, 27], [151, 20], [126, 69], [65, 18], [0, 1]], ![[0, 1], [0, 93], [73, 89], [55, 154], [149, 161], [101, 112], [27, 163], [18, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [150]]
 b := ![[], [49, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [116, 163, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5847, 1571, -4725]
  a := ![2, 1, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3687, 4316, -4725]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-38, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-38, 1, 0]] 
 ![![181, 0, 0], ![143, 1, 0], ![81, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-38, 1, 0], ![1, -38, 9], ![87, -24, -37]]]
  hmulB := by decide  
  f := ![![![-9225, 383777, -90900], ![4163, 1828100, 0]], ![![-7294, 303184, -71811], ![3259, 1444199, 0]], ![![-4109, 171745, -40679], ![1955, 818100, 0]]]
  g := ![![![1, 0, 0], ![-143, 181, 0], ![-81, 0, 181]], ![![-1, 1, 0], ![26, -38, 9], ![36, -24, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-41, -16, 1]] ![![181, 0, 0], ![-38, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-6878, 181, 0]], ![![-7421, -2896, 181], ![1629, 543, -181]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-38, 1, 0]]], ![![![-41, -16, 1]], ![![9, 3, -1]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0]] 
 ![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [121, 138, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [144, 23, 190], [42, 167, 1], [0, 1]]
 g := ![![[73, 106, 6], [44, 91, 5], [170, 130, 153], [52, 116, 4], [172, 144, 144], [78, 186, 1], []], ![[163, 104, 133, 22], [184, 15, 145, 119], [174, 71, 99, 110], [32, 14, 158, 152], [91, 80, 8, 74], [51, 160, 79, 188], [140, 1]], ![[14, 86, 43, 133], [155, 131, 127, 103], [159, 146, 117, 17], [45, 179, 42, 97], [150, 14, 77, 125], [109, 86, 95, 147], [138, 1]]]
 h' := ![![[144, 23, 190], [24, 33, 31], [58, 86, 14], [11, 38, 150], [7, 34, 2], [112, 155, 179], [0, 0, 1], [0, 1]], ![[42, 167, 1], [21, 139, 178], [73, 170, 151], [164, 166, 182], [80, 169, 109], [182, 176, 133], [167, 171, 167], [144, 23, 190]], ![[0, 1], [103, 19, 173], [110, 126, 26], [27, 178, 50], [26, 179, 80], [178, 51, 70], [155, 20, 23], [42, 167, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 16], []]
 b := ![[], [154, 53, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [121, 138, 5, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-28336569, 21392000, -37382520]
  a := ![-5, 0, -40]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-148359, 112000, -195720]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![18, 1, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![18, 1, 0]] 
 ![![193, 0, 0], ![18, 1, 0], ![7, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![18, 1, 0], ![1, 18, 9], ![87, -24, 19]]]
  hmulB := by decide  
  f := ![![![-9631, -176283, -88146], ![-1737, 1890242, 0]], ![![-913, -16434, -8217], ![1, 176209, 0]], ![![-355, -6394, -3197], ![-2, 68558, 0]]]
  g := ![![![1, 0, 0], ![-18, 193, 0], ![-7, 0, 193]], ![![0, 1, 0], ![-2, 18, 9], ![2, -24, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N0 : Nat.card (O ⧸ I193N0) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N0)

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := prime_ideal_of_norm_prime hp193.out _ NI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-212, 66, -15]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-212, 66, -15]] 
 ![![193, 0, 0], ![79, 1, 0], ![143, 0, 1]] where
  M :=![![![-212, 66, -15], ![-1239, 148, 579], ![5637, -1689, 214]]]
  hmulB := by decide  
  f := ![![![1009603, 11211, 40434]], ![![431542, 4792, 17283]], ![![754568, 8379, 30220]]]
  g := ![![![-17, 66, -15], ![-496, 148, 579], ![562, -1689, 214]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![95, 1, 0]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![193, 0, 0], ![95, 1, 0]] 
 ![![193, 0, 0], ![95, 1, 0], ![91, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![95, 1, 0], ![1, 95, 9], ![87, -24, 96]]]
  hmulB := by decide  
  f := ![![![-9180, -1422659, -134784], ![-11773, 2890368, 0]], ![![-4521, -700215, -66339], ![-5789, 1422603, 0]], ![![-4385, -670788, -63551], ![-5436, 1362816, 0]]]
  g := ![![![1, 0, 0], ![-95, 193, 0], ![-91, 0, 193]], ![![0, 1, 0], ![-51, 95, 9], ![-33, -24, 96]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![18, 1, 0]] ![![-212, 66, -15]]
  ![![193, 0, 0], ![8, -75, 1]] where
 M := ![![![-40916, 12738, -2895]], ![![-5055, 1336, 309]]]
 hmul := by decide  
 g := ![![![![-212, 66, -15], ![0, 0, 0]]], ![![![-31, 52, 1], ![116, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![8, -75, 1]] ![![193, 0, 0], ![95, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![18335, 193, 0]], ![![1544, -14475, 193], ![772, -7141, -579]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![95, 1, 0]]], ![![![8, -75, 1]], ![![4, -37, -3]]]]
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


lemma PB230I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB230I3 : PrimesBelowBoundCertificateInterval O 137 193 230 where
  m := 11
  g := ![1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB230I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
    · exact ![I191N0]
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
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![157, 157, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![5177717]
    · exact ![5735339]
    · exact ![32761, 181]
    · exact ![6967871]
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
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
  β := ![I151N1, I157N0, I157N1, I163N1, I167N1, I181N1, I193N0, I193N1, I193N2]
  Il := ![[], [], [I151N1], [I157N0, I157N0, I157N1], [I163N1], [I167N1], [], [], [I181N1], [], [I193N0, I193N1, I193N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
