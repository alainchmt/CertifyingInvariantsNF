
import IdealArithmetic.Examples.NF3_1_975819_1.RI3_1_975819_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [88, 9, 114, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 42, 56], [114, 96, 83], [0, 1]]
 g := ![![[110, 57, 47], [88, 137, 122], [96, 86], [98, 43, 30], [37, 125], [25, 1], []], ![[91, 64, 47, 40], [82, 87, 125, 105], [112, 42], [115, 110, 101, 68], [28, 124], [77, 42], [121, 78]], ![[57, 96, 25, 80], [18, 115, 96, 100], [7, 28], [91, 24, 5, 81], [17, 51], [37, 96], [94, 78]]]
 h' := ![![[50, 42, 56], [40, 120, 66], [67, 118, 119], [133, 52, 15], [100, 53, 13], [24, 104, 60], [0, 0, 1], [0, 1]], ![[114, 96, 83], [86, 36, 129], [42, 91, 101], [53, 99, 43], [103, 2, 46], [64, 59, 47], [53, 0, 96], [50, 42, 56]], ![[0, 1], [105, 122, 83], [76, 69, 58], [54, 127, 81], [0, 84, 80], [84, 115, 32], [137, 0, 42], [114, 96, 83]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 13], []]
 b := ![[], [90, 6, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [88, 9, 114, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1225702, 273830, -51430]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8818, 1970, -370]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![182846659547, -4020212096, -4094918563]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![182846659547, -4020212096, -4094918563]] 
 ![![149, 0, 0], ![0, 149, 0], ![123, 84, 1]] where
  M :=![![![182846659547, -4020212096, -4094918563], ![1220136318840, 15104411398, -16006141917], ![526605973210, 117571271977, 23070129123]]]
  hmulB := by decide  
  f := ![![![14968611985938524187, -2608711221057533807, 846975972898489994]], ![![-245487465535837970610, 42783252486864566339, -13890532078186159029]], ![![-119935699340250776311, 20902245643631572256, -6786377770323405580]]]
  g := ![![![4607527804, 2281563404, -4094918563], ![21401958219, 9124968674, -16006141917], ![-15510200731, -12216909895, 23070129123]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [45, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 148], [0, 1]]
 g := ![![[138, 53], [114], [114, 31], [143], [37, 33], [69], [1]], ![[0, 96], [114], [112, 118], [143], [131, 116], [69], [1]]]
 h' := ![![[48, 148], [9, 65], [85, 76], [52, 110], [123, 21], [112, 35], [104, 48], [0, 1]], ![[0, 1], [0, 84], [8, 73], [117, 39], [88, 128], [4, 114], [24, 101], [48, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [64, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [45, 101, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8677, -7586, 6824]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5575, -3898, 6824]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14968611985938524187, 2608711221057533807, -846975972898489994]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-14968611985938524187, 2608711221057533807, -846975972898489994]] 
 ![![149, 0, 0], ![28, 1, 0], ![70, 0, 1]] where
  M :=![![![-14968611985938524187, 2608711221057533807, -846975972898489994], ![245487465535837970610, -42783252486864566339, 13890532078186159029], ![-909388629042585385900, 158487127805442648071, -51456362122935657754]]]
  hmulB := by decide  
  f := ![![![-182846659547, 4020212096, 4094918563]], ![![-42549280444, 654104210, 876938669]], ![![-89435383500, 1099621307, 1768954163]]]
  g := ![![![-192779919950705847, 2608711221057533807, -846975972898489994], ![3161619393926273128, -42783252486864566339, 13890532078186159029], ![-11711965496573714692, 158487127805442648071, -51456362122935657754]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![182846659547, -4020212096, -4094918563]] ![![-14968611985938524187, 2608711221057533807, -846975972898489994]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [104, 110, 92, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 36, 92], [135, 114, 59], [0, 1]]
 g := ![![[53, 11, 110], [93, 89, 31], [1, 37, 44], [9, 29], [144, 89, 136], [59, 1], []], ![[45, 136, 61, 52], [98, 118, 71, 135], [111, 77, 31, 108], [7, 45], [140, 150, 30, 112], [57, 10], [150, 8]], ![[32, 73, 3, 55], [131, 80, 132, 11], [142, 39, 95, 127], [73, 45], [48, 18, 114, 76], [123, 88], [32, 8]]]
 h' := ![![[75, 36, 92], [143, 88, 67], [47, 84, 22], [95, 62, 78], [124, 126, 28], [55, 50, 49], [0, 0, 1], [0, 1]], ![[135, 114, 59], [100, 98, 30], [109, 89, 119], [117, 35, 100], [111, 73, 137], [42, 143, 69], [142, 148, 114], [75, 36, 92]], ![[0, 1], [83, 116, 54], [126, 129, 10], [30, 54, 124], [125, 103, 137], [29, 109, 33], [99, 3, 36], [135, 114, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 84], []]
 b := ![[], [138, 42, 91], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [104, 110, 92, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26858588648, 18548477751, -9835005537]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-177871448, 122837601, -65132487]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-70, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-70, 1, 0]] 
 ![![157, 0, 0], ![87, 1, 0], ![21, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-70, 1, 0], ![-2, -68, 5], ![-296, 39, -71]]]
  hmulB := by decide  
  f := ![![![-7143, -266706, 19610], ![1570, -615754, 0]], ![![-3925, -147770, 10865], ![943, -341161, 0]], ![![-959, -35674, 2623], ![202, -82362, 0]]]
  g := ![![![1, 0, 0], ![-87, 157, 0], ![-21, 0, 157]], ![![-1, 1, 0], ![37, -68, 5], ![-14, 39, -71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-65, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-65, 1, 0]] 
 ![![157, 0, 0], ![92, 1, 0], ![154, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-65, 1, 0], ![-2, -63, 5], ![-296, 39, -66]]]
  hmulB := by decide  
  f := ![![![25825, 879008, -69760], ![-5024, 2190464, 0]], ![![15181, 515043, -40875], ![-2825, 1283475, 0]], ![![25310, 862212, -68427], ![-4980, 2148608, 0]]]
  g := ![![![1, 0, 0], ![-92, 157, 0], ![-154, 0, 157]], ![![-1, 1, 0], ![32, -63, 5], ![40, 39, -66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-273748582941707703030417123, 47708565145484745466129066, -15489644102234937992542864]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![-273748582941707703030417123, 47708565145484745466129066, -15489644102234937992542864]] 
 ![![157, 0, 0], ![134, 1, 0], ![60, 0, 1]] where
  M :=![![![-273748582941707703030417123, 47708565145484745466129066, -15489644102234937992542864], ![4489517523970572154860429612, -782427572637900793807330687, 254032469829658665323188194], ![-16631057627625544612766147504, 2898440195523645918679405462, -941042912176589968198260749]]]
  hmulB := by decide  
  f := ![![![-587813437788935, -4901685107266, 8352258620764]], ![![-517385132772286, -5915315453295, 6919375611626]], ![![-206782430439628, -6655211166946, 1607096238183]]]
  g := ![![![-36543424626131002012351211, 47708565145484745466129066, -15489644102234937992542864], ![599317605526558972010518790, -782427572637900793807330687, 254032469829658665323188194], ![-2220124006988526749196884296, 2898440195523645918679405462, -941042912176589968198260749]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-70, 1, 0]] ![![157, 0, 0], ![-65, 1, 0]]
  ![![-587813437788935, -4901685107266, 8352258620764]] where
 M := ![![![24649, 0, 0], ![-10205, 157, 0]], ![![-10990, 157, 0], ![4548, -133, 5]]]
 hmul := by decide  
 g := ![![![![-42978527521848109375775488311, 7490244727841105038182263362, -2431874124050885264829229648]], ![![22283175415181572851837542607, -3883484307094409249105719977, 1260859336474929634838474354]]], ![![![23651918329890111366989628222, -4122027132821832976436365307, 1338307556986104324801188674]], ![![-12262864165892359573519776760, 2137156830701424570380426757, -693875378504407963815670567]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![-587813437788935, -4901685107266, 8352258620764]] ![![-273748582941707703030417123, 47708565145484745466129066, -15489644102234937992542864]]
  ![![157, 0, 0]] where
 M := ![![![157, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![29, 1, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![29, 1, 0]] 
 ![![163, 0, 0], ![29, 1, 0], ![48, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![29, 1, 0], ![-2, 31, 5], ![-296, 39, 28]]]
  hmulB := by decide  
  f := ![![![-8613, 135319, 21825], ![-652, -711495, 0]], ![![-1552, 24056, 3880], ![1, -126488, 0]], ![![-2552, 39848, 6427], ![-104, -209520, 0]]]
  g := ![![![1, 0, 0], ![-29, 163, 0], ![-48, 0, 163]], ![![0, 1, 0], ![-7, 31, 5], ![-17, 39, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N0)

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := prime_ideal_of_norm_prime hp163.out _ NI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![41, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![41, 1, 0]] 
 ![![163, 0, 0], ![41, 1, 0], ![136, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![41, 1, 0], ![-2, 43, 5], ![-296, 39, 40]]]
  hmulB := by decide  
  f := ![![![-127, 2752, 320], ![0, -10432, 0]], ![![-32, 688, 80], ![1, -2608, 0]], ![![-112, 2296, 267], ![24, -8704, 0]]]
  g := ![![![1, 0, 0], ![-41, 163, 0], ![-136, 0, 163]], ![![0, 1, 0], ![-15, 43, 5], ![-45, 39, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39417656471682619, -30592585446536474, -7609583449074673]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![-39417656471682619, -30592585446536474, -7609583449074673]] 
 ![![163, 0, 0], ![92, 1, 0], ![63, 0, 1]] where
  M :=![![![-39417656471682619, -30592585446536474, -7609583449074673], ![2313621871819176156, -397376581878667814, -145353343783607697], ![7822652773424699278, -683268741326919395, -313208408988133065]]]
  hmulB := by decide  
  f := ![![![25146290724675500216708080944086595, -4382464509271793505963673280929975, 1422864329126032469286708769965556]], ![![11662919228634257644418435567533878, -2032599167551888484918377702053217, 659928413522147160584491605289667]], ![![19091594059616102156087749762988639, -3327259447835381061659534737684354, 1080268595913672626130078267064226]]]
  g := ![![![19966281974855076, -30592585446536474, -7609583449074673], ![294659681368244785, -397376581878667814, -145353343783607697], ![554696360378856851, -683268741326919395, -313208408988133065]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![29, 1, 0]] ![![163, 0, 0], ![41, 1, 0]]
  ![![-25146290724675500216708080944086595, 4382464509271793505963673280929975, -1422864329126032469286708769965556]] where
 M := ![![![26569, 0, 0], ![6683, 163, 0]], ![![4727, 163, 0], ![1187, 72, 5]]]
 hmul := by decide  
 g := ![![![![6425078004884266897, 4986591427785445262, 1240362102199171699]], ![![-697497956480188777, 1651672585186663248, 457346265195669290]]], ![![![-1170509834140380205, 1284561559828225560, 366031263806773214]], ![![-974879020897036263, 419269058447469167, 129227351849153720]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![-25146290724675500216708080944086595, 4382464509271793505963673280929975, -1422864329126032469286708769965556]] ![![-39417656471682619, -30592585446536474, -7609583449074673]]
  ![![163, 0, 0]] where
 M := ![![![-163, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3439724734629070915387501, -493660084413843467665664, -189880610264342817968147]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![3439724734629070915387501, -493660084413843467665664, -189880610264342817968147]] 
 ![![167, 0, 0], ![0, 167, 0], ![102, 119, 1]] where
  M :=![![![3439724734629070915387501, -493660084413843467665664, -189880610264342817968147], ![57191980807073161053902840, -4952939234507985920701560, -2278419811804874520360173], ![115362726123674129918196730, -6530742404428926435095047, -3661839591530798335672715]]]
  hmulB := by decide  
  f := ![![![19503569480973172819866784527825724545733063307, -3399058015765640034838261105864247114579543053, 1103579593863379473514250592504407448484143656]], ![![-319861443752029044090541653169576110522147436070, 55745057610113692217246035423769120807455579785, -18098869672691579647705556121825643021381858921]], ![![-208917644626105962240279106718681449676052673168, 36409909237076213797692386885053121160976411970, -11821284797754247185528338615137339462271737761]]]
  g := ![![![136572137614323582922985, 132348099024209292637987, -189880610264342817968147], ![1734076656354313545692458, 1593886337546539413186581, -2278419811804874520360173], ![2927367451855182994950980, 2570228556812790871317114, -3661839591530798335672715]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [84, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 166], [0, 1]]
 g := ![![[104, 2], [16, 50], [161, 56], [21], [89], [58, 32], [1]], ![[0, 165], [88, 117], [88, 111], [21], [89], [64, 135], [1]]]
 h' := ![![[115, 166], [159, 154], [3, 102], [94, 35], [45, 122], [138, 16], [83, 115], [0, 1]], ![[0, 1], [0, 13], [43, 65], [111, 132], [47, 45], [141, 151], [115, 52], [115, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [143, 89]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [84, 52, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2367, -7008, 4989]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3033, -3597, 4989]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-99714877488653211685483, -515590736073736133506, 1502132535722060877438]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-99714877488653211685483, -515590736073736133506, 1502132535722060877438]] 
 ![![167, 0, 0], ![74, 1, 0], ![144, 0, 1]] where
  M :=![![![-99714877488653211685483, -515590736073736133506, 1502132535722060877438], ![-443600049101582547454636, -42162890067640309732413, -4080086216090741544968], ![395960328664799757662732, -120750918600253787995080, -39113985323697040454457]]]
  hmulB := by decide  
  f := ![![![-1156484504749144172760140251803044507200457301, 201550692031589657813060961567809619891741282, -65437903626073563581998494072937522919495702]], ![![-398882247078934570536556564736355724481716138, 69516705678052699648709889571891755752763759, -22570140745780969176171169218475395650685508]], ![![-1417926430614677945451556867805544522381913620, 247114468172022970896910509399975895064639920, -80231194395079458261442659417912325414846753]]]
  g := ![![![-1663881725527985054833, -515590736073736133506, 1502132535722060877438], ![19544827730663875180954, -42162890067640309732413, -4080086216090741544968], ![89604444261652418531380, -120750918600253787995080, -39113985323697040454457]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![3439724734629070915387501, -493660084413843467665664, -189880610264342817968147]] ![![-99714877488653211685483, -515590736073736133506, 1502132535722060877438]]
  ![![167, 0, 0]] where
 M := ![![![-199189281670097570952084510334873462654371527283, 41968903775900651768520022707517000356560975486, 14608085546799516488728111325148222941913862369]]]
 hmul := by decide  
 g := ![![![![-1192750189641302820072362337334571632660907349, 251310801053297315979161812619862277584197458, 87473566148500098734898870210468400849783607]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![27, -55, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![27, -55, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![27, 118, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![27, -55, 1], ![-186, -44, -276], ![16442, -2212, 122]]]
  hmulB := by decide  
  f := ![![![-26, 55, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -118, 173]], ![![0, -1, 1], ![42, 188, -276], ![76, -96, 122]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [111, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [80, 172], [0, 1]]
 g := ![![[85, 25], [136], [116, 109], [80, 119], [157], [152, 172], [1]], ![[9, 148], [136], [13, 64], [85, 54], [157], [72, 1], [1]]]
 h' := ![![[80, 172], [68, 5], [99, 84], [116, 121], [23, 43], [82, 26], [62, 80], [0, 1]], ![[0, 1], [122, 168], [72, 89], [108, 52], [3, 130], [86, 147], [61, 93], [80, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [132, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [111, 93, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4547, -778, 530]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-109, -366, 530]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-70, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-70, 1, 0]] 
 ![![173, 0, 0], ![103, 1, 0], ![51, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-70, 1, 0], ![-2, -68, 5], ![-296, 39, -71]]]
  hmulB := by decide  
  f := ![![![-9225, -339875, 24990], ![1903, -864654, 0]], ![![-5459, -202307, 14875], ![1212, -514675, 0]], ![![-2675, -100195, 7367], ![671, -254898, 0]]]
  g := ![![![1, 0, 0], ![-103, 173, 0], ![-51, 0, 173]], ![![-1, 1, 0], ![39, -68, 5], ![-4, 39, -71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![27, -55, 1]] ![![173, 0, 0], ![-70, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-12110, 173, 0]], ![![4671, -9515, 173], ![-2076, 3806, -346]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-70, 1, 0]]], ![![![27, -55, 1]], ![![-12, 22, -2]]]]
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


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [51, 166, 70, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 156, 82], [168, 22, 97], [0, 1]]
 g := ![![[124, 26, 59], [130, 153, 155], [171, 101], [122, 75], [12, 50, 85], [80, 109, 1], []], ![[135, 65, 56, 124], [21, 75, 72, 129], [116, 151], [52, 126], [106, 94, 24, 153], [8, 71, 132, 129], [77, 101]], ![[156, 138, 124, 8], [22, 22, 14, 113], [87, 61], [138, 85], [160, 11, 32, 78], [169, 66, 138, 119], [62, 101]]]
 h' := ![![[120, 156, 82], [172, 40, 43], [70, 4, 100], [119, 77, 97], [104, 49, 95], [37, 135, 62], [0, 0, 1], [0, 1]], ![[168, 22, 97], [114, 161, 109], [163, 45, 22], [107, 168, 35], [130, 104, 22], [41, 48, 83], [91, 175, 22], [120, 156, 82]], ![[0, 1], [176, 157, 27], [47, 130, 57], [3, 113, 47], [113, 26, 62], [108, 175, 34], [2, 4, 156], [168, 22, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 163], []]
 b := ![[], [143, 6, 153], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [51, 166, 70, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-59586594, 4109840, 2122940]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-332886, 22960, 11860]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [93, 41, 81, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [138, 162, 99], [143, 18, 82], [0, 1]]
 g := ![![[162, 61, 87], [159, 119], [167, 148, 170], [110, 170], [145, 138, 64], [4, 100, 1], []], ![[166, 6, 154, 20], [110, 39], [171, 86, 163, 36], [154, 82], [34, 165, 145, 64], [171, 101, 57, 39], [24, 27]], ![[22, 124, 132, 165], [97, 121], [136, 110, 169, 45], [42, 5], [163, 103, 40, 100], [152, 114, 110, 99], [41, 27]]]
 h' := ![![[138, 162, 99], [13, 171, 79], [35, 158, 149], [42, 169, 129], [90, 145, 129], [171, 129, 8], [0, 0, 1], [0, 1]], ![[143, 18, 82], [51, 143, 70], [67, 78, 43], [21, 165, 48], [15, 78, 25], [67, 37, 64], [160, 130, 18], [138, 162, 99]], ![[0, 1], [34, 48, 32], [154, 126, 170], [63, 28, 4], [118, 139, 27], [28, 15, 109], [165, 51, 162], [143, 18, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [152, 23], []]
 b := ![[], [93, 143, 157], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [93, 41, 81, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10720268, 2080957, -644179]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-59228, 11497, -3559]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def PBC181 : ContainsPrimesAboveP 181 ![I181N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![181, 0, 0]]) timesTableT_eq_Table B_one_repr 181 (by decide) 𝕀


def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![68008640314770426941225, -2675516226923486126677, -1841677576146688911790]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![68008640314770426941225, -2675516226923486126677, -1841677576146688911790]] 
 ![![191, 0, 0], ![55, 1, 0], ![22, 0, 1]] where
  M :=![![![68008640314770426941225, -2675516226923486126677, -1841677576146688911790], ![550487594993266890143194, -9167817608797412871939, -11535903558470741721595], ![493601035833588289786412, 19047264751812198149527, -2982946504173643403698]]]
  hmulB := by decide  
  f := ![![![247074518716628479206542451820971698567965987, -43059842156303022595627809648814044011474876, 13980333050587903315726655201760958699229005]], ![![49932144663629073403643981831046218504132427, -8702112540417359054612058352318070266053250, 2825333895027390921838221636916343192151790]], ![![107047992901710793549725045752856595315010020, -18656192072899863353334985796312256112818381, 6057146649263777525535198345439608282364603]]]
  g := ![![![1338633190946540942240, -2675516226923486126677, -1841677576146688911790], ![6850824302426601654319, -9167817608797412871939, -11535903558470741721595], ![-2556930379184620175687, 19047264751812198149527, -2982946504173643403698]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N0 : Nat.card (O ⧸ I191N0) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N0)

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := prime_ideal_of_norm_prime hp191.out _ NI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-28, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-28, 1, 0]] 
 ![![191, 0, 0], ![163, 1, 0], ![45, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-28, 1, 0], ![-2, -26, 5], ![-296, 39, -29]]]
  hmulB := by decide  
  f := ![![![-8437, -111154, 21375], ![764, -816525, 0]], ![![-7211, -94851, 18240], ![574, -696768, 0]], ![![-1991, -26188, 5036], ![158, -192375, 0]]]
  g := ![![![1, 0, 0], ![-163, 191, 0], ![-45, 0, 191]], ![![-1, 1, 0], ![21, -26, 5], ![-28, 39, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![68008640314770426941225, -2675516226923486126677, -1841677576146688911790]] ![![191, 0, 0], ![-28, 1, 0]]
  ![![191, 0, 0], ![-41, 44, 1]] where
 M := ![![![12989650300121151545773975, -511023599342385850195307, -351760417044017582151890], ![-1353754333820305064211106, 65746636745060198675017, 40031068573636547808525]]]
 hmul := by decide  
 g := ![![![![65035382517241284795404, 515297019205349346887, -1769159093280124469209], ![-13851030227513808532971, 0, 0]], ![![-6774892584597737387917, 8507048833281870571, 201956833272501754186], ![1457313418588712758999, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-41, 44, 1]] ![![191, 0, 0], ![-28, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-5348, 191, 0]], ![![-7831, 8404, 191], ![764, -1146, 191]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-28, 1, 0]]], ![![![-41, 44, 1]], ![![4, -6, 1]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-886637, 154522, -50169]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-886637, 154522, -50169]] 
 ![![193, 0, 0], ![0, 193, 0], ![18, 169, 1]] where
  M :=![![![-886637, 154522, -50169], ![14540980, -2534184, 822779], ![-53865890, 9387681, -3047919]]]
  hmulB := by decide  
  f := ![![![-4029, 147, 106]], ![![-31670, 399, 629]], ![![-28244, 356, 561]]]
  g := ![![![85, 44731, -50169], ![-1394, -733595, 822779], ![5164, 2717544, -3047919]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [40, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [186, 192], [0, 1]]
 g := ![![[5, 144], [192], [54], [54], [191], [81], [186, 1]], ![[155, 49], [192], [54], [54], [191], [81], [179, 192]]]
 h' := ![![[186, 192], [191, 181], [94, 81], [18, 61], [21, 61], [83, 34], [87, 9], [0, 1]], ![[0, 1], [82, 12], [106, 112], [170, 132], [173, 132], [38, 159], [24, 184], [186, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [160]]
 b := ![[], [87, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [40, 7, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13422, -2755, 4015]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-444, -3530, 4015]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4029, 147, 106]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-4029, 147, 106]] 
 ![![193, 0, 0], ![121, 1, 0], ![111, 0, 1]] where
  M :=![![![-4029, 147, 106], ![-31670, 399, 629], ![-26340, -1369, 64]]]
  hmulB := by decide  
  f := ![![![-886637, 154522, -50169]], ![![-480529, 83746, -27190]], ![![-789029, 137511, -44646]]]
  g := ![![![-174, 147, 106], ![-776, 399, 629], ![685, -1369, 64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-886637, 154522, -50169]] ![![-4029, 147, 106]]
  ![![193, 0, 0]] where
 M := ![![![193, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB280I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB280I3 : PrimesBelowBoundCertificateInterval O 137 193 280 where
  m := 11
  g := ![1, 2, 1, 3, 3, 2, 2, 1, 1, 3, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB280I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0]
    · exact ![I191N0, I191N1, I191N1]
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
    · exact ![3442951]
    · exact ![157, 157, 157]
    · exact ![163, 163, 163]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![5735339]
    · exact ![5929741]
    · exact ![191, 191, 191]
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
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
      exact NI163N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I149N1, I157N0, I157N1, I157N2, I163N0, I163N1, I163N2, I167N1, I173N1, I191N0, I191N1, I193N1]
  Il := ![[], [I149N1], [], [I157N0, I157N1, I157N2], [I163N0, I163N1, I163N2], [I167N1], [I173N1], [], [], [I191N0, I191N1, I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
