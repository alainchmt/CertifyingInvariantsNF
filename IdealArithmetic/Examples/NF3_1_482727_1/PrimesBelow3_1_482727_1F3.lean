
import IdealArithmetic.Examples.NF3_1_482727_1.RI3_1_482727_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [18, 97, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 126, 132], [101, 12, 7], [0, 1]]
 g := ![![[91, 11, 125], [25, 51, 118], [85, 24], [31, 126, 49], [57, 116], [131, 1], []], ![[22, 79, 49, 56], [55, 86, 2, 33], [119, 38], [33, 127, 18, 102], [89, 9], [121, 5], [68, 49]], ![[117, 74, 35, 80], [74, 79, 87, 79], [1, 89], [48, 6, 10, 49], [94, 45], [85, 30], [54, 49]]]
 h' := ![![[30, 126, 132], [106, 2, 79], [3, 113, 37], [137, 96, 118], [111, 102, 132], [5, 63, 106], [0, 0, 1], [0, 1]], ![[101, 12, 7], [7, 58, 100], [23, 36, 70], [91, 88, 49], [18, 46, 36], [77, 89, 136], [93, 82, 12], [30, 126, 132]], ![[0, 1], [66, 79, 99], [107, 129, 32], [60, 94, 111], [20, 130, 110], [105, 126, 36], [55, 57, 126], [101, 12, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [116, 2], []]
 b := ![[], [37, 58, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [18, 97, 8, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2701604, -774230, -458283]
  a := ![4, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19436, -5570, -3297]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [127, 51, 88, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 120, 90], [145, 28, 59], [0, 1]]
 g := ![![[91, 87, 47], [13, 25], [54, 0, 123], [75, 124], [7, 133, 45], [61, 1], []], ![[77, 133, 62, 41], [35, 86], [9, 50, 31, 111], [52, 1], [71, 133, 111, 48], [105, 39], [11, 54]], ![[124, 98, 128, 8], [55, 127], [97, 85, 4, 94], [75, 132], [91, 52, 58, 146], [127, 96], [42, 54]]]
 h' := ![![[65, 120, 90], [4, 78, 135], [145, 32, 144], [36, 18, 102], [5, 37, 78], [1, 40, 94], [0, 0, 1], [0, 1]], ![[145, 28, 59], [50, 20, 72], [5, 36, 58], [6, 136, 6], [90, 70, 1], [84, 57, 123], [146, 135, 28], [65, 120, 90]], ![[0, 1], [91, 51, 91], [85, 81, 96], [37, 144, 41], [18, 42, 70], [142, 52, 81], [46, 14, 120], [145, 28, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 41], []]
 b := ![[], [129, 112, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [127, 51, 88, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9730892, 2705244, 1644364]
  a := ![-7, -3, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![65308, 18156, 11036]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49488853776953537051706, -1902602512276709363025, 2471436646415550978655]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![49488853776953537051706, -1902602512276709363025, 2471436646415550978655]] 
 ![![151, 0, 0], ![65, 1, 0], ![24, 0, 1]] where
  M :=![![![49488853776953537051706, -1902602512276709363025, 2471436646415550978655], ![-243907293751140520755080, 9377033300165879777596, -12180549317659282309915], ![122962627640312218263185, -4727306987529205508400, 6140662409751302667176]]]
  hmulB := by decide  
  f := ![![![-257446397104, 17712365400, 138748679495]], ![![-203978606205, -9818427569, 62619687515]], ![![-78494208356, -12961878375, 5880581256]]]
  g := ![![![753930712324280941461, -1902602512276709363025, 2471436646415550978655], ![-3715770030715893581860, 9377033300165879777596, -12180549317659282309915], ![1873256185401849750311, -4727306987529205508400, 6140662409751302667176]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3137899158704279, -120636756905491, 156704356268396]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![3137899158704279, -120636756905491, 156704356268396]] 
 ![![151, 0, 0], ![86, 1, 0], ![127, 0, 1]] where
  M :=![![![3137899158704279, -120636756905491, 156704356268396], ![-15465229712391523, 594561859047038, -772322099612627], ![7796590471939503, -299740476632593, 389355944598961]]]
  hmulB := by decide  
  f := ![![![-157624293, -15635977, 32423809]], ![![-111149576, -13495941, 17964049]], ![![-128125286, -14611355, 22583752]]]
  g := ![![![-42309887374237, -120636756905491, 156704356268396], ![208525543446138, 594561859047038, -772322099612627], ![-105125387428646, -299740476632593, 389355944598961]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3263468079, -125464263, 162975175]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![3263468079, -125464263, 162975175]] 
 ![![151, 0, 0], ![150, 1, 0], ![33, 0, 1]] where
  M :=![![![3263468079, -125464263, 162975175], ![-16084099886, 618354367, -803228017], ![8108585663, -311735154, 404936753]]]
  hmulB := by decide  
  f := ![![![-259267, -43911, 17246]], ![![-268213, -46988, 14743]], ![![-30488, -6366, -357]]]
  g := ![![![110628654, -125464263, 162975175], ![-545236625, 618354367, -803228017], ![274873814, -311735154, 404936753]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![49488853776953537051706, -1902602512276709363025, 2471436646415550978655]] ![![3137899158704279, -120636756905491, 156704356268396]]
  ![![203983996945119710428919705051130395514, -7842179307712393692856641222735590011, 10186809490569704410029959783328777706]] where
 M := ![![![203983996945119710428919705051130395514, -7842179307712393692856641222735590011, 10186809490569704410029959783328777706]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![203983996945119710428919705051130395514, -7842179307712393692856641222735590011, 10186809490569704410029959783328777706]] ![![3263468079, -125464263, 162975175]]
  ![![151, 0, 0]] where
 M := ![![![874430275353345999015882283292969825852837265430, -33617534287546099687734154143118027310497620943, 43668399292163489219306373533656462212300331755]]]
 hmul := by decide  
 g := ![![![![5790928975849973503416438962205098184455875930, -222632677400967547600888438033894220599321993, 289194697299095955094744195587128888823181005]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [145, 143, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 12, 121], [109, 144, 36], [0, 1]]
 g := ![![[27, 12, 1], [82, 143], [75, 66, 153], [33], [109, 123, 141], [119, 1], []], ![[102, 89, 66, 25], [98, 82], [14, 139, 81, 93], [146, 82, 52, 51], [150, 76, 41, 76], [15, 12], [128, 40]], ![[67, 88, 122, 58], [79, 147], [101, 17, 137, 39], [5, 69, 70, 106], [88, 72, 124, 126], [23, 144], [56, 40]]]
 h' := ![![[10, 12, 121], [79, 25, 1], [115, 88, 92], [82, 26, 101], [52, 87], [15, 108, 45], [0, 0, 1], [0, 1]], ![[109, 144, 36], [81, 143, 29], [2, 114, 32], [100, 155, 106], [137, 102, 8], [140, 40, 80], [66, 0, 144], [10, 12, 121]], ![[0, 1], [128, 146, 127], [114, 112, 33], [11, 133, 107], [115, 125, 149], [11, 9, 32], [150, 0, 12], [109, 144, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106, 93], []]
 b := ![[], [143, 87, 68], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [145, 143, 38, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-654275677, -169082092, -73820615]
  a := ![2, 1, -70]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4167361, -1076956, -470195]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def PBC157 : ContainsPrimesAboveP 157 ![I157N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![157, 0, 0]]) timesTableT_eq_Table B_one_repr 157 (by decide) 𝕀

instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![253, 620, 1128]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![253, 620, 1128]] 
 ![![163, 0, 0], ![0, 163, 0], ![131, 15, 1]] where
  M :=![![![253, 620, 1128], ![-115788, -19543, 7836], ![-94204, -27460, -16555]]]
  hmulB := by decide  
  f := ![![![3304975, -127060, 165048]], ![![-16288668, 626219, -813444]], ![![1207567, -46425, 60305]]]
  g := ![![![-905, -100, 1128], ![-7008, -841, 7836], ![12727, 1355, -16555]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [36, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 162], [0, 1]]
 g := ![![[33, 77], [76, 121], [93], [140], [4], [132, 90], [1]], ![[0, 86], [94, 42], [93], [140], [4], [140, 73], [1]]]
 h' := ![![[116, 162], [35, 136], [136, 11], [77, 147], [155, 38], [138, 2], [127, 116], [0, 1]], ![[0, 1], [0, 27], [108, 152], [14, 16], [162, 125], [44, 161], [54, 47], [116, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [151]]
 b := ![[], [22, 157]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [36, 47, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-425, -5409, -10108]
  a := ![8, 3, -23]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8121, 897, -10108]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3304975, 127060, -165048]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-3304975, 127060, -165048]] 
 ![![163, 0, 0], ![26, 1, 0], ![18, 0, 1]] where
  M :=![![![-3304975, 127060, -165048], ![16288668, -626219, 813444], ![-8211716, 315700, -410087]]]
  hmulB := by decide  
  f := ![![![-253, -620, -1128]], ![![670, 21, -228]], ![![550, 100, -23]]]
  g := ![![![-22317, 127060, -165048], ![109990, -626219, 813444], ![-55450, 315700, -410087]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![253, 620, 1128]] ![![-3304975, 127060, -165048]]
  ![![163, 0, 0]] where
 M := ![![![-163, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-194943914695, 7494632701, -9735354489]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-194943914695, 7494632701, -9735354489]] 
 ![![167, 0, 0], ![0, 167, 0], ![127, 59, 1]] where
  M :=![![![-194943914695, 7494632701, -9735354489], ![960786905286, -36937521083, 47980985331], ![-484367977109, 18621561418, -24188977469]]]
  hmulB := by decide  
  f := ![![![-155207, -24601, 13668]], ![![-1306665, -362962, -194073]], ![![-567081, -145664, -60704]]]
  g := ![![![6236204224, 3484314656, -9735354489], ![-30735318753, -17172548836, 47980985331], ![15494803362, 8657312767, -24188977469]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [160, 52, 1] where
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
 g := ![![[88, 54], [67, 7], [44, 25], [9], [114], [113, 32], [1]], ![[119, 113], [37, 160], [80, 142], [9], [114], [119, 135], [1]]]
 h' := ![![[115, 166], [135, 80], [141, 72], [66, 162], [62, 164], [123, 75], [7, 115], [0, 1]], ![[0, 1], [150, 87], [71, 95], [159, 5], [51, 3], [64, 92], [39, 52], [115, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [155, 128]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [160, 52, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1227, -1693, -3063]
  a := ![4, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2322, 1072, -3063]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-155207, -24601, 13668]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-155207, -24601, 13668]] 
 ![![167, 0, 0], ![135, 1, 0], ![105, 0, 1]] where
  M :=![![![-155207, -24601, 13668], ![-1306665, -362962, -194073], ![2101997, 213197, -423097]]]
  hmulB := by decide  
  f := ![![![-194943914695, 7494632701, -9735354489]], ![![-151836177117, 5837352656, -7582586052]], ![![-125469934252, 4823700569, -6265875442]]]
  g := ![![![10364, -24601, 13668], ![407610, -362962, -194073], ![106261, 213197, -423097]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-194943914695, 7494632701, -9735354489]] ![![-155207, -24601, 13668]]
  ![![167, 0, 0]] where
 M := ![![![167, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [35, 172, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 75, 64], [55, 97, 109], [0, 1]]
 g := ![![[37, 1, 95], [164, 43], [164, 119, 56], [149, 139, 135], [92, 136], [150, 144, 1], []], ![[82, 21, 129, 85], [0, 88], [122, 37, 48, 36], [55, 119, 123, 14], [80, 23], [8, 46, 38, 136], [152, 117]], ![[37, 160, 53, 77], [120, 167], [137, 0, 151, 40], [136, 157, 168, 81], [33, 89], [93, 43, 114, 13], [107, 117]]]
 h' := ![![[89, 75, 64], [65, 25, 152], [142, 84, 133], [148, 73, 70], [34, 160, 57], [113, 127, 84], [0, 0, 1], [0, 1]], ![[55, 97, 109], [88, 164, 82], [112, 67, 112], [145, 164, 44], [84, 135, 26], [156, 107, 14], [6, 65, 97], [89, 75, 64]], ![[0, 1], [125, 157, 112], [0, 22, 101], [127, 109, 59], [145, 51, 90], [75, 112, 75], [145, 108, 75], [55, 97, 109]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 101], []]
 b := ![[], [22, 26, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [35, 172, 29, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![572149233, 147772967, 64460492]
  a := ![-22, -1, 67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3307221, 854179, 372604]
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


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [25, 131, 145, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [140, 82, 131], [73, 96, 48], [0, 1]]
 g := ![![[66, 78, 83], [97, 147, 82], [117, 25], [1, 49], [94, 2, 80], [130, 34, 1], []], ![[44, 48, 4, 24], [89, 145, 178, 73], [118, 61], [60, 45], [123, 9, 107, 131], [157, 34, 51, 120], [117, 156]], ![[114, 96, 15, 158], [51, 70, 116, 16], [122, 153], [70, 101], [70, 66, 14, 65], [3, 141, 78, 15], [21, 156]]]
 h' := ![![[140, 82, 131], [81, 54, 21], [133, 127, 34], [146, 52, 5], [156, 55, 172], [151, 20, 120], [0, 0, 1], [0, 1]], ![[73, 96, 48], [174, 123, 140], [70, 43, 32], [48, 17, 132], [142, 38, 89], [46, 131, 178], [28, 153, 96], [140, 82, 131]], ![[0, 1], [13, 2, 18], [5, 9, 113], [38, 110, 42], [78, 86, 97], [100, 28, 60], [150, 26, 82], [73, 96, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [162, 3], []]
 b := ![[], [113, 51, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [25, 131, 145, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27387, 3222, -1969]
  a := ![0, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![153, 18, -11]
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


def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![115845186100, -4453676440, 5785222659]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![115845186100, -4453676440, 5785222659]] 
 ![![181, 0, 0], ![8, 1, 0], ![94, 0, 1]] where
  M :=![![![115845186100, -4453676440, 5785222659], ![-570946459239, 21950077337, -28512642642], ![287835085988, -11065840405, 14374270676]]]
  hmulB := by decide  
  f := ![![![1719802, 336545, -24603]], ![![84164, 24828, 15375]], ![![709167, 145210, 2618]]]
  g := ![![![-2167604046, -4453676440, 5785222659], ![10683101273, 21950077337, -28512642642], ![-5385743836, -11065840405, 14374270676]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23610751687, -7274916810, -4927808109]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-23610751687, -7274916810, -4927808109]] 
 ![![181, 0, 0], ![164, 1, 0], ![26, 0, 1]] where
  M :=![![![-23610751687, -7274916810, -4927808109], ![519533369439, 67436902976, -75329867508], ![872745224862, 197590707405, 40684344437]]]
  hmulB := by decide  
  f := ![![![-17628107998070778841252, 677713868964844061175, -880334636760001041864]], ![![-15492425718109072690169, 595607411426070833381, -773680247963958985629]], ![![-2774201872298394866735, 106654388796042056235, -138541583578680116782]]]
  g := ![![![7169053127, -7274916810, -4927808109], ![-47411835157, 67436902976, -75329867508], ![-180054827320, 197590707405, 40684344437]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![115845186100, -4453676440, 5785222659]] ![![115845186100, -4453676440, 5785222659]]
  ![![17628107998070778841252, -677713868964844061175, 880334636760001041864]] where
 M := ![![![17628107998070778841252, -677713868964844061175, 880334636760001041864]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI181N1 : IdealMulLeCertificate' Table 
  ![![17628107998070778841252, -677713868964844061175, 880334636760001041864]] ![![-23610751687, -7274916810, -4927808109]]
  ![![181, 0, 0]] where
 M := ![![![-181, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N0, I181N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N0
    exact isPrimeI181N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![146261, 21524, -16171]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![146261, 21524, -16171]] 
 ![![191, 0, 0], ![21, 1, 0], ![144, 0, 1]] where
  M :=![![![146261, 21524, -16171], ![1568699, 399644, 161374], ![-1721136, -123343, 448045]]]
  hmulB := by decide  
  f := ![![![-198962849262, 7649140927, -9936057100]], ![![-16741494713, 643627958, -836057827]], ![![-152591643605, 5866396619, -7620313488]]]
  g := ![![![10591, 21524, -16171], ![-157391, 399644, 161374], ![-333243, -123343, 448045]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N0 : Nat.card (O ⧸ I191N0) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N0)

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := prime_ideal_of_norm_prime hp191.out _ NI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, -3, 4]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![79, -3, 4]] 
 ![![191, 0, 0], ![79, 1, 0], ![79, 0, 1]] where
  M :=![![![79, -3, 4], ![-395, 14, -19], ![191, -9, 9]]]
  hmulB := by decide  
  f := ![![![-45, -9, 1]], ![![-19, -4, 0]], ![![-14, -3, 0]]]
  g := ![![![0, -3, 4], ![0, 14, -19], ![1, -9, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1918191188, 73744997, -95793045]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![-1918191188, 73744997, -95793045]] 
 ![![191, 0, 0], ![90, 1, 0], ![1, 0, 1]] where
  M :=![![![-1918191188, 73744997, -95793045], ![9453862554, -363454420, 472118883], ![-4766039437, 183230726, -238012474]]]
  hmulB := by decide  
  f := ![![![-36022, 8092, 30549]], ![![-33255, 863, 15096]], ![![-8946, -3077, -2503]]]
  g := ![![![-44290303, 73744997, -95793045], ![218286081, -363454420, 472118883], ![-110046033, 183230726, -238012474]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![146261, 21524, -16171]] ![![79, -3, 4]]
  ![![-36022, 8092, 30549]] where
 M := ![![![-36022, 8092, 30549]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![-36022, 8092, 30549]] ![![-1918191188, 73744997, -95793045]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![76187435, 14751187, -1402920]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![76187435, 14751187, -1402920]] 
 ![![193, 0, 0], ![0, 193, 0], ![29, 63, 1]] where
  M :=![![![76187435, 14751187, -1402920], ![97441359, 85285888, 129954843], ![-1450588127, -229726379, 128136529]]]
  hmulB := by decide  
  f := ![![![-211307218533193, 8123721083851, -10552525744257]], ![![1041433936918404, -40038001964675, 52008438266145]], ![![305478775024700, -11744153288106, 15255383418271]]]
  g := ![![![605555, 534379, -1402920], ![-19022016, -41978597, 129954843], ![-26769676, -43017242, 128136529]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [183, 174, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 192], [0, 1]]
 g := ![![[137, 161], [108], [54], [170], [72], [32], [19, 1]], ![[108, 32], [108], [54], [170], [72], [32], [38, 192]]]
 h' := ![![[19, 192], [178, 136], [177, 84], [71, 132], [109, 154], [136, 119], [190, 178], [0, 1]], ![[0, 1], [60, 57], [36, 109], [70, 61], [140, 39], [81, 74], [98, 15], [19, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [167]]
 b := ![[], [27, 180]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [183, 174, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4862, -5511, -3828]
  a := ![-7, -2, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![550, 1221, -3828]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211307218533193, -8123721083851, 10552525744257]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![211307218533193, -8123721083851, 10552525744257]] 
 ![![193, 0, 0], ![10, 1, 0], ![54, 0, 1]] where
  M :=![![![211307218533193, -8123721083851, 10552525744257], ![-1041433936918404, 40038001964675, -52008438266145], ![525025108629755, -20184627738388, 26219364457379]]]
  hmulB := by decide  
  f := ![![![-76187435, -14751187, 1402920]], ![![-4452413, -1206206, -600651]], ![![-13800691, -2936983, -271393]]]
  g := ![![![-1436745910975, -8123721083851, 10552525744257], ![7081045128532, 40038001964675, -52008438266145], ![-3569814998367, -20184627738388, 26219364457379]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![76187435, 14751187, -1402920]] ![![211307218533193, -8123721083851, 10552525744257]]
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


lemma PB197I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 196 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 196 (by omega)

def PB197I3 : PrimesBelowBoundCertificateInterval O 137 196 197 where
  m := 11
  g := ![1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB197I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0]
    · exact ![I181N0, I181N0, I181N1]
    · exact ![I191N0, I191N1, I191N2]
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
    · exact ![3307949]
    · exact ![151, 151, 151]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![5177717]
    · exact ![5735339]
    · exact ![181, 181, 181]
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
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
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
      exact NI193N1
  β := ![I151N0, I151N1, I151N2, I163N1, I167N1, I181N0, I181N1, I191N0, I191N1, I191N2, I193N1]
  Il := ![[], [], [I151N0, I151N1, I151N2], [], [I163N1], [I167N1], [], [], [I181N0, I181N0, I181N1], [I191N0, I191N1, I191N2], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
