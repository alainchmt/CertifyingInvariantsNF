
import IdealArithmetic.Examples.NF3_1_317044_1.RI3_1_317044_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [34, 10, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 6, 35], [21, 30, 2], [0, 1]]
 g := ![![[26, 34, 26], [14, 33], [35, 13, 11], [25, 1], []], ![[35, 34, 25, 35], [7, 1], [27, 13], [36, 12], [2, 4]], ![[34, 2, 13, 14], [16, 10], [35, 6, 8, 22], [13, 36], [35, 4]]]
 h' := ![![[4, 6, 35], [4, 16, 27], [31, 23, 25], [1, 12, 23], [0, 0, 1], [0, 1]], ![[21, 30, 2], [33, 29, 1], [7, 28, 1], [0, 30], [22, 3, 30], [4, 6, 35]], ![[0, 1], [23, 29, 9], [30, 23, 11], [9, 32, 14], [28, 34, 6], [21, 30, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 14], []]
 b := ![[], [4, 30, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [34, 10, 12, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1204498, -614348, -276316]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32554, -16604, -7468]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [24, 36, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 7, 14], [28, 33, 27], [0, 1]]
 g := ![![[30, 29, 39], [6, 9], [24, 5], [30, 5, 1], []], ![[6, 38, 19, 13], [35, 23], [30, 40], [37, 28, 18, 35], [28, 32]], ![[1, 6], [24, 39], [33, 33], [16, 25, 13, 11], [15, 32]]]
 h' := ![![[18, 7, 14], [15, 15, 30], [35, 14, 3], [18, 30, 28], [0, 0, 1], [0, 1]], ![[28, 33, 27], [13, 18, 11], [22, 36, 8], [39, 14, 32], [21, 34, 33], [18, 7, 14]], ![[0, 1], [35, 8], [18, 32, 30], [20, 38, 22], [14, 7, 7], [28, 33, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 14], []]
 b := ![[], [1, 20, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [24, 36, 36, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![435871, 217013, 97211]
  a := ![-1, 1, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10631, 5293, 2371]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [41, 29, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 36, 39], [41, 6, 4], [0, 1]]
 g := ![![[11, 25, 13], [42, 12, 38], [36, 25], [27, 20, 1], []], ![[4, 1, 18, 19], [11, 31, 40, 30], [22, 21], [20, 3, 7, 28], [32, 16]], ![[6, 6, 11, 31], [7, 10, 30, 25], [6, 9], [35, 35, 0, 24], [24, 16]]]
 h' := ![![[22, 36, 39], [41, 21, 20], [21, 32, 34], [11, 31, 5], [0, 0, 1], [0, 1]], ![[41, 6, 4], [25, 25, 36], [7, 34, 33], [36, 41, 35], [32, 0, 6], [22, 36, 39]], ![[0, 1], [7, 40, 30], [5, 20, 19], [37, 14, 3], [9, 0, 36], [41, 6, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 31], []]
 b := ![[], [31, 6, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [41, 29, 23, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-172817, 1806, -6407]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4019, 42, -149]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-541948973419011119747199353896291456617920565746001562796423124208968467, 14922973579562297705653990591562993347474417197444149074008911970831348, -24034930253105156304592976810287342648972212718230421818087350939863222]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-541948973419011119747199353896291456617920565746001562796423124208968467, 14922973579562297705653990591562993347474417197444149074008911970831348, -24034930253105156304592976810287342648972212718230421818087350939863222]] 
 ![![47, 0, 0], ![24, 1, 0], ![21, 0, 1]] where
  M :=![![![-541948973419011119747199353896291456617920565746001562796423124208968467, 14922973579562297705653990591562993347474417197444149074008911970831348, -24034930253105156304592976810287342648972212718230421818087350939863222], ![1682445117717360941321508376720113985428054890276129527266114565790425540, -46327394777345695949685827098981610291001894183948977360667193440872679, 74614867897811488528269952957814966737372085987220745370044559854156740], ![-1381097174112833027660081016753432331408820181876316340633846751116279468, 38029551952226234151221863512762930136122634106342923973044673741458148, -61250368356907993655339817690544603638476311381393126434676105411704027]]]
  hmulB := by decide  
  f := ![![![-705510605100162446064046336796460813, -48014130977749284407005862552005540, 218355097365990657133558701279226218]], ![![-685470454000494568189068535588529676, -133467358018376759551284402684704759, 106392588976489986152561266339178756]], ![![-178675790968874303382654061195236643, -66063521151098265622911227243854736, -10365010802854718913414630542919885]]]
  g := ![![![-8412059659857403878434949256973810666572130029826006008357503016421131, 14922973579562297705653990591562993347474417197444149074008911970831348, -24034930253105156304592976810287342648972212718230421818087350939863222], ![26114688649353540106814876914501241083559288190622751726621094711363368, -46327394777345695949685827098981610291001894183948977360667193440872679, 74614867897811488528269952957814966737372085987220745370044559854156740], ![-21437206073855208096324884458687361239739592796155124699121717175861499, 38029551952226234151221863512762930136122634106342923973044673741458148, -61250368356907993655339817690544603638476311381393126434676105411704027]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, 0, 31]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-79, 0, 31]] 
 ![![47, 0, 0], ![30, 1, 0], ![2, 0, 1]] where
  M :=![![![-79, 0, 31], ![-2170, -699, 0], ![434, -434, -699]]]
  hmulB := by decide  
  f := ![![![488601, -13454, 21669]], ![![279600, -7699, 12400]], ![![47284, -1302, 2097]]]
  g := ![![![-3, 0, 31], ![400, -699, 0], ![316, -434, -699]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6294451435, -1573664442, 552942581]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![-6294451435, -1573664442, 552942581]] 
 ![![47, 0, 0], ![39, 1, 0], ![17, 0, 1]] where
  M :=![![![-6294451435, -1573664442, 552942581], ![-38705980670, -18926967497, -7868322210], ![117897707074, 23732092706, -17353303055]]]
  hmulB := by decide  
  f := ![![![-515177155015974603595, 14185791375516556124, -22847625138370146577]], ![![-393459048636959559145, 10834191548342352615, -17449540925933041189]], ![![-214274123053083175359, 5900199527885795398, -9502857012784343912]]]
  g := ![![![971881658, -1573664442, 552942581], ![17727813389, -18926967497, -7868322210], ![-10907399075, 23732092706, -17353303055]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-541948973419011119747199353896291456617920565746001562796423124208968467, 14922973579562297705653990591562993347474417197444149074008911970831348, -24034930253105156304592976810287342648972212718230421818087350939863222]] ![![-79, 0, 31]]
  ![![-43497395945397433762561549377200857700944231683098731822472096154615, 1197733591739941212512162174359769322698698542866317680840289526096, -1929068840455252689180394182643523960848082983595846058543513630299]] where
 M := ![![![-43497395945397433762561549377200857700944231683098731822472096154615, 1197733591739941212512162174359769322698698542866317680840289526096, -1929068840455252689180394182643523960848082983595846058543513630299]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-43497395945397433762561549377200857700944231683098731822472096154615, 1197733591739941212512162174359769322698698542866317680840289526096, -1929068840455252689180394182643523960848082983595846058543513630299]] ![![-6294451435, -1573664442, 552942581]]
  ![![47, 0, 0]] where
 M := ![![![3311051109736869723885413404595550065881299023079, -91172288637184169407465214881754061996444100976, 146842020910082343283038972216967741877252709970]]]
 hmul := by decide  
 g := ![![![![70447895951848291997561987331820214167687213257, -1939835928450727008669472657058597063754129808, 3124298317235794537936999408871654082494738510]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52875, -19654, -3194]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-52875, -19654, -3194]] 
 ![![53, 0, 0], ![0, 53, 0], ![10, 41, 1]] where
  M :=![![![-52875, -19654, -3194], ![223580, -8649, -98270], ![1331064, 437796, 11005]]]
  hmulB := by decide  
  f := ![![![-809943975, 22302418, -35920258]], ![![2514418060, -69236397, 111512090]], ![![1753351846, -48279865, 77759515]]]
  g := ![![![-395, 2100, -3194], ![22760, 75857, -98270], ![23038, -253, 11005]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [51, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 52], [0, 1]]
 g := ![![[52, 44], [13], [6, 37], [36], [51, 1]], ![[17, 9], [13], [38, 16], [36], [49, 52]]]
 h' := ![![[51, 52], [11, 16], [12, 15], [35, 39], [49, 6], [0, 1]], ![[0, 1], [32, 37], [35, 38], [10, 14], [37, 47], [51, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [44, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [51, 2, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1332, -2578, -2444]
  a := ![1, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![436, 1842, -2444]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![809943975, -22302418, 35920258]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![809943975, -22302418, 35920258]] 
 ![![53, 0, 0], ![7, 1, 0], ![10, 0, 1]] where
  M :=![![![809943975, -22302418, 35920258], ![-2514418060, 69236397, -111512090], ![2064052872, -56835252, 91538815]]]
  hmulB := by decide  
  f := ![![![52875, 19654, 3194]], ![![2765, 2759, 2276]], ![![-15138, -4552, 395]]]
  g := ![![![11450157, -22302418, 35920258], ![-35546263, 69236397, -111512090], ![29179462, -56835252, 91538815]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-52875, -19654, -3194]] ![![809943975, -22302418, 35920258]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [55, 40, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 49, 27], [23, 9, 32], [0, 1]]
 g := ![![[10, 56, 57], [48, 36, 16], [16, 9], [27, 39, 16], [1]], ![[16, 2, 54, 28], [48, 55, 45, 51], [29, 16], [29, 44, 53, 16], [15, 38, 45, 36]], ![[15, 24, 1, 8], [30, 44, 33, 58], [56, 1], [4, 18, 30, 30], [31, 26, 10, 23]]]
 h' := ![![[40, 49, 27], [15, 45, 23], [46, 33, 55], [49, 36, 3], [4, 19, 4], [0, 1]], ![[23, 9, 32], [26, 45, 6], [20, 20, 29], [50, 56, 55], [45, 50, 18], [40, 49, 27]], ![[0, 1], [10, 28, 30], [47, 6, 34], [0, 26, 1], [19, 49, 37], [23, 9, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 43], []]
 b := ![[], [1, 14, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [55, 40, 55, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1264075, -693958, -345386]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21425, -11762, -5854]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [42, 16, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 48, 35], [13, 12, 26], [0, 1]]
 g := ![![[13, 55, 1], [54, 39], [13, 8, 1], [5, 46, 12], [1]], ![[9, 20, 45, 7], [36, 49], [46, 44, 41, 40], [28, 11, 13, 18], [13, 1, 43, 53]], ![[56, 32, 34, 21], [52, 45], [45, 18, 5, 40], [54, 58, 41, 33], [15, 1, 3, 8]]]
 h' := ![![[3, 48, 35], [59, 11, 60], [3, 2, 10], [34, 57, 1], [19, 45, 16], [0, 1]], ![[13, 12, 26], [54, 41, 7], [23, 25, 7], [60, 51, 55], [30, 9, 59], [3, 48, 35]], ![[0, 1], [16, 9, 55], [59, 34, 44], [46, 14, 5], [42, 7, 47], [13, 12, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 21], []]
 b := ![[], [35, 21, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [42, 16, 45, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![913855396, 438032948, 176586643]
  a := ![1, 20, 81]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14981236, 7180868, 2894863]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀


def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![20, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![20, 1, 0]] 
 ![![67, 0, 0], ![20, 1, 0], ![50, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![20, 1, 0], ![0, 21, 5], ![-70, -20, 20]]]
  hmulB := by decide  
  f := ![![![981, 49, 0], ![-3283, 0, 0]], ![![260, 13, 0], ![-870, 0, 0]], ![![710, 27, -2], ![-2376, 27, 0]]]
  g := ![![![1, 0, 0], ![-20, 67, 0], ![-50, 0, 67]], ![![0, 1, 0], ![-10, 21, 5], ![-10, -20, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![26, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![26, 1, 0]] 
 ![![67, 0, 0], ![26, 1, 0], ![7, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![26, 1, 0], ![0, 27, 5], ![-70, -20, 26]]]
  hmulB := by decide  
  f := ![![![1171, 45, 0], ![-3015, 0, 0]], ![![442, 17, 0], ![-1138, 0, 0]], ![![75, -8, -2], ![-193, 27, 0]]]
  g := ![![![1, 0, 0], ![-26, 67, 0], ![-7, 0, 67]], ![![0, 1, 0], ![-11, 27, 5], ![4, -20, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![20, 1, 0]] ![![67, 0, 0], ![20, 1, 0]]
  ![![67, 0, 0], ![13, -32, 1]] where
 M := ![![![4489, 0, 0], ![1340, 67, 0]], ![![1340, 67, 0], ![400, 41, 5]]]
 hmul := by decide  
 g := ![![![![54, 32, -1], ![67, 0, 0]], ![![7, 33, -1], ![67, 0, 0]]], ![![![7, 33, -1], ![67, 0, 0]], ![![5, 3, 0], ![5, 0, 0]]]]
 hle2 := by decide  
def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![13, -32, 1]] ![![67, 0, 0], ![26, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![1742, 67, 0]], ![![871, -2144, 67], ![268, -871, -134]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![26, 1, 0]]], ![![![13, -32, 1]], ![![4, -13, -2]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![46, -25, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![46, -25, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![46, 46, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![46, -25, 1], ![-70, 1, -125], ![1764, 486, 26]]]
  hmulB := by decide  
  f := ![![![-45, 25, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-46, -46, 71]], ![![0, -1, 1], ![80, 81, -125], ![8, -10, 26]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [24, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 70], [0, 1]]
 g := ![![[68, 3], [13, 58], [5, 15], [8], [1], [1]], ![[0, 68], [0, 13], [20, 56], [8], [1], [1]]]
 h' := ![![[1, 70], [43, 28], [22, 49], [64, 21], [55, 24], [47, 1], [0, 1]], ![[0, 1], [0, 43], [0, 22], [14, 50], [8, 47], [48, 70], [1, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [68, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [24, 70, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1319, -1106, -484]
  a := ![-1, 2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![295, 298, -484]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-17, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-17, 1, 0]] 
 ![![71, 0, 0], ![54, 1, 0], ![45, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-17, 1, 0], ![0, -16, 5], ![-70, -20, -17]]]
  hmulB := by decide  
  f := ![![![885, -52, 0], ![3692, 0, 0]], ![![698, -41, 0], ![2912, 0, 0]], ![![593, -22, -4], ![2474, 57, 0]]]
  g := ![![![1, 0, 0], ![-54, 71, 0], ![-45, 0, 71]], ![![-1, 1, 0], ![9, -16, 5], ![25, -20, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![46, -25, 1]] ![![71, 0, 0], ![-17, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1207, 71, 0]], ![![3266, -1775, 71], ![-852, 426, -142]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-17, 1, 0]]], ![![![46, -25, 1]], ![![-12, 6, -2]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -46, -58]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![5, -46, -58]] 
 ![![73, 0, 0], ![0, 73, 0], ![49, 31, 1]] where
  M :=![![![5, -46, -58], ![4060, 1119, -230], ![2408, 1732, 1165]]]
  hmulB := by decide  
  f := ![![![-23315, 642, -1034]], ![![72380, -1993, 3210]], ![![14273, -393, 633]]]
  g := ![![![39, 24, -58], ![210, 113, -230], ![-749, -471, 1165]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [16, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 72], [0, 1]]
 g := ![![[71, 32], [19], [36], [39, 48], [2], [1]], ![[0, 41], [19], [36], [42, 25], [2], [1]]]
 h' := ![![[32, 72], [65, 55], [2, 26], [33, 67], [5, 62], [57, 32], [0, 1]], ![[0, 1], [0, 18], [31, 47], [60, 6], [18, 11], [59, 41], [32, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [56, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [16, 41, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3120, -4292, -3301]
  a := ![0, 3, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2173, 1343, -3301]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23315, -642, 1034]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![23315, -642, 1034]] 
 ![![73, 0, 0], ![64, 1, 0], ![44, 0, 1]] where
  M :=![![![23315, -642, 1034], ![-72380, 1993, -3210], ![59416, -1636, 2635]]]
  hmulB := by decide  
  f := ![![![-5, 46, 58]], ![![-60, 25, 54]], ![![-36, 4, 19]]]
  g := ![![![259, -642, 1034], ![-804, 1993, -3210], ![660, -1636, 2635]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![5, -46, -58]] ![![23315, -642, 1034]]
  ![![73, 0, 0]] where
 M := ![![![-73, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [28, 16, 66, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 39, 58], [35, 39, 21], [0, 1]]
 g := ![![[29, 57, 23], [36, 63, 1], [70, 15, 72], [68, 78, 25], [13, 1], []], ![[69, 59, 47, 28], [78, 55, 75, 57], [69, 5, 43, 17], [65, 55, 65, 61], [54, 20], [66, 46]], ![[65, 48, 31, 44], [71, 60, 5, 13], [50, 77, 38, 5], [8, 51, 61, 4], [71, 20], [24, 46]]]
 h' := ![![[57, 39, 58], [19, 18, 24], [15, 25, 1], [71, 59, 25], [31, 1, 74], [0, 0, 1], [0, 1]], ![[35, 39, 21], [67, 37, 5], [76, 75, 67], [65, 25, 52], [35, 36, 21], [58, 48, 39], [57, 39, 58]], ![[0, 1], [17, 24, 50], [21, 58, 11], [3, 74, 2], [66, 42, 63], [0, 31, 39], [35, 39, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 38], []]
 b := ![[], [27, 53, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [28, 16, 66, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-50472468, -24787040, -10374280]
  a := ![2, -8, -30]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-638892, -313760, -131320]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB160I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB160I1 : PrimesBelowBoundCertificateInterval O 31 79 160 where
  m := 11
  g := ![1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB160I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0, I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![68921]
    · exact ![79507]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![226981]
    · exact ![67, 67, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I47N0, I47N1, I47N2, I53N1, I67N0, I67N1, I71N1, I73N1]
  Il := ![[], [], [], [I47N0, I47N1, I47N2], [I53N1], [], [], [I67N0, I67N0, I67N1], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
