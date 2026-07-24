
import IdealArithmetic.Examples.NF5_3_2025000000_1.RI5_3_2025000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3030723, -3308888, -554319, 132274, 1183553]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-3030723, -3308888, -554319, 132274, 1183553]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-3030723, -3308888, -554319, 132274, 1183553], ![515270, 645297, 109497, -25223, -236896], ![-120670, -230530, -40168, 8605, 90002], ![59534, 170498, 30871, -5748, -67438], ![-1138858, -1242318, -208065, 49692, 444372]]]
  hmulB := by decide  
  f := ![![![-628290, -1677636, -1190784, 190035, 1049071]], ![![-281174, 1023857, 639771, -215322, 1132453]], ![![5279414, 5971214, 4636538, -221517, -11850760]], ![![-20600282, -40351490, -29359549, 3750470, 39871462]], ![![2870251, 7181958, 5121368, -786553, -4972622]]]
  g := ![![![-2107138, -3308888, -554319, 132274, 1183553], ![376083, 645297, 109497, -25223, -236896], ![-105336, -230530, -40168, 8605, 90002], ![63486, 170498, 30871, -5748, -67438], ![-791615, -1242318, -208065, 49692, 444372]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-655670, -695241, -116126, 27933, 247157]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-655670, -695241, -116126, 27933, 247157]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-655670, -695241, -116126, 27933, 247157], ![103252, 109494, 18297, -4394, -38906], ![-16296, -17220, -2830, 721, 6228], ![2362, 2848, 743, 54, -398], ![-246490, -261344, -43635, 10511, 92947]]]
  hmulB := by decide  
  f := ![![![54, 321, 188, -41, -22]], ![![265, 147, 148, 12, -653]], ![![-1474, -2443, -1824, 196, 3020]], ![![3296, 9038, 6421, -1040, -5416]], ![![-248, -1330, -917, 189, 165]]]
  g := ![![![-327835, -695241, -116126, 27933, 247157], ![51626, 109494, 18297, -4394, -38906], ![-8148, -17220, -2830, 721, 6228], ![1181, 2848, 743, 54, -398], ![-123245, -261344, -43635, 10511, 92947]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0, 0, 0]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![1, 1, 0, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 0, 1, 1, 0], ![-14, -8, -1, 5, 34], ![2, 4, 3, 0, -3]]]
  hmulB := by decide  
  f := ![![![28, 84, 15, -3, -34]], ![![1, 0, 0, 0, 0]], ![![27, 85, 15, -3, -34]], ![![1, -1, 1, 0, 0]], ![![19, 57, 10, -2, -23]]]
  g := ![![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-1, 0, 1, 1, 0], ![-22, -8, -1, 5, 34], ![-1, 4, 3, 0, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-3030723, -3308888, -554319, 132274, 1183553]] ![![-655670, -695241, -116126, 27933, 247157]]
  ![![1363116480276, 1445387120871, 241425682559, -58070127307, -513826051076]] where
 M := ![![![1363116480276, 1445387120871, 241425682559, -58070127307, -513826051076]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![1363116480276, 1445387120871, 241425682559, -58070127307, -513826051076]] ![![-655670, -695241, -116126, 27933, 247157]]
  ![![-621933922852349786, -659470625934747414, -110152597285483900, 26495008141832959, 234437669683252872]] where
 M := ![![![-621933922852349786, -659470625934747414, -110152597285483900, 26495008141832959, 234437669683252872]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-621933922852349786, -659470625934747414, -110152597285483900, 26495008141832959, 234437669683252872]] ![![1, 1, 0, 0, 0]]
  ![![-523988697471505468, -555613935188749384, -92805222312305657, 22322443423680895, 197517267772561990]] where
 M := ![![![-523988697471505468, -555613935188749384, -92805222312305657, 22322443423680895, 197517267772561990]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-523988697471505468, -555613935188749384, -92805222312305657, 22322443423680895, 197517267772561990]] ![![1, 1, 0, 0, 0]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-441468369857914018, -468113108959454052, -78189797607049966, 18806994806098818, 166411273087464460]]]
 hmul := by decide  
 g := ![![![![-220734184928957009, -234056554479727026, -39094898803524983, 9403497403049409, 83205636543732230]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23093, 75490, 13485, -2675, -30718]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![23093, 75490, 13485, -2675, -30718]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![23093, 75490, 13485, -2675, -30718], ![-23986, -78379, -13989, 2785, 31922], ![24854, 81422, 14602, -2849, -32998], ![-26110, -84346, -14723, 3206, 35126], ![8414, 27570, 4947, -963, -11167]]]
  hmulB := by decide  
  f := ![![![-229, 158, 73, -61, 674]], ![![734, 985, 747, -57, -1590]], ![![-2382, -5170, -3728, 519, 4422]], ![![1578, 11154, 7577, -1652, -42]], ![![487, -728, -418, 196, -1569]]]
  g := ![![![17937, 75490, 13485, -2675, -30718], ![-18636, -78379, -13989, 2785, 31922], ![19284, 81422, 14602, -2849, -32998], ![-20412, -84346, -14723, 3206, 35126], ![6527, 27570, 4947, -963, -11167]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![23093, 75490, 13485, -2675, -30718]] ![![23093, 75490, 13485, -2675, -30718]]
  ![![-1130877303, -3696834180, -660290456, 131052494, 1504508832]] where
 M := ![![![-1130877303, -3696834180, -660290456, 131052494, 1504508832]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-1130877303, -3696834180, -660290456, 131052494, 1504508832]] ![![23093, 75490, 13485, -2675, -30718]]
  ![![55383212783985, 181047623921634, 32336890997295, -6418106606083, -73681287456018]] where
 M := ![![![55383212783985, 181047623921634, 32336890997295, -6418106606083, -73681287456018]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N2 : IdealMulLeCertificate' Table 
  ![![55383212783985, 181047623921634, 32336890997295, -6418106606083, -73681287456018]] ![![23093, 75490, 13485, -2675, -30718]]
  ![![-2712320274887085911, -8866570118874709688, -1583656849788759748, 314318366014340596, 3608444515775290456]] where
 M := ![![![-2712320274887085911, -8866570118874709688, -1583656849788759748, 314318366014340596, 3608444515775290456]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N3 : IdealMulLeCertificate' Table 
  ![![-2712320274887085911, -8866570118874709688, -1583656849788759748, 314318366014340596, 3608444515775290456]] ![![23093, 75490, 13485, -2675, -30718]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![132832331037810337792077, 434228652172633544974410, 77557518882181715766225, -15393330067944563905455, -176718841384450424228790]]]
 hmul := by decide  
 g := ![![![![44277443679270112597359, 144742884057544514991470, 25852506294060571922075, -5131110022648187968485, -58906280461483474742930]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0, I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 100, 73, -9, -104]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![53, 100, 73, -9, -104]] 
 ![![5, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![53, 100, 73, -9, -104], ![-82, -291, -203, 37, 110], ![-298, 62, 2, -55, 818], ![2406, 3414, 2571, -218, -5142], ![-502, -910, -667, 79, 999]]]
  hmulB := by decide  
  f := ![![![4013, 4560, 767, -181, -1644]], ![![2257, 2513, 422, -100, -902]], ![![851, 1030, 175, -40, -374]], ![![1568, 1722, 293, -66, -606]], ![![2709, 3078, 518, -122, -1109]]]
  g := ![![![2, 100, 73, -9, -104], ![118, -291, -203, 37, 110], ![-566, 62, 2, -55, 818], ![1091, 3414, 2571, -218, -5142], ![-52, -910, -667, 79, 999]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![53, 100, 73, -9, -104]] ![![53, 100, 73, -9, -104]]
  ![![3409, 44640, 29944, -7046, 7584]] where
 M := ![![![3409, 44640, 29944, -7046, 7584]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![3409, 44640, 29944, -7046, 7584]] ![![53, 100, 73, -9, -104]]
  ![![-33162959, -41749296, -31926969, 2109243, 72857004]] where
 M := ![![![-33162959, -41749296, -31926969, 2109243, 72857004]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-33162959, -41749296, -31926969, 2109243, 72857004]] ![![53, 100, 73, -9, -104]]
  ![![-20319335143, -52245640880, -37182400772, 5805614316, 34678684024]] where
 M := ![![![-20319335143, -52245640880, -37182400772, 5805614316, 34678684024]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-20319335143, -52245640880, -37182400772, 5805614316, 34678684024]] ![![53, 100, 73, -9, -104]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![10847181883885, -870996053100, 843740994085, 1768809463195, -29257476946320]]]
 hmul := by decide  
 g := ![![![![2169436376777, -174199210620, 168748198817, 353761892639, -5851495389264]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2 ⊙ MulI5N3)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34357, 32693, 17108, -10669, 103852]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-34357, 32693, 17108, -10669, 103852]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![1, 4, 0, 1, 0], ![4, 2, 4, 0, 1]] where
  M :=![![![-34357, 32693, 17108, -10669, 103852], ![357070, 466403, 354918, -25568, -778154], ![-1198356, -2551002, -1842491, 252646, 2243304], ![949564, 5753692, 3926264, -831907, -383252], ![242916, -450148, -265672, 112500, -816083]]]
  hmulB := by decide  
  f := ![![![-47733, -55829, -9502, 2151, 20030]], ![![9946, 15179, 2110, -898, -6986]], ![![-1400, -10814, -4881, -1482, -2588]], ![![1089, 713, -2594, -1750, -6850]], ![![-27676, -36810, -8296, 144, 8705]]]
  g := ![![![-62728, -18905, -56900, -10669, 103852], ![499322, 303569, 495362, -25568, -778154], ![-1489174, -1149742, -1545101, 252646, 2243304], ![473497, 1406832, 779896, -831907, -383252], ![484964, 104574, 428380, 112500, -816083]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [3, 3, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 4], [1, 2], [0, 1]]
 g := ![![[6, 5, 2], [1]], ![[4, 5, 4], [1]], ![[6, 4, 1], [1]]]
 h' := ![![[3, 4], [4, 4, 4], [0, 1]], ![[1, 2], [3, 0, 1], [3, 4]], ![[0, 1], [5, 3, 2], [1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4], []]
 b := ![[], [1, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [3, 3, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![112677126, -66016068, -153972618, -90161746, -318174567]
  a := ![35, 19, 2, -11, -85]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![210791020, 132997150, 159817950, -90161746, -318174567]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47733, 55829, 9502, -2151, -20030]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![47733, 55829, 9502, -2151, -20030]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 2, 0, 1, 0], ![2, 2, 0, 0, 1]] where
  M :=![![![47733, 55829, 9502, -2151, -20030], ![-9946, -15179, -2110, 898, 6986], ![1400, 10814, 4881, 1482, 2588], ![-15572, -104, 17096, 10809, 40036], ![17092, 21456, 4760, -128, -5139]]]
  hmulB := by decide  
  f := ![![![34357, -32693, -17108, 10669, -103852]], ![![-357070, -466403, -354918, 25568, 778154]], ![![181010, 355088, 258325, -33044, -350144]], ![![-237672, -955214, -662300, 126149, 277080]], ![![-126906, -78292, -68340, -5718, 309241]]]
  g := ![![![9827, 14313, 9502, -2151, -20030], ![-2814, -4421, -2110, 898, 6986], ![-1934, 382, 4881, 1482, 2588], ![-18548, -14542, 17096, 10809, 40036], ![2550, 4570, 4760, -128, -5139]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [6, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 6], [0, 1]]
 g := ![![[1, 4], [1, 1]], ![[5, 3], [2, 6]]]
 h' := ![![[1, 6], [1, 2], [0, 1]], ![[0, 1], [3, 5], [1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [3, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [6, 6, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17025, -528, 17776, 12266, 44478]
  a := ![-27, -79, -1, 8, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20219, -16288, 17776, 12266, 44478]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-34357, 32693, 17108, -10669, 103852]] ![![47733, 55829, 9502, -2151, -20030]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![-7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22813, 25383, 4231, -1030, -9186]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![22813, 25383, 4231, -1030, -9186]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![1, 5, 4, 7, 1]] where
  M :=![![![22813, 25383, 4231, -1030, -9186], ![-3952, -5691, -1145, 111, 1724], ![1894, 2056, -630, -701, -3122], ![3570, -4986, -6609, -3434, -11346], ![8846, 9338, 1185, -613, -4233]]]
  hmulB := by decide  
  f := ![![![1105, 3221, 2273, -380, -1744]], ![![1832, -2831, -1631, 753, -5944]], ![![-22430, -27968, -21416, 1381, 49378]], ![![79422, 164034, 118785, -15892, -150558]], ![![42279, 90394, 65264, -8980, -78999]]]
  g := ![![![2909, 6483, 3725, 5752, -9186], ![-516, -1301, -731, -1087, 1724], ![456, 1606, 1078, 1923, -3122], ![1356, 4704, 3525, 6908, -11346], ![1189, 2773, 1647, 2638, -4233]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 4 2 3 [4, 3, 9, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 5, 3, 2], [10, 8, 5, 4], [8, 8, 3, 5], [0, 1]]
 g := ![![[8, 4], [8, 1], []], ![[4, 1, 5, 2, 0, 7], [10, 3, 2, 1, 4, 2], [4, 0, 4]], ![[5, 8, 6, 6, 2, 5], [6, 9, 1, 0, 7, 5], [2, 3, 5]], ![[2, 0, 3, 4, 2, 5], [5, 3, 7, 4, 1, 5], [10, 10, 3]]]
 h' := ![![[1, 5, 3, 2], [1, 5, 2], [0, 0, 1], [0, 1]], ![[10, 8, 5, 4], [9, 10, 6, 8], [7, 9, 1, 10], [1, 5, 3, 2]], ![[8, 8, 3, 5], [4, 5, 6, 2], [4, 10, 7, 2], [10, 8, 5, 4]], ![[0, 1], [1, 2, 8, 1], [2, 3, 2, 10], [8, 8, 3, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 0, 9], []]
 b := ![[], [], [0, 9, 5, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 4
  hpos := by decide
  P := [4, 3, 9, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5373821600, 3614100404, 7848096977, 4407407779, 15337337660]
  a := ![12, 4, 1, -4, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1882832660, -6642962536, -4863750333, -9359450531, 15337337660]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 14641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1105, 3221, 2273, -380, -1744]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![1105, 3221, 2273, -380, -1744]] 
 ![![11, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![1105, 3221, 2273, -380, -1744], ![1832, -2831, -1631, 753, -5944], ![-22430, -27968, -21416, 1381, 49378], ![79422, 164034, 118785, -15892, -150558], ![-11430, -31098, -22045, 3555, 18869]]]
  hmulB := by decide  
  f := ![![![22813, 25383, 4231, -1030, -9186]], ![![16232, 17943, 2973, -739, -6524]], ![![4320, 4802, 712, -251, -1954]], ![![12768, 13392, 1707, -874, -6042]], ![![4952, 5464, 877, -243, -2055]]]
  g := ![![![-2131, 3221, 2273, -380, -1744], ![3192, -2831, -1631, 753, -5944], ![12464, -27968, -21416, 1381, 49378], ![-97632, 164034, 118785, -15892, -150558], ![20216, -31098, -22045, 3555, 18869]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![22813, 25383, 4231, -1030, -9186]] ![![1105, 3221, 2273, -380, -1744]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2023, 2599, 447, -98, -946]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![2023, 2599, 447, -98, -946]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![11, 4, 8, 1, 0], ![11, 9, 3, 0, 1]] where
  M :=![![![2023, 2599, 447, -98, -946], ![-520, -977, -141, 55, 452], ![134, 848, 324, 79, 62], ![-982, -250, 955, 640, 2438], ![710, 1002, 237, 3, -215]]]
  hmulB := by decide  
  f := ![![![-259, -725, -513, 84, 420]], ![![-336, 749, 451, -177, 1176]], ![![4830, 5784, 4454, -257, -10722]], ![![1277, 407, 436, 122, -3254]], ![![867, 1776, 1287, -171, -1649]]]
  g := ![![![1039, 885, 313, -98, -946], ![-469, -405, -149, 55, 452], ![-109, -2, -38, 79, 62], ![-2680, -1904, -883, 640, 2438], ![234, 225, 66, 3, -215]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [2, 10, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 7, 2], [7, 5, 11], [0, 1]]
 g := ![![[7, 12, 10], [5, 10], [1]], ![[8, 10, 4, 6], [5, 9], [12, 6, 2, 8]], ![[4, 3, 10, 5], [4, 9], [0, 8, 12, 5]]]
 h' := ![![[12, 7, 2], [7, 9, 6], [11, 3, 6], [0, 1]], ![[7, 5, 11], [4, 9, 9], [1, 6, 10], [12, 7, 2]], ![[0, 1], [4, 8, 11], [5, 4, 10], [7, 5, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 4], []]
 b := ![[], [1, 11, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [2, 10, 7, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-295157646, 149677486, 376134916, 228937864, 825436238]
  a := ![-51, -10, -3, 14, 124]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-914867136, -630384624, -302436670, 228937864, 825436238]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![217, 440, 313, -41, -414]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![217, 440, 313, -41, -414]] 
 ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![217, 440, 313, -41, -414], ![-254, -1111, -761, 149, 262], ![-1562, -398, -474, -165, 4018], ![10346, 15830, 11821, -1134, -21682], ![-2042, -3934, -2869, 361, 3977]]]
  hmulB := by decide  
  f := ![![![87721, 92884, 15411, -3797, -33258]], ![![12468, 13141, 2133, -567, -4814]], ![![61095, 64350, 10411, -2798, -23652]], ![![55098, 56370, 7817, -3272, -23714]], ![![70088, 74086, 12193, -3091, -26755]]]
  g := ![![![76, 440, 313, -41, -414], ![385, -1111, -761, 149, 262], ![-2720, -398, -474, -165, 4018], ![7553, 15830, 11821, -1134, -21682], ![-847, -3934, -2869, 361, 3977]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-69, -73, -12, 3, 26]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![-69, -73, -12, 3, 26]] 
 ![![13, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-69, -73, -12, 3, 26], ![10, 11, 2, 0, -2], ![-4, 2, 5, 2, 8], ![-12, 12, 24, 13, 36], ![-28, -28, -4, 2, 15]]]
  hmulB := by decide  
  f := ![![![1545, 5051, 902, -179, -2056]], ![![233, 762, 136, -27, -310]], ![![604, 1974, 353, -70, -804]], ![![-15, -49, -10, 2, 20]], ![![1113, 3639, 650, -129, -1481]]]
  g := ![![![-3, -73, -12, 3, 26], ![-1, 11, 2, 0, -2], ![-8, 2, 5, 2, 8], ![-37, 12, 24, 13, 36], ![-5, -28, -4, 2, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![2023, 2599, 447, -98, -946]] ![![217, 440, 313, -41, -414]]
  ![![-1545, -5051, -902, 179, 2056]] where
 M := ![![![-1545, -5051, -902, 179, 2056]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-1545, -5051, -902, 179, 2056]] ![![-69, -73, -12, 3, 26]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![-13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-444401, -1452705, -259466, 51499, 591212]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-444401, -1452705, -259466, 51499, 591212]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![1, 14, 1, 0, 0], ![3, 9, 0, 1, 0], ![8, 14, 0, 0, 1]] where
  M :=![![![-444401, -1452705, -259466, 51499, 591212], ![461438, 1508455, 269432, -53470, -613882], ![-479184, -1566330, -279721, 55552, 637548], ![497368, 1626592, 290762, -57513, -661424], ![-162248, -530328, -94706, 18810, 215865]]]
  hmulB := by decide  
  f := ![![![-2887, -6313, -4548, 637, 5338]], ![![1758, 13369, 9064, -2000, 306]], ![![2961, 11755, 8155, -1547, -3506]], ![![-8599, -9142, -7166, 262, 19520]], ![![1740, 11498, 7826, -1686, -347]]]
  g := ![![![-298184, -385920, -259466, 51499, 591212], ![309616, 400705, 269432, -53470, -613882], ![-321559, -416228, -279721, 55552, 637548], ![333561, 431381, 290762, -57513, -661424], ![-108876, -140932, -94706, 18810, 215865]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [12, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 16], [0, 1]]
 g := ![![[1, 15], [8], [8], [1]], ![[8, 2], [8], [8], [1]]]
 h' := ![![[5, 16], [15, 10], [14, 5], [5, 5], [0, 1]], ![[0, 1], [14, 7], [5, 12], [13, 12], [5, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [2, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [12, 12, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-54987, 115862, 178747, 75536, 183836]
  a := ![65, 37, 5, -17, -158]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-113590, -331772, 178747, 75536, 183836]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65931, -215368, -38463, 7637, 87652]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-65931, -215368, -38463, 7637, 87652]] 
 ![![17, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![0, 0, 0, 0, 17]] where
  M :=![![![-65931, -215368, -38463, 7637, 87652], ![68386, 223581, 39951, -7915, -90950], ![-71090, -232094, -41354, 8291, 94690], ![73306, 241342, 43685, -8190, -96866], ![-24098, -78606, -14001, 2811, 32079]]]
  hmulB := by decide  
  f := ![![![3201, 7524, 5391, -795, -5728]], ![![734, 985, 747, -57, -1590]], ![![-2117, -1586, -1325, -48, 5054]], ![![13247, 25022, 18268, -2255, -25986]], ![![-31586, -70818, -50929, 7265, 57791]]]
  g := ![![![43219, -215368, -38463, 7637, 5156], ![-44882, 223581, 39951, -7915, -5350], ![46521, -232094, -41354, 8291, 5570], ![-48781, 241342, 43685, -8190, -5698], ![15752, -78606, -14001, 2811, 1887]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [4, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 16], [0, 1]]
 g := ![![[2, 13], [2], [13], [1]], ![[0, 4], [2], [13], [1]]]
 h' := ![![[9, 16], [13, 8], [15, 11], [13, 9], [0, 1]], ![[0, 1], [0, 9], [12, 6], [9, 8], [9, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [14, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [4, 8, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6757, 628, 2232, 1796, -17816]
  a := ![23, 14, 4, 0, -54]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1255, 628, 2232, 1796, -1048]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-196643, -298787, -223167, 21178, 412874]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![-196643, -298787, -223167, 21178, 412874]] 
 ![![17, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![-196643, -298787, -223167, 21178, 412874], ![529256, 1285429, 918657, -138455, -931444], ![75482, -2088880, -1370448, 364837, -981694], ![-7071106, -6769990, -5398799, 88900, 16331234], ![1801730, 2606886, 1958367, -171915, -3831773]]]
  hmulB := by decide  
  f := ![![![-204339101, -216670171, -36190731, 8705028, 77024892]], ![![-142346460, -150936577, -25211135, 6064101, 53657064]], ![![-108477675, -115023627, -19212445, 4621309, 40890438]], ![![-132173017, -140148399, -23408524, 5631078, 49823422]], ![![-124718000, -132244192, -22088895, 5313123, 47012083]]]
  g := ![![![60918, -298787, -223167, 21178, 412874], ![-725080, 1285429, 918657, -138455, -931444], ![2545871, -2088880, -1370448, 364837, -981694], ![-2443075, -6769990, -5398799, 88900, 16331234], ![-405730, 2606886, 1958367, -171915, -3831773]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-444401, -1452705, -259466, 51499, 591212]] ![![-65931, -215368, -38463, 7637, 87652]]
  ![![-62071284941, -202910919047, -36241890225, 7193157154, 82579035372]] where
 M := ![![![-62071284941, -202910919047, -36241890225, 7193157154, 82579035372]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![-62071284941, -202910919047, -36241890225, 7193157154, 82579035372]] ![![-196643, -298787, -223167, 21178, 412874]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![645751817, 2110961536, 377038546, -74833218, -859101936]]]
 hmul := by decide  
 g := ![![![![37985401, 124174208, 22178738, -4401954, -50535408]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-475, -617, -105, 24, 228]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-475, -617, -105, 24, 228]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![2, 17, 1, 0, 0], ![4, 17, 0, 1, 0], ![6, 10, 0, 0, 1]] where
  M :=![![![-475, -617, -105, 24, 228], ![120, 245, 43, -9, -96], ![-66, -192, -34, 7, 78], ![58, 190, 35, -6, -74], ![-178, -230, -39, 9, 85]]]
  hmulB := by decide  
  f := ![![![1, 13, 9, -2, 2]], ![![32, 25, 21, 1, -76]], ![![20, 9, 9, 2, -50]], ![![46, 77, 58, -5, -94]], ![![16, 10, 9, 1, -39]]]
  g := ![![![-91, -80, -105, 24, 228], ![34, 33, 43, -9, -96], ![-26, -27, -34, 7, 78], ![24, 23, 35, -6, -74], ![-34, -30, -39, 9, 85]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [15, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 18], [0, 1]]
 g := ![![[1, 7], [12, 1], [16], [1]], ![[10, 12], [16, 18], [16], [1]]]
 h' := ![![[4, 18], [10, 11], [4, 1], [4, 4], [0, 1]], ![[0, 1], [16, 8], [8, 18], [1, 15], [4, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [12, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [15, 15, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3099, 6674, 11206, 5084, 10412]
  a := ![-19, -14, -1, 4, 46]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5701, -19704, 11206, 5084, 10412]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 737, 135, -24, -292]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![223, 737, 135, -24, -292]] 
 ![![19, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![223, 737, 135, -24, -292], ![-248, -753, -115, 39, 352], ![158, 848, 264, 41, -82], ![-738, -498, 561, 428, 1722], ![50, 290, 95, 17, -17]]]
  hmulB := by decide  
  f := ![![![-61, -69, -83, 2, 222]], ![![-7, 10, -8, -3, 62]], ![![-76, -170, -144, 17, 202]], ![![-163, -27, -50, -20, 456]], ![![50, 50, 39, -1, -113]]]
  g := ![![![-428, 737, 135, -24, -292], ![414, -753, -115, 39, 352], ![-603, 848, 264, 41, -82], ![-374, -498, 561, 428, 1722], ![-211, 290, 95, 17, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, -5011, -3314, 845, -1816]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![-21, -5011, -3314, 845, -1816]] 
 ![![19, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-21, -5011, -3314, 845, -1816], ![-15462, -14045, -11304, 66, 35994], ![71064, 127986, 93871, -11040, -141732], ![-128904, -407544, -286170, 49711, 191568], ![4408, 53392, 35858, -8378, 8189]]]
  hmulB := by decide  
  f := ![![![699791, 754495, 126236, -30227, -269174]], ![![546405, 588544, 98460, -23583, -209928]], ![![111723, 121137, 20275, -4851, -43278]], ![![441516, 475272, 79482, -19061, -169560]], ![![234830, 253178, 42358, -10144, -90327]]]
  g := ![![![4518, -5011, -3314, 845, -1816], ![651, -14045, -11304, 66, 35994], ![-60393, 127986, 93871, -11040, -141732], ![268254, -407544, -286170, 49711, 191568], ![-44876, 53392, 35858, -8378, 8189]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2

def I19N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3873, -4107, -686, 165, 1460]] i)))

def SI19N3: IdealEqSpanCertificate' Table ![![-3873, -4107, -686, 165, 1460]] 
 ![![19, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-3873, -4107, -686, 165, 1460], ![610, 647, 108, -26, -230], ![-96, -102, -17, 4, 36], ![16, 16, 2, -1, -8], ![-1456, -1544, -258, 62, 549]]]
  hmulB := by decide  
  f := ![![![-37, -129, -24, 5, 46]], ![![-30, -103, -20, 4, 38]], ![![-18, -68, -9, 2, 20]], ![![-21, -85, -26, 4, 22]], ![![-11, -35, -6, 1, 15]]]
  g := ![![![3136, -4107, -686, 165, 1460], ![-494, 647, 108, -26, -230], ![78, -102, -17, 4, 36], ![-11, 16, 2, -1, -8], ![1179, -1544, -258, 62, 549]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N3 : Nat.card (O ⧸ I19N3) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N3)

lemma isPrimeI19N3 : Ideal.IsPrime I19N3 := prime_ideal_of_norm_prime hp19.out _ NI19N3
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-475, -617, -105, 24, 228]] ![![223, 737, 135, -24, -292]]
  ![![24189, 79654, 14234, -2820, -32422]] where
 M := ![![![24189, 79654, 14234, -2820, -32422]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![24189, 79654, 14234, -2820, -32422]] ![![-21, -5011, -3314, 845, -1816]]
  ![![-37, -129, -24, 5, 46]] where
 M := ![![![-37, -129, -24, 5, 46]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N2 : IdealMulLeCertificate' Table 
  ![![-37, -129, -24, 5, 46]] ![![-3873, -4107, -686, 165, 1460]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2, I19N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
    exact isPrimeI19N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1 ⊙ MulI19N2)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![296625111, 314528362, 52536669, -12636285, -111811900]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![296625111, 314528362, 52536669, -12636285, -111811900]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![22, 4, 0, 7, 1]] where
  M :=![![![296625111, 314528362, 52536669, -12636285, -111811900], ![-46715810, -49532209, -8271053, 1991529, 17613910], ![7346414, 7807598, 1317992, -304937, -2743654], ![-1218190, -1188706, -118427, 98244, 606758], ![111502422, 118238962, 19754999, -4747033, -42020963]]]
  hmulB := by decide  
  f := ![![![29557, 102478, 71585, -12927, -40552]], ![![99874, -29235, -6251, 19877, -277310]], ![![-832898, -1168382, -881042, 73257, 1785058]], ![![2544518, 5721278, 4113535, -588014, -4649494]], ![![806166, 1790460, 1288612, -182543, -1481361]]]
  g := ![![![119847257, 33120694, 2284203, 33480305, -111811900], ![-18879210, -5216863, -359611, -5274167, 17613910], ![2943774, 816618, 57304, 821767, -2743654], ![-633342, -157206, -5149, -180394, 606758], ![45041896, 12448818, 858913, 12582596, -42020963]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [8, 13, 3, 10, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 1, 16, 17], [11, 14, 13, 13], [19, 7, 17, 16], [0, 1]]
 g := ![![[5, 12, 11, 2], [3, 3, 12, 2], [13, 1], []], ![[8, 9, 20, 8, 15, 20], [0, 13, 13, 13, 16, 20], [21, 14, 14, 5, 10, 11], [21, 0, 13]], ![[11, 5, 18, 3, 13, 4], [9, 20, 15, 13, 10, 1], [13, 21, 3, 22, 16, 9], [22, 5, 8]], ![[14, 6, 11, 8, 20, 3], [4, 12, 16, 21, 9, 9], [4, 11, 15, 19, 10, 2], [10, 8, 3]]]
 h' := ![![[6, 1, 16, 17], [22, 12, 10, 5], [11, 7, 17, 5], [0, 0, 1], [0, 1]], ![[11, 14, 13, 13], [1, 10, 0, 14], [2, 18, 10, 9], [6, 15, 3, 18], [6, 1, 16, 17]], ![[19, 7, 17, 16], [19, 3, 3, 8], [5, 14, 15, 4], [14, 5, 11, 12], [11, 14, 13, 13]], ![[0, 1], [8, 21, 10, 19], [6, 7, 4, 5], [5, 3, 8, 16], [19, 7, 17, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [21, 19, 7], []]
 b := ![[], [], [12, 12, 22, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [8, 13, 3, 10, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1011379642595, 708145445813, 1513780122702, 842013006919, 2895980044916]
  a := ![-55, -31, 0, 13, 134]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2814040896989, -472859771037, 65816527074, -844775969891, 2895980044916]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29557, 102478, 71585, -12927, -40552]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![29557, 102478, 71585, -12927, -40552]] 
 ![![23, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![29557, 102478, 71585, -12927, -40552], ![99874, -29235, -6251, 19877, -277310], ![-832898, -1168382, -881042, 73257, 1785058], ![2544518, 5721278, 4113535, -588014, -4649494], ![-319558, -1005942, -706535, 122495, 476539]]]
  hmulB := by decide  
  f := ![![![296625111, 314528362, 52536669, -12636285, -111811900]], ![![243007013, 257674203, 43040246, -10352082, -91600530]], ![![90596617, 96065484, 16046725, -3859084, -34148998]], ![![64430755, 68324048, 11415866, -2742747, -24280554]], ![![120918627, 128217140, 21416740, -5151026, -45579481]]]
  g := ![![![-86479, 102478, 71585, -12927, -40552], ![134587, -29235, -6251, 19877, -277310], ![482689, -1168382, -881042, 73257, 1785058], ![-3920391, 5721278, 4113535, -588014, -4649494], ![819033, -1005942, -706535, 122495, 476539]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![296625111, 314528362, 52536669, -12636285, -111811900]] ![![29557, 102478, 71585, -12927, -40552]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)


lemma PB2201I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB2201I0 : PrimesBelowBoundCertificateInterval O 1 23 2201 where
  m := 9
  g := ![5, 5, 5, 2, 2, 3, 3, 4, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB2201I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0, I19N1, I19N2, I19N3]
    · exact ![I23N0, I23N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![343, 49]
    · exact ![14641, 11]
    · exact ![2197, 13, 13]
    · exact ![289, 289, 17]
    · exact ![361, 19, 19, 19]
    · exact ![279841, 23]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N0
      exact NI3N0
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
      exact NI19N3
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I5N0, I7N0, I7N1, I11N1, I13N0, I13N1, I13N2, I17N0, I17N1, I17N2, I19N0, I19N1, I19N2, I19N3, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N0, I3N0, I3N0], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1], [I11N1], [I13N0, I13N1, I13N2], [I17N0, I17N1, I17N2], [I19N0, I19N1, I19N2, I19N3], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
