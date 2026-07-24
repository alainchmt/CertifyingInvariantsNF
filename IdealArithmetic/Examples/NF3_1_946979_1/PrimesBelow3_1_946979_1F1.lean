
import IdealArithmetic.Examples.NF3_1_946979_1.RI3_1_946979_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-223884399077, -14564819778, -13849688728]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-223884399077, -14564819778, -13849688728]] 
 ![![37, 0, 0], ![9, 1, 0], ![33, 0, 1]] where
  M :=![![![-223884399077, -14564819778, -13849688728], ![-2589891792136, -168485644165, -160213017558], ![-2723621298486, -177185429264, -168485644165]]]
  hmulB := by decide  
  f := ![![![470087, 159178, -190004]], ![![-845945, 71965, 1106]], ![![1223761, 37462, -136217]]]
  g := ![![![9844289377, -14564819778, -13849688728], ![113878610399, -168485644165, -160213017558], ![119758751955, -177185429264, -168485644165]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![218, -22, 3]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![218, -22, 3]] 
 ![![37, 0, 0], ![30, 1, 0], ![9, 0, 1]] where
  M :=![![![218, -22, 3], ![561, 206, -242], ![-4114, 139, 206]]]
  hmulB := by decide  
  f := ![![![76074, 4949, 4706]], ![![85466, 5560, 5287]], ![![43517, 2831, 2692]]]
  g := ![![![23, -22, 3], ![-93, 206, -242], ![-274, 139, 206]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3554, 547, -228]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-3554, 547, -228]] 
 ![![37, 0, 0], ![35, 1, 0], ![3, 0, 1]] where
  M :=![![![-3554, 547, -228], ![-42636, -2642, 6017], ![102289, -6064, -2642]]]
  hmulB := by decide  
  f := ![![![-43467252, -2827766, -2688923]], ![![-54707633, -3559010, -3384263]], ![![-17816054, -1159025, -1102117]]]
  g := ![![![-595, 547, -228], ![859, -2642, 6017], ![8715, -6064, -2642]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-223884399077, -14564819778, -13849688728]] ![![218, -22, 3]]
  ![![-43467252, -2827766, -2688923]] where
 M := ![![![-43467252, -2827766, -2688923]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-43467252, -2827766, -2688923]] ![![-3554, 547, -228]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [39, 32, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 16, 35], [7, 24, 6], [0, 1]]
 g := ![![[21, 21, 9], [11, 5], [18, 4], [32, 8, 1], []], ![[16, 19], [11, 9], [32, 5], [18, 7, 34, 29], [14, 36]], ![[34, 40, 32, 13], [17, 18], [29, 39], [30, 6, 20, 19], [2, 36]]]
 h' := ![![[1, 16, 35], [21, 29, 38], [32, 9, 28], [23, 17, 2], [0, 0, 1], [0, 1]], ![[7, 24, 6], [4, 20], [33, 24, 3], [16, 35, 28], [29, 25, 24], [1, 16, 35]], ![[0, 1], [24, 33, 3], [21, 8, 10], [2, 30, 11], [12, 16, 16], [7, 24, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 13], []]
 b := ![[], [39, 22, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [39, 32, 33, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9389, -164, -246]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![229, -4, -6]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2573391885036, -100188130651, -116266486352]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![2573391885036, -100188130651, -116266486352]] 
 ![![43, 0, 0], ![6, 1, 0], ![28, 0, 1]] where
  M :=![![![2573391885036, -100188130651, -116266486352], ![-21741832947824, 3038457830444, -1102069437161], ![-18735180431737, -1575777745380, 3038457830444]]]
  hmulB := by decide  
  f := ![![![-7495609494444693285170956, -487627551821086578392804, -463685092631205158622099]], ![![-3062389983458221497054843, -199224056624334700489288, -189442177344632170094266]], ![![-7001474838023130282424212, -455481577172943385534953, -433117481804502723072124]]]
  g := ![![![149534471786, -100188130651, -116266486352], ![-211968271860, 3038457830444, -1102069437161], ![-2194356586323, -1575777745380, 3038457830444]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1568, -102, -97]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-1568, -102, -97]] 
 ![![43, 0, 0], ![9, 1, 0], ![20, 0, 1]] where
  M :=![![![-1568, -102, -97], ![-18139, -1180, -1122], ![-19074, -1241, -1180]]]
  hmulB := by decide  
  f := ![![![2, -17, 16]], ![![70, -5, -1]], ![![-73, 0, 6]]]
  g := ![![![30, -102, -97], ![347, -1180, -1122], ![365, -1241, -1180]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1908265977227212512587, -124142415288366901080, -118047036344591425330]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-1908265977227212512587, -124142415288366901080, -118047036344591425330]] 
 ![![43, 0, 0], ![28, 1, 0], ![3, 0, 1]] where
  M :=![![![-1908265977227212512587, -124142415288366901080, -118047036344591425330], ![-22074795796438596536710, -1436077831848846811267, -1365566568172035911880], ![-23214631658924610501960, -1510229956704586626290, -1436077831848846811267]]]
  hmulB := by decide  
  f := ![![![99013179911, -22731457340, 13476362710]], ![![123080206146, -13752862243, 2960281980]], ![![-91947511229, 5856502870, 1989228307]]]
  g := ![![![44694482787926395201, -124142415288366901080, -118047036344591425330], ![517025190694074928242, -1436077831848846811267, -1365566568172035911880], ![543721874984891987627, -1510229956704586626290, -1436077831848846811267]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![2573391885036, -100188130651, -116266486352]] ![![-1568, -102, -97]]
  ![![-99013179911, 22731457340, -13476362710]] where
 M := ![![![-99013179911, 22731457340, -13476362710]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-99013179911, 22731457340, -13476362710]] ![![-1908265977227212512587, -124142415288366901080, -118047036344591425330]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [15, 24, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 7, 5], [20, 39, 42], [0, 1]]
 g := ![![[0, 45, 7], [17, 44, 24], [41, 5, 14], [0, 20, 1], []], ![[30, 0, 1, 29], [25, 31, 34, 45], [20, 43, 4, 11], [38, 5, 5, 38], [6, 25]], ![[8, 25, 15, 4], [10, 29, 0, 12], [38, 31, 41, 18], [20, 46, 20, 37], [16, 25]]]
 h' := ![![[0, 7, 5], [27, 29, 17], [43, 22, 20], [0, 29, 22], [0, 0, 1], [0, 1]], ![[20, 39, 42], [1, 28, 9], [29, 20, 44], [41, 18, 16], [4, 45, 39], [0, 7, 5]], ![[0, 1], [37, 37, 21], [17, 5, 30], [11, 0, 9], [19, 2, 7], [20, 39, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 21], []]
 b := ![[], [24, 32, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [15, 24, 27, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![55930, 7426, -11139]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1190, 158, -237]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11988940781, -779941624, -741646576]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-11988940781, -779941624, -741646576]] 
 ![![53, 0, 0], ![19, 1, 0], ![25, 0, 1]] where
  M :=![![![-11988940781, -779941624, -741646576], ![-138687909712, -9022354477, -8579357864], ![-145849083688, -9488225296, -9022354477]]]
  hmulB := by decide  
  f := ![![![-615785, 64152, -10384]], ![![-257391, 12163, 9592]], ![![-64117, 22088, -15733]]]
  g := ![![![403228575, -779941624, -741646576], ![4664542867, -9022354477, -8579357864], ![4905397337, -9488225296, -9022354477]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-398813027, 48008940, -12868876]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-398813027, 48008940, -12868876]] 
 ![![53, 0, 0], ![36, 1, 0], ![46, 0, 1]] where
  M :=![![![-398813027, 48008940, -12868876], ![-2406479812, -347337523, 528098340], ![8977671780, -410806652, -347337523]]]
  hmulB := by decide  
  f := ![![![337589665865933209, 21961926166018772, 20883598005525452]], ![![302989826381261416, 19711030487179381, 18743221057077788]], ![![370490657035442226, 24102303114466436, 22918882681094381]]]
  g := ![![![-28965407, 48008940, -12868876], ![-267827408, -347337523, 528098340], ![749891270, -410806652, -347337523]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11240381, -731244, -695340]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![-11240381, -731244, -695340]] 
 ![![53, 0, 0], ![51, 1, 0], ![43, 0, 1]] where
  M :=![![![-11240381, -731244, -695340], ![-130028580, -8459021, -8043684], ![-136742628, -8895804, -8459021]]]
  hmulB := by decide  
  f := ![![![23495, -1236, -756]], ![![19941, -689, -984]], ![![14701, -1152, -113]]]
  g := ![![![1055711, -731244, -695340], ![12212451, -8459021, -8043684], ![12843043, -8895804, -8459021]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-11988940781, -779941624, -741646576]] ![![-398813027, 48008940, -12868876]]
  ![![23495, -1236, -756]] where
 M := ![![![23495, -1236, -756]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![23495, -1236, -756]] ![![-11240381, -731244, -695340]]
  ![![53, 0, 0]] where
 M := ![![![53, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3028729389319, 1013473317068, -714747298830]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-3028729389319, 1013473317068, -714747298830]] 
 ![![59, 0, 0], ![0, 59, 0], ![18, 37, 1]] where
  M :=![![![-3028729389319, 1013473317068, -714747298830], ![-133657744881210, -169740193999, 11148206487748], ![189519510291716, -16204597348382, -169740193999]]]
  hmulB := by decide  
  f := ![![![3062389983458221497054843, 199224056624334700489288, 189442177344632170094266]], ![![35425687163446215807627742, 2304621274079692816677779, 2191464622867681705382168]], ![![23781836327771331539334076, 1547129507602509608737803, 1471165618854021948771437]]]
  g := ![![![166724101519, 465408870742, -714747298830], ![-5666533248486, -6994125088825, 11148206487748], ![3263980233622, -168206952041, -169740193999]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [4, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 58], [0, 1]]
 g := ![![[25, 15], [42, 19], [57], [39, 35], [18, 1]], ![[0, 44], [30, 40], [57], [20, 24], [36, 58]]]
 h' := ![![[18, 58], [9, 29], [36, 45], [21, 23], [46, 25], [0, 1]], ![[0, 1], [0, 30], [20, 14], [22, 36], [24, 34], [18, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [15, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [4, 41, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1102, -62, 94]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, -60, 94]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3062389983458221497054843, -199224056624334700489288, -189442177344632170094266]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-3062389983458221497054843, -199224056624334700489288, -189442177344632170094266]] 
 ![![59, 0, 0], ![6, 1, 0], ![45, 0, 1]] where
  M :=![![![-3062389983458221497054843, -199224056624334700489288, -189442177344632170094266], ![-35425687163446215807627742, -2304621274079692816677779, -2191464622867681705382168], ![-37254898588750588991496856, -2423620788361408089645370, -2304621274079692816677779]]]
  hmulB := by decide  
  f := ![![![3028729389319, -1013473317068, 714747298830]], ![![2573391885036, -100188130651, -116266486352]], ![![-902147250379, -498333930842, 548023197311]]]
  g := ![![![112844954860953124747845, -199224056624334700489288, -189442177344632170094266], ![1305388957797925726010788, -2304621274079692816677779, -2191464622867681705382168], ![1372792940254305699947041, -2423620788361408089645370, -2304621274079692816677779]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-3028729389319, 1013473317068, -714747298830]] ![![-3062389983458221497054843, -199224056624334700489288, -189442177344632170094266]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [57, 31, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 27, 30], [38, 33, 31], [0, 1]]
 g := ![![[43, 16, 58], [57, 46], [21, 28, 16], [1, 14, 58], [1]], ![[14, 15, 15, 53], [39, 1], [12, 24, 0, 44], [24, 42, 6, 2], [18, 44, 55, 38]], ![[35, 9, 29, 51], [54, 46], [29, 12, 27, 44], [41, 20, 58, 11], [57, 8, 51, 23]]]
 h' := ![![[50, 27, 30], [25, 40, 34], [23, 26, 30], [4, 41, 4], [4, 30, 27], [0, 1]], ![[38, 33, 31], [30, 35, 4], [22, 6, 1], [18, 26, 20], [22, 25, 22], [50, 27, 30]], ![[0, 1], [49, 47, 23], [57, 29, 30], [44, 55, 37], [17, 6, 12], [38, 33, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 58], []]
 b := ![[], [2, 52, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [57, 31, 34, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-145363, 9028, 3782]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2383, 148, 62]
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

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18456085782, 767677068, 787124531]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-18456085782, 767677068, 787124531]] 
 ![![67, 0, 0], ![0, 67, 0], ![46, 63, 1]] where
  M :=![![![-18456085782, 767677068, 787124531], ![147192287297, -21604583906, 8444447748], ![143555611716, 10310408755, -21604583906]]]
  hmulB := by decide  
  f := ![![![5667049817302611688, 368670437074861739, 350568759142152850]], ![![65556357959582582950, 4264774780734000288, 4055374807823479129]], ![![66562331563919731473, 4330218484310489696, 4117605232748540545]]]
  g := ![![![-815877824, -728674155, 787124531], ![-3600780733, -8262758090, 8444447748], ![16975618976, 20468644699, -21604583906]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [23, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 66], [0, 1]]
 g := ![![[58, 35], [17, 9], [36], [49], [36], [1]], ![[0, 32], [4, 58], [36], [49], [36], [1]]]
 h' := ![![[6, 66], [11, 54], [62, 64], [35, 61], [36, 7], [44, 6], [0, 1]], ![[0, 1], [0, 13], [44, 3], [66, 6], [11, 60], [13, 61], [6, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [31, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [23, 61, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![397, -52, -54]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![43, 50, -54]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5667049817302611688, 368670437074861739, 350568759142152850]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![5667049817302611688, 368670437074861739, 350568759142152850]] 
 ![![67, 0, 0], ![44, 1, 0], ![25, 0, 1]] where
  M :=![![![5667049817302611688, 368670437074861739, 350568759142152850], ![65556357959582582950, 4264774780734000288, 4055374807823479129], ![68941371732999145193, 4484987157117151494, 4264774780734000288]]]
  hmulB := by decide  
  f := ![![![-18456085782, 767677068, 787124531]], ![![-9923514733, 181689658, 642954136]], ![![-4743978102, 440333365, -28753293]]]
  g := ![![![-288338334217091434, 368670437074861739, 350568759142152850], ![-3335494068482095641, 4264774780734000288, 4055374807823479129], ![-3507722876097097429, 4484987157117151494, 4264774780734000288]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-18456085782, 767677068, 787124531]] ![![5667049817302611688, 368670437074861739, 350568759142152850]]
  ![![67, 0, 0]] where
 M := ![![![67, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [39, 45, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 41, 5], [33, 29, 66], [0, 1]]
 g := ![![[21, 47, 27], [7, 5, 57], [30, 36, 32], [3, 45], [66, 1], []], ![[66, 60, 47, 57], [65, 30, 17, 24], [46, 55, 34, 45], [32, 25], [5, 60], [1, 25]], ![[12, 36, 15, 66], [34, 14, 64, 51], [27, 44, 15, 28], [4, 57], [29, 48], [11, 25]]]
 h' := ![![[33, 41, 5], [11, 7, 13], [37, 51, 46], [65, 5, 48], [53, 44, 51], [0, 0, 1], [0, 1]], ![[33, 29, 66], [47, 53, 57], [36, 56, 27], [7, 51, 68], [30, 34, 66], [56, 53, 29], [33, 41, 5]], ![[0, 1], [18, 11, 1], [59, 35, 69], [31, 15, 26], [20, 64, 25], [21, 18, 41], [33, 29, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 6], []]
 b := ![[], [7, 35, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [39, 45, 5, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14126444, -98477, -5183]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![198964, -1387, -73]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-111574441736438717178962, -7258485372012401159325, -6902094538166488216358]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-111574441736438717178962, -7258485372012401159325, -6902094538166488216358]] 
 ![![73, 0, 0], ![36, 1, 0], ![68, 0, 1]] where
  M :=![![![-111574441736438717178962, -7258485372012401159325, -6902094538166488216358], ![-1290691678637133296458946, -83966063583772764313530, -79843339092136412752575], ![-1357336764566319016793775, -88301665660780695040786, -83966063583772764313530]]]
  hmulB := by decide  
  f := ![![![1778010463050, -237419210138, 79607711865]], ![![1080753682035, -97089204786, 3483100214]], ![![1048045468378, -189609566399, 94149370170]]]
  g := ![![![8480458359607245524234, -7258485372012401159325, -6902094538166488216358], ![98101831077314551863058, -83966063583772764313530, -79843339092136412752575], ![103167335930388136684857, -88301665660780695040786, -83966063583772764313530]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1613335720133617, 104955700808230, 99802387436248]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![1613335720133617, 104955700808230, 99802387436248]] 
 ![![73, 0, 0], ![40, 1, 0], ![47, 0, 1]] where
  M :=![![![1613335720133617, 104955700808230, 99802387436248], ![18663046450578376, 1214126170388625, 1154512708890530], ![19626716051139010, 1276817783183296, 1214126170388625]]]
  hmulB := by decide  
  f := ![![![-259196255, 129658, 21182900]], ![![-87762300, -4640295, 11626606]], ![![-166547643, 5009378, 8926965]]]
  g := ![![![-99665815365743, 104955700808230, 99802387436248], ![-1152932844970158, 1214126170388625, 1154512708890530], ![-1212464729924085, 1276817783183296, 1214126170388625]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-134901121340786679386, -8776004617914065882, -8345103755914142727]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![-134901121340786679386, -8776004617914065882, -8345103755914142727]] 
 ![![73, 0, 0], ![70, 1, 0], ![39, 0, 1]] where
  M :=![![![-134901121340786679386, -8776004617914065882, -8345103755914142727], ![-1560534402355944689949, -101520706317130108478, -96536050797054724702], ![-1641112863549930319934, -106762745378884162831, -101520706317130108478]]]
  hmulB := by decide  
  f := ![![![-57601525122, 8256367459, -3116077658]], ![![-63216620282, 7298746680, -1743909507]], ![![-9623544725, 3232870423, -2283071824]]]
  g := ![![![11025729430052732859, -8776004617914065882, -8345103755914142727], ![127545493437373933793, -101520706317130108478, -96536050797054724702], ![134131326840274456286, -106762745378884162831, -101520706317130108478]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-111574441736438717178962, -7258485372012401159325, -6902094538166488216358]] ![![1613335720133617, 104955700808230, 99802387436248]]
  ![![-450937931624785863293380572264331047334, -29335807819821493492808598323164691353, -27895422880731783213060901452637634576]] where
 M := ![![![-450937931624785863293380572264331047334, -29335807819821493492808598323164691353, -27895422880731783213060901452637634576]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![-450937931624785863293380572264331047334, -29335807819821493492808598323164691353, -27895422880731783213060901452637634576]] ![![-134901121340786679386, -8776004617914065882, -8345103755914142727]]
  ![![73, 0, 0]] where
 M := ![![![152391107278746570897585218008368089100037624178233974805905, 9913817230835471485205075780123164582454565817167474693978, 9427049894620001214633817775805743837405861321695087276952]]]
 hmul := by decide  
 g := ![![![![2087549414777350286268290657648877932877227728468958558985, 135805715490896869660343503837303624417185833111883214986, 129137669789315085131970106517886901882272072899932702424]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![753674, -121716, 53787]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![753674, -121716, 53787]] 
 ![![79, 0, 0], ![26, 1, 0], ![75, 0, 1]] where
  M :=![![![753674, -121716, 53787], ![10058169, 538526, -1338876], ![-22760892, 1401243, 538526]]]
  hmulB := by decide  
  f := ![![![-2166100875544, -140915887857, -133996933254]], ![![-1030076573198, -67011724390, -63721456089]], ![![-2389985274621, -155480707635, -147846621982]]]
  g := ![![![-1465, -121716, 53787], ![1221167, 538526, -1338876], ![-1260540, 1401243, 538526]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4694996, 570070, -928013]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![4694996, 570070, -928013]] 
 ![![79, 0, 0], ![57, 1, 0], ![35, 0, 1]] where
  M :=![![![4694996, 570070, -928013], ![-173538431, 8407048, 6270770], ![106603090, -18056501, 8407048]]]
  hmulB := by decide  
  f := ![![![-183906620850074, -11964061809153, -11376627689524]], ![![-159621604637914, -10384197888781, -9874334913969]], ![![-109797611241319, -7142893503869, -6792178218042]]]
  g := ![![![59259, 570070, -928013], ![-11040723, 8407048, 6270770], ![10652873, -18056501, 8407048]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12632120148518010273787154, 821783715773469593655678, 781434225667064627710681]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![12632120148518010273787154, 821783715773469593655678, 781434225667064627710681]] 
 ![![79, 0, 0], ![75, 1, 0], ![56, 0, 1]] where
  M :=![![![12632120148518010273787154, 821783715773469593655678, 781434225667064627710681], ![146128200199741085381897347, 9506383245849751762944430, 9039620873508165530212458], ![153673554849638814013611786, 9997246973246220296458865, 9506383245849751762944430]]]
  hmulB := by decide  
  f := ![![![30394760484730, -1564830336475, -1010482420306]], ![![26463883845032, -1049690950249, -1177206521825]], ![![17841560939545, -1247460489138, -280383865458]]]
  g := ![![![-1174202217365162384837808, 821783715773469593655678, 781434225667064627710681], ![-13583155850068956538364969, 9506383245849751762944430, 9039620873508165530212458], ![-14284524429258402619565711, 9997246973246220296458865, 9506383245849751762944430]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![753674, -121716, 53787]] ![![4694996, 570070, -928013]]
  ![![30394760484730, -1564830336475, -1010482420306]] where
 M := ![![![30394760484730, -1564830336475, -1010482420306]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![30394760484730, -1564830336475, -1010482420306]] ![![12632120148518010273787154, 821783715773469593655678, 781434225667064627710681]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB276I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB276I1 : PrimesBelowBoundCertificateInterval O 31 79 276 where
  m := 11
  g := ![3, 1, 3, 1, 3, 2, 1, 2, 1, 3, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB276I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0, I73N1, I73N2]
    · exact ![I79N0, I79N1, I79N2]
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
    · exact ![37, 37, 37]
    · exact ![68921]
    · exact ![43, 43, 43]
    · exact ![103823]
    · exact ![53, 53, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![357911]
    · exact ![73, 73, 73]
    · exact ![79, 79, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I37N0, I37N1, I37N2, I43N0, I43N1, I43N2, I53N0, I53N1, I53N2, I59N1, I67N1, I73N0, I73N1, I73N2, I79N0, I79N1, I79N2]
  Il := ![[I37N0, I37N1, I37N2], [], [I43N0, I43N1, I43N2], [], [I53N0, I53N1, I53N2], [I59N1], [], [I67N1], [], [I73N0, I73N1, I73N2], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
