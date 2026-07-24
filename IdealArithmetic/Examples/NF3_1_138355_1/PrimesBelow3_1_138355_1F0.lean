
import IdealArithmetic.Examples.NF3_1_138355_1.RI3_1_138355_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-32580153789079, -8955885360749, -2287587899801]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-32580153789079, -8955885360749, -2287587899801]] 
 ![![2, 0, 0], ![0, 2, 0], ![1, 1, 1]] where
  M :=![![![-32580153789079, -8955885360749, -2287587899801], ![-160131152986070, -44018093288084, -11243473260550], ![-787043128238500, -216348519288820, -55261566548634]]]
  hmulB := by decide  
  f := ![![![1686872, 1821023, -440333]], ![![-30823310, -514793, 1380690]], ![![33755931, -11306815, 903127]]]
  g := ![![![-15146282944639, -3334148730474, -2287587899801], ![-74443839862760, -16387310013767, -11243473260550], ![-365890780844933, -80543476370093, -55261566548634]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [0, 1]]
 g := ![![[1]], ![[1]]]
 h' := ![![[1, 1], [0, 1]], ![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], []]
 b := ![[], [1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-209, 617, 43]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-126, 287, 43]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1686872, 1821023, -440333]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![1686872, 1821023, -440333]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![1686872, 1821023, -440333], ![-30823310, -514793, 1380690], ![96648300, -23919860, 865897]]]
  hmulB := by decide  
  f := ![![![-32580153789079, -8955885360749, -2287587899801]], ![![-80065576493035, -22009046644042, -5621736630275]], ![![-393521564119250, -108174259644410, -27630783274317]]]
  g := ![![![843436, 1821023, -440333], ![-15411655, -514793, 1380690], ![48324150, -23919860, 865897]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-32580153789079, -8955885360749, -2287587899801]] ![![1686872, 1821023, -440333]]
  ![![2, 0, 0]] where
 M := ![![![2, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0)
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![90637, 24915, 6364]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![90637, 24915, 6364]] 
 ![![3, 0, 0], ![0, 3, 0], ![1, 0, 1]] where
  M :=![![![90637, 24915, 6364], ![445480, 122457, 31279], ![2189530, 601875, 153736]]]
  hmulB := by decide  
  f := ![![![409, 20, -21]], ![![-1470, 304, -1]], ![![113, -485, 94]]]
  g := ![![![28091, 8305, 6364], ![138067, 40819, 31279], ![678598, 200625, 153736]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [1, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 2], [0, 1]]
 g := ![![[0, 1]], ![[0, 2]]]
 h' := ![![[0, 2], [0, 1]], ![[0, 1], [0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [0, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [1, 0, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4027, -63, 133]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1298, -21, 133]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![409, 20, -21]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![409, 20, -21]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![409, 20, -21], ![-1470, 304, -1], ![-70, -1475, 303]]]
  hmulB := by decide  
  f := ![![![90637, 24915, 6364]], ![![208918, 57429, 14669]], ![![790268, 217235, 55488]]]
  g := ![![![137, 20, -21], ![-692, 304, -1], ![758, -1475, 303]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![90637, 24915, 6364]] ![![409, 20, -21]]
  ![![3, 0, 0]] where
 M := ![![![3, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -1, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, -1, 0]] 
 ![![5, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![5, -1, 0], ![0, 5, -1], ![-70, -5, 4]]]
  hmulB := by decide  
  f := ![![![15, 4, 1]], ![![14, 4, 1]], ![![70, 19, 5]]]
  g := ![![![1, -1, 0], ![0, 5, -1], ![-14, -5, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![171, 47, 12]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![171, 47, 12]] 
 ![![5, 0, 0], ![4, 1, 0], ![4, 0, 1]] where
  M :=![![![171, 47, 12], ![840, 231, 59], ![4130, 1135, 290]]]
  hmulB := by decide  
  f := ![![![25, -10, 1]], ![![34, -2, -1]], ![![-106, -3, 5]]]
  g := ![![![-13, 47, 12], ![-64, 231, 59], ![-314, 1135, 290]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, -1, 0]] ![![5, -1, 0]]
  ![![25, -10, 1]] where
 M := ![![![25, -10, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![25, -10, 1]] ![![171, 47, 12]]
  ![![5, 0, 0]] where
 M := ![![![5, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![941844946614943, 258901643745821, 66130845094024]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![941844946614943, 258901643745821, 66130845094024]] 
 ![![7, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![941844946614943, 258901643745821, 66130845094024], ![4629159156581680, 1272499172085063, 325032488839845], ![22752274218789150, 6254321600780905, 1597531660924908]]]
  hmulB := by decide  
  f := ![![![-47710521, 29002252, -3925767]], ![![-39257670, -9619908, 3582355]], ![![250764850, -21345895, -6037553]]]
  g := ![![![134549278087849, 258901643745821, 66130845094024], ![661308450940240, 1272499172085063, 325032488839845], ![3250324888398450, 6254321600780905, 1597531660924908]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1822566557398687153, -501001230874147646, -127969966939958444]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-1822566557398687153, -501001230874147646, -127969966939958444]] 
 ![![7, 0, 0], ![3, 1, 0], ![5, 0, 1]] where
  M :=![![![-1822566557398687153, -501001230874147646, -127969966939958444], ![-8957897685797091080, -2462416392098479373, -628971197814106090], ![-44027983846987426300, -12102753674867621530, -3091387589912585463]]]
  hmulB := by decide  
  f := ![![![4182963001, -1064429222, 43411472]], ![![2226813149, 172390385, -127254762]], ![![-7222346785, -1055490260, 513722853]]]
  g := ![![![45755281417649715, -501001230874147646, -127969966939958444], ![224886782795553927, -2462416392098479373, -628971197814106090], ![1105316446739766515, -12102753674867621530, -3091387589912585463]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![941844946614943, 258901643745821, 66130845094024]] ![![-1822566557398687153, -501001230874147646, -127969966939958444]]
  ![![-6947397316902416162569485588735159, -1909754457531433092247774012061131, -487805617497828563870450348151694]] where
 M := ![![![-6947397316902416162569485588735159, -1909754457531433092247774012061131, -487805617497828563870450348151694]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![-6947397316902416162569485588735159, -1909754457531433092247774012061131, -487805617497828563870450348151694]] ![![-1822566557398687153, -501001230874147646, -127969966939958444]]
  ![![7, 0, 0]] where
 M := ![![![51246576893973339188469016389916027231920650392676007, 14087056518041315415581270253563481088558321396208397, 3598234985869564837021778218786435534421316044344708]]]
 hmul := by decide  
 g := ![![![![7320939556281905598352716627130861033131521484668001, 2012436645434473630797324321937640155508331628029771, 514033569409937833860254031255205076345902292049244]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0]] 
 ![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [1, 6, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 1, 1], [9, 9, 10], [0, 1]]
 g := ![![[5, 3, 5], [10, 4, 1], []], ![[8, 0, 3, 3], [9, 7, 10, 4], [6, 1]], ![[4, 4, 10, 7], [9, 9, 10, 10], [8, 1]]]
 h' := ![![[6, 1, 1], [1, 2, 4], [0, 0, 1], [0, 1]], ![[9, 9, 10], [1, 1, 5], [8, 8, 9], [6, 1, 1]], ![[0, 1], [3, 8, 2], [7, 3, 1], [9, 9, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4], []]
 b := ![[], [5, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [1, 6, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-140195, -13772, -2332]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12745, -1252, -212]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2226813149, -172390385, 127254762]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-2226813149, -172390385, 127254762]] 
 ![![13, 0, 0], ![3, 1, 0], ![4, 0, 1]] where
  M :=![![![-2226813149, -172390385, 127254762], ![8907833340, -1590539339, -45135623], ![-3159493610, 8682155225, -1635674962]]]
  hmulB := by decide  
  f := ![![![2993479857941410293, 822870960370391080, 210184652462267173]], ![![1822566557398687153, 501001230874147646, 127969966939958444]], ![![6483677871542439914, 1782283659846427515, 455245949456497931]]]
  g := ![![![-170666234, -172390385, 127254762], ![1066153373, -1590539339, -45135623], ![-1743327649, 8682155225, -1635674962]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-209897309023, -57698200239, -14737761750]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-209897309023, -57698200239, -14737761750]] 
 ![![13, 0, 0], ![4, 1, 0], ![10, 0, 1]] where
  M :=![![![-209897309023, -57698200239, -14737761750], ![-1031643322500, -283586117773, -72435961989], ![-5070517339230, -1393823132445, -356022079762]]]
  hmulB := by decide  
  f := ![![![823079, 484368, -132621]], ![![-460858, 161342, -13749]], ![![2527160, -206235, -62653]]]
  g := ![![![12944085341, -57698200239, -14737761750], ![63620059114, -283586117773, -72435961989], ![312691999090, -1393823132445, -356022079762]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3523791, -968647, -247420]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![-3523791, -968647, -247420]] 
 ![![13, 0, 0], ![5, 1, 0], ![1, 0, 1]] where
  M :=![![![-3523791, -968647, -247420], ![-17319400, -4760891, -1216067], ![-85124690, -23399735, -5976958]]]
  hmulB := by decide  
  f := ![![![-7333, 2126, -129]], ![![-3515, 204, 104]], ![![10189, 237, -470]]]
  g := ![![![120528, -968647, -247420], ![592394, -4760891, -1216067], ![2911611, -23399735, -5976958]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-2226813149, -172390385, 127254762]] ![![-209897309023, -57698200239, -14737761750]]
  ![![-7333, 2126, -129]] where
 M := ![![![-7333, 2126, -129]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-7333, 2126, -129]] ![![-3523791, -968647, -247420]]
  ![![13, 0, 0]] where
 M := ![![![13, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [15, 5, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 13, 13], [5, 3, 4], [0, 1]]
 g := ![![[0, 6, 2], [9, 9], [5, 1], []], ![[11, 3, 15, 16], [14, 1], [5, 9], [10, 16]], ![[10, 2, 4, 2], [12, 4], [4, 16], [2, 16]]]
 h' := ![![[0, 13, 13], [16, 6, 11], [10, 11, 3], [0, 0, 1], [0, 1]], ![[5, 3, 4], [15, 16, 9], [2, 4, 16], [3, 16, 3], [0, 13, 13]], ![[0, 1], [8, 12, 14], [16, 2, 15], [12, 1, 13], [5, 3, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 12], []]
 b := ![[], [10, 13, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [15, 5, 12, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4675, -340, -340]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-275, -20, -20]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10977876086525098953143197, 3017683721566187944107214, 770802270106763696806113]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![10977876086525098953143197, 3017683721566187944107214, 770802270106763696806113]] 
 ![![19, 0, 0], ![0, 19, 0], ![16, 1, 1]] where
  M :=![![![10977876086525098953143197, 3017683721566187944107214, 770802270106763696806113], ![53956158907473458776427910, 14831887437058917437173762, 3788485991672951640913327], ![265194019417106614863932890, 72898588865838216980994545, 18620373428731869078087089]]]
  hmulB := by decide  
  f := ![![![4842781945137, 2406868081, -200959756112]], ![![-14067182927840, 3837983164577, -198552888031]], ![![2606243475378, -588602858638, 11869541617]]]
  g := ![![![-71313696588585273460769, 118256918497864434068479, 770802270106763696806113], ![-350506155752303551483438, 581231655020313989276865, 3788485991672951640913327], ![-1722734496979120546603186, 2856748180900334100153024, 18620373428731869078087089]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [17, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 18], [0, 1]]
 g := ![![[14, 9], [4, 6], [5], [1]], ![[0, 10], [1, 13], [5], [1]]]
 h' := ![![[9, 18], [8, 16], [14, 5], [2, 9], [0, 1]], ![[0, 1], [0, 3], [2, 14], [7, 10], [9, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [8, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [17, 10, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2758, 493, 417]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-206, 4, 417]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4842781945137, 2406868081, -200959756112]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![4842781945137, 2406868081, -200959756112]] 
 ![![19, 0, 0], ![17, 1, 0], ![15, 0, 1]] where
  M :=![![![4842781945137, 2406868081, -200959756112], ![-14067182927840, 3837983164577, -198552888031], ![-13898702162170, -15059947367995, 3639430276546]]]
  hmulB := by decide  
  f := ![![![10977876086525098953143197, 3017683721566187944107214, 770802270106763696806113]], ![![12662108019915796893676961, 3480658458088637499315600, 889059188604628130874592]], ![![22624324248157005219004255, 6219149720491107165400145, 1588547762122806554219936]]]
  g := ![![![411382185760, 2406868081, -200959756112], ![-4017610705536, 3837983164577, -198552888031], ![9869944681345, -15059947367995, 3639430276546]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![10977876086525098953143197, 3017683721566187944107214, 770802270106763696806113]] ![![4842781945137, 2406868081, -200959756112]]
  ![![19, 0, 0]] where
 M := ![![![19, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [9, 21, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 4, 7], [9, 18, 16], [0, 1]]
 g := ![![[15, 1, 13], [14, 8, 16], [8, 12, 1], []], ![[3, 0, 22, 11], [2, 10, 12, 17], [16, 10, 18, 14], [0, 3]], ![[8, 21, 15, 8], [22, 3, 12, 2], [12, 12, 18, 3], [14, 3]]]
 h' := ![![[3, 4, 7], [12, 11, 17], [20, 0, 19], [0, 0, 1], [0, 1]], ![[9, 18, 16], [14, 16, 15], [7, 12, 20], [9, 20, 18], [3, 4, 7]], ![[0, 1], [13, 19, 14], [16, 11, 7], [1, 3, 4], [9, 18, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 22], []]
 b := ![[], [20, 11, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [9, 21, 11, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4692, -1449, 483]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-204, -63, 21]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀

instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0]] 
 ![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [9, 4, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 18, 23], [20, 10, 6], [0, 1]]
 g := ![![[19, 9, 13], [23, 4], [2, 6, 7], [1]], ![[27, 11, 15, 1], [26, 20], [19, 1, 5, 25], [3, 15, 21, 16]], ![[4, 19, 12, 13], [17, 25], [15, 8, 12, 28], [24, 13, 16, 13]]]
 h' := ![![[3, 18, 23], [1, 0, 19], [11, 19, 2], [20, 25, 23], [0, 1]], ![[20, 10, 6], [7, 18, 16], [3, 2, 22], [0, 20, 22], [3, 18, 23]], ![[0, 1], [5, 11, 23], [19, 8, 5], [12, 13, 13], [20, 10, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 15], []]
 b := ![[], [23, 27, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [9, 4, 6, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54259, 10179, 2639]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1871, 351, 91]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6424228844052334096903, 1765941850091438805950, 451071786350279288296]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![6424228844052334096903, 1765941850091438805950, 451071786350279288296]] 
 ![![31, 0, 0], ![0, 31, 0], ![12, 10, 1]] where
  M :=![![![6424228844052334096903, 1765941850091438805950, 451071786350279288296], ![31575025044519550180720, 8679587775803730538383, 2217013636441718094246], ![155190954550920266597220, 42660093226728140651950, 10896601412245448632629]]]
  hmulB := by decide  
  f := ![![![28495710297, 25015330150, -6269196828]], ![![-438843777960, -2850273843, 18746133322]], ![![-88201933016, -2368770580, 4133123573]]]
  g := ![![![32624755091902665721, -88541161722946905710, 451071786350279288296], ![160350367974804291928, -435178986729466142067, 2217013636441718094246], ![788120567870157516312, -2138900674055688570140, 10896601412245448632629]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [3, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 30], [0, 1]]
 g := ![![[18, 2], [22, 4], [25, 1], [8, 1]], ![[3, 29], [23, 27], [2, 30], [16, 30]]]
 h' := ![![[8, 30], [27, 23], [18, 29], [7, 30], [0, 1]], ![[0, 1], [25, 8], [2, 2], [30, 1], [8, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [24, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [3, 23, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2467, -170, 138]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-133, -50, 138]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28495710297, 25015330150, -6269196828]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![28495710297, 25015330150, -6269196828]] 
 ![![31, 0, 0], ![20, 1, 0], ![3, 0, 1]] where
  M :=![![![28495710297, 25015330150, -6269196828], ![-438843777960, -2850273843, 18746133322], ![1312229332540, -345113111350, 15895859479]]]
  hmulB := by decide  
  f := ![![![6424228844052334096903, 1765941850091438805950, 451071786350279288296]], ![![5163212965340846197380, 1419304025084919569593, 362530624627332382586]], ![![5627859389776686093159, 1547029637967821195800, 395155379719235048307]]]
  g := ![![![-14613009749, 25015330150, -6269196828], ![-14131506486, -2850273843, 18746133322], ![263445289713, -345113111350, 15895859479]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![6424228844052334096903, 1765941850091438805950, 451071786350279288296]] ![![28495710297, 25015330150, -6269196828]]
  ![![31, 0, 0]] where
 M := ![![![31, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)


lemma PB106I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB106I0 : PrimesBelowBoundCertificateInterval O 1 31 106 where
  m := 11
  g := ![2, 2, 3, 3, 1, 3, 1, 2, 1, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB106I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N1]
    · exact ![I5N0, I5N0, I5N1]
    · exact ![I7N0, I7N1, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
    · exact ![I29N0]
    · exact ![I31N0, I31N1]
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
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![4, 2]
    · exact ![9, 3]
    · exact ![5, 5, 5]
    · exact ![7, 7, 7]
    · exact ![1331]
    · exact ![13, 13, 13]
    · exact ![4913]
    · exact ![361, 19]
    · exact ![12167]
    · exact ![24389]
    · exact ![961, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I7N0, I7N1, I13N0, I13N1, I13N2, I19N1, I31N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N1], [I5N0, I5N0, I5N1], [I7N0, I7N1, I7N1], [], [I13N0, I13N1, I13N2], [], [I19N1], [], [], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
