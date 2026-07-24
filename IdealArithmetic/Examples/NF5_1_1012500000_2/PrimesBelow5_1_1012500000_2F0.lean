
import IdealArithmetic.Examples.NF5_1_1012500000_2.RI5_1_1012500000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-971, 373, -786, -276, 2891]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-971, 373, -786, -276, 2891]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-971, 373, -786, -276, 2891], ![9852, -1579, 836, 56, -1824], ![-16848, 76, 6989, 3140, -29328], ![-69336, 18568, -30128, -9715, 106248], ![-12740, 1933, -762, 50, 1126]]]
  hmulB := by decide  
  f := ![![![-3998, -913, 1958, 706, -6833]], ![![-9228, 1027, -3016, -660, 9078]], ![![49536, 6636, -13019, -5332, 47592]], ![![91224, -28280, 73392, 19765, -233448]], ![![20697, -1638, 5164, 994, -15083]]]
  g := ![![![-1931, 373, -786, -276, 2891], ![5838, -1579, 836, 56, -1824], ![6240, 76, 6989, 3140, -29328], ![-87792, 18568, -30128, -9715, 106248], ![-6933, 1933, -762, 50, 1126]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -2, 0, 0, -1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-2, -2, 0, 0, -1]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-2, -2, 0, 0, -1], ![-12, -10, 5, 2, -24], ![-108, -32, 8, 5, -60], ![-270, -158, 13, 8, -150], ![-56, -23, 3, 2, -29]]]
  hmulB := by decide  
  f := ![![![-14, -1, 2, 1, -8]], ![![-3, 4, -10, -3, 33]], ![![126, 3, -2, -4, 18]], ![![-144, -74, 177, 58, -600]], ![![19, -7, 18, 5, -58]]]
  g := ![![![-1, -2, 0, 0, -1], ![-6, -10, 5, 2, -24], ![-54, -32, 8, 5, -60], ![-135, -158, 13, 8, -150], ![-28, -23, 3, 2, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3163929, 1618388, -425306, -204313, 2686148]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![3163929, 1618388, -425306, -204313, 2686148]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![3163929, 1618388, -425306, -204313, 2686148], ![13845606, 7082195, -1861173, -894090, 11754798], ![60589476, 30992250, -8144641, -3912609, 51439932], ![265144374, 135624558, -35641599, -17121889, 225105246], ![41056174, 21000730, -5518909, -2651232, 34856331]]]
  hmulB := by decide  
  f := ![![![24, -40, 133, 51, -514]], ![![-777, 129, -67, -6, 154]], ![![2109, -230, -299, -174, 1480]], ![![2901, -1184, 2660, 974, -10040]], ![![1025, -208, 208, 55, -671]]]
  g := ![![![-255494, 1618388, -425306, -204313, 2686148], ![-1118062, 7082195, -1861173, -894090, 11754798], ![-4892728, 30992250, -8144641, -3912609, 51439932], ![-21410971, 135624558, -35641599, -17121889, 225105246], ![-3315373, 21000730, -5518909, -2651232, 34856331]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-971, 373, -786, -276, 2891]] ![![-2, -2, 0, 0, -1]]
  ![![-5022, 479, 662, 390, -3260]] where
 M := ![![![-5022, 479, 662, 390, -3260]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-5022, 479, 662, 390, -3260]] ![![-2, -2, 0, 0, -1]]
  ![![10060, -2570, 2981, 868, -10154]] where
 M := ![![![10060, -2570, 2981, 868, -10154]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![10060, -2570, 2981, 868, -10154]] ![![3163929, 1618388, -425306, -204313, 2686148]]
  ![![-9875927888, -5051656696, 1327555483, 637745167, -8384576134]] where
 M := ![![![-9875927888, -5051656696, 1327555483, 637745167, -8384576134]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-9875927888, -5051656696, 1327555483, 637745167, -8384576134]] ![![3163929, 1618388, -425306, -204313, 2686148]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-195898165428943678, -100204282722492148, 26333290798297306, 12650265252359062, -166315822518133948]]]
 hmul := by decide  
 g := ![![![![-97949082714471839, -50102141361246074, 13166645399148653, 6325132626179531, -83157911259066974]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34633557, -17715655, 4655774, 2236567, -29404446]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-34633557, -17715655, 4655774, 2236567, -29404446]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 3]] where
  M :=![![![-34633557, -17715655, 4655774, 2236567, -29404446], ![-151562322, -77524363, 20372942, 9787058, -128672418], ![-663233796, -339254678, 89153213, 42828386, -563077068], ![-2902370076, -1484609144, 390155848, 187426085, -2464126044], ![-449415510, -229883532, 60412618, 29021546, -381552993]]]
  hmulB := by decide  
  f := ![![![3552195, 1013209, -2225392, -774859, 7672840]], ![![7445590, -567653, 1805918, 341848, -5255154]], ![![-32295528, -5196714, 10579825, 4111874, -37926912]], ![![-85054284, 17910340, -48098880, -12251327, 150617604]], ![![-52390258, 1451034, -6592986, -547636, 16814445]]]
  g := ![![![-11544519, -17715655, 4655774, 2236567, -9801482], ![-50520774, -77524363, 20372942, 9787058, -42890806], ![-221077932, -339254678, 89153213, 42828386, -187692356], ![-967456692, -1484609144, 390155848, 187426085, -821375348], ![-149805170, -229883532, 60412618, 29021546, -127184331]]]
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
  c := ![787560, 192881, -179792, -79916, 754779]
  a := ![-255, -244, 212, 67, -731]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![262520, 192881, -179792, -79916, 251593]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![421847535, 215776160, -56706243, -27241231, 358143904]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![421847535, 215776160, -56706243, -27241231, 358143904]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![421847535, 215776160, -56706243, -27241231, 358143904], ![1846016058, 944252901, -248138843, -119204507, 1567216098], ![8078187546, 4132157240, -1085921760, -521662871, 6858423546], ![35351424162, 18082569008, -4752092257, -2282859948, 30013144386], ![5473933814, 2799994066, -735836393, -353487589, 4647369357]]]
  hmulB := by decide  
  f := ![![![-405355851, -62030152, 125108191, 49275281, -450698136]], ![![-459652731, 54901025, -159227028, -35609000, 481856366]], ![![2631763272, 215893020, -363083318, -183439479, 1444876282]], ![![1342911885, -1756853868, 4303282218, 1270204895, -14064765682]], ![![656348680, -153860098, 408793179, 105972645, -1286358767]]]
  g := ![![![-123187572, 215776160, -56706243, -27241231, 358143904], ![-539062282, 944252901, -248138843, -119204507, 1567216098], ![-2359103465, 4132157240, -1085921760, -521662871, 6858423546], ![-10323463052, 18082569008, -4752092257, -2282859948, 30013144386], ![-1598546197, 2799994066, -735836393, -353487589, 4647369357]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-34633557, -17715655, 4655774, 2236567, -29404446]] ![![421847535, 215776160, -56706243, -27241231, 358143904]]
  ![![-91595411270534571, -46852161517064415, 12312563497482835, 5914839712580776, -77763699989544474]] where
 M := ![![![-91595411270534571, -46852161517064415, 12312563497482835, 5914839712580776, -77763699989544474]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-91595411270534571, -46852161517064415, 12312563497482835, 5914839712580776, -77763699989544474]] ![![421847535, 215776160, -56706243, -27241231, 358143904]]
  ![![-242241283214430500595569769, -123909348396029908773170951, 32562888683876377409199848, 15642905491352890517469559, -205660722638414555101384626]] where
 M := ![![![-242241283214430500595569769, -123909348396029908773170951, 32562888683876377409199848, 15642905491352890517469559, -205660722638414555101384626]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-242241283214430500595569769, -123909348396029908773170951, 32562888683876377409199848, 15642905491352890517469559, -205660722638414555101384626]] ![![421847535, 215776160, -56706243, -27241231, 358143904]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-640652609957955327769433287508666571, -327701564302881191940319035724288215, 86118680293768523032998472079214435, 41370604124028453153303488630261970, -543908441103777080424016722060946074]]]
 hmul := by decide  
 g := ![![![![-213550869985985109256477762502888857, -109233854767627063980106345241429405, 28706226764589507677666157359738145, 13790201374676151051101162876753990, -181302813701259026808005574020315358]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1939, -479, 388, 187, -1964]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-1939, -479, 388, 187, -1964]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-1939, -479, 388, 187, -1964], ![-6738, -1569, -756, -172, 1110], ![-2160, -12650, 3561, 1152, -17736], ![-109152, -44976, 25102, 11385, -128448], ![-9862, -7782, 3488, 1420, -17353]]]
  hmulB := by decide  
  f := ![![![58139, -21317, 54694, 15003, -174898]], ![![-103190, -27211, 59304, 20886, -205274]], ![![61768, 74390, -175183, -54944, 583516]], ![![2702548, 28288, 92138, -47091, -49664]], ![![304192, 20542, -31360, -17980, 132027]]]
  g := ![![![321, -479, 388, 187, -1964], ![206, -1569, -756, -172, 1110], ![13012, -12650, 3561, 1152, -17736], ![36340, -44976, 25102, 11385, -128448], ![7268, -7782, 3488, 1420, -17353]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-1939, -479, 388, 187, -1964]] ![![-1939, -479, 388, 187, -1964]]
  ![![5106687, 3645468, -1164898, -493114, 6456454]] where
 M := ![![![5106687, 3645468, -1164898, -493114, 6456454]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5106687, 3645468, -1164898, -493114, 6456454]] ![![-1939, -479, 388, 187, -1964]]
  ![![-41798019817, -21495712429, 5219182894, 2540029267, -34021772050]] where
 M := ![![![-41798019817, -21495712429, 5219182894, 2540029267, -34021772050]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-41798019817, -21495712429, 5219182894, 2540029267, -34021772050]] ![![-1939, -479, 388, 187, -1964]]
  ![![272884477126241, 138242434464852, -36289489057304, -17499151580308, 229781773412448]] where
 M := ![![![272884477126241, 138242434464852, -36289489057304, -17499151580308, 229781773412448]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![272884477126241, 138242434464852, -36289489057304, -17499151580308, 229781773412448]] ![![-1939, -479, 388, 187, -1964]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-1738255684307960795, -889671926863664355, 234356148830221060, 112508484604507895, -1478537724738416020]]]
 hmul := by decide  
 g := ![![![![-347651136861592159, -177934385372732871, 46871229766044212, 22501696920901579, -295707544947683204]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [6, 6, 2, 1, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 6, 0, 3, 6], [4, 5, 1, 4, 2], [1, 1, 5, 3, 3], [1, 1, 1, 4, 3], [0, 1]]
 g := ![![[0, 6, 1], []], ![[4, 5, 4, 6, 1, 5, 0, 3], [2, 5, 0, 2, 3, 6, 3, 6]], ![[0, 2, 0, 6, 2, 0, 1, 4], [2, 4, 5, 0, 0, 4, 5, 1]], ![[4, 3, 1, 5, 2, 3, 1, 5], [1, 4, 3, 4, 4, 2, 5, 6]], ![[5, 6, 4, 6, 6, 4, 1, 6], [2, 0, 6, 0, 0, 0, 4, 6]]]
 h' := ![![[0, 6, 0, 3, 6], [0, 0, 0, 1], [0, 1]], ![[4, 5, 1, 4, 2], [2, 0, 1, 3, 5], [0, 6, 0, 3, 6]], ![[1, 1, 5, 3, 3], [3, 1, 3, 5, 3], [4, 5, 1, 4, 2]], ![[1, 1, 1, 4, 3], [2, 1, 2, 3, 2], [1, 1, 5, 3, 3]], ![[0, 1], [3, 5, 1, 2, 4], [1, 1, 1, 4, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 2, 4], [], [], []]
 b := ![[], [3, 3, 4, 4], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [6, 6, 2, 1, 1, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2273687532931381721, -164705638671133336, -2208386739914809160, -742106340055352664, 6693410648263876152]
  a := ![-1719, -1664, 1434, 460, -4928]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![324812504704483103, -23529376953019048, -315483819987829880, -106015191436478952, 956201521180553736]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 16807 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14589, 402, -1831, -151, 4666]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-14589, 402, -1831, -151, 4666]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![7, 10, 3, 1, 0], ![10, 10, 4, 0, 1]] where
  M :=![![![-14589, 402, -1831, -151, 4666], ![42402, 9753, -20935, -7539, 73026], ![197802, -21744, 63996, 13949, -192438], ![-1053846, -142088, 279147, 114096, -1019670], ![-57202, -20600, 46135, 15607, -157521]]]
  hmulB := by decide  
  f := ![![![-2415, 550, -749, -223, 2542]], ![![10434, -1257, -519, -481, 3474]], ![![-1602, -3140, 10500, 4077, -40722]], ![![-3555, 464, -254, -4, 446]], ![![5524, -1662, 2761, 911, -9877]]]
  g := ![![![-5472, -4068, -1822, -151, 4666], ![-57735, -58647, -26402, -7539, 73026], ![184049, 160286, 71991, 13949, -192438], ![758562, 810332, 365049, 114096, -1019670], ![128069, 127140, 57218, 15607, -157521]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [8, 2, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1, 6], [7, 9, 5], [0, 1]]
 g := ![![[4, 10, 1], [7, 8, 1], []], ![[2, 0, 5, 8], [3, 3, 10, 2], [3, 3]], ![[1, 6, 2, 4], [3, 7, 10, 5], [4, 3]]]
 h' := ![![[1, 1, 6], [10, 10, 10], [0, 0, 1], [0, 1]], ![[7, 9, 5], [10, 5, 7], [10, 5, 9], [1, 1, 6]], ![[0, 1], [8, 7, 5], [6, 6, 1], [7, 9, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6], []]
 b := ![[], [8, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [8, 2, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-204645076, -14382178, -15572133, 785965, 17074380]
  a := ![-158, -152, 132, 42, -453]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-34626421, -17544148, -7838868, 785965, 17074380]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2415, 550, -749, -223, 2542]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-2415, 550, -749, -223, 2542]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![3, 8, 1, 0, 0], ![9, 5, 0, 1, 0], ![2, 1, 0, 0, 1]] where
  M :=![![![-2415, 550, -749, -223, 2542], ![10434, -1257, -519, -481, 3474], ![-1602, -3140, 10500, 4077, -40722], ![-121734, 23244, -23861, -5904, 74538], ![-13018, 1348, 1051, 753, -5919]]]
  hmulB := by decide  
  f := ![![![-14589, 402, -1831, -151, 4666]], ![![42402, 9753, -20935, -7539, 73026]], ![![44841, 5226, -9907, -4256, 36888]], ![![-88467, -8155, 14363, 6822, -55686]], ![![-3998, -913, 1958, 706, -6833]]]
  g := ![![![-295, 465, -749, -223, 2542], ![852, 166, -519, -481, 3474], ![1059, -6073, 10500, 4077, -40722], ![-13281, 15374, -23861, -5904, 74538], ![-1010, -446, 1051, 753, -5919]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [7, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 10], [0, 1]]
 g := ![![[7, 3], [0, 3], [1]], ![[3, 8], [7, 8], [1]]]
 h' := ![![[6, 10], [0, 6], [4, 6], [0, 1]], ![[0, 1], [3, 5], [7, 5], [6, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [9, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [7, 5, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10604481, 2050929, -1842331, -907800, 8144714]
  a := ![907, 873, -755, -242, 2600]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![728386, 1198533, -1842331, -907800, 8144714]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-14589, 402, -1831, -151, 4666]] ![![-2415, 550, -749, -223, 2542]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1399212711, 684026373, -1727401924, -485981317, 5564908196]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-1399212711, 684026373, -1727401924, -485981317, 5564908196]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 10, 4, 12, 1]] where
  M :=![![![-1399212711, 684026373, -1727401924, -485981317, 5564908196], ![23040579822, 1325659595, -1821732224, -1193666708, 8174616918], ![-9334600704, -14217821722, 33628344269, 10477034932, -111775204632], ![-398369311704, -2511233608, -17569009198, 5729915165, 20470101288], ![-44012347574, -4046554774, 7120384356, 3386287068, -27620605293]]]
  hmulB := by decide  
  f := ![![![-9766641, -4871993, 1217766, 596323, -7895786]], ![![-41080362, -21649151, 5674284, 2697586, -35647530]], ![![-184987620, -94268206, 25564609, 12227280, -159563532]], ![![-814307184, -409949796, 105630518, 51236953, -674886528]], ![![-849875506, -428968334, 111025876, 53755134, -707649153]]]
  g := ![![![-107631747, -4228081199, -1845156516, -5174221513, 5564908196], ![1772352294, -6186193045, -2655399992, -7637620748, 8174616918], ![-718046208, 84887248046, 36979166369, 103983037732, -111775204632], ![-30643793208, -15939403576, -7649954950, -18454715407, 20470101288], ![-3385565198, 20935346012, 9046369656, 25756426968, -27620605293]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 4 2 3 [2, 5, 1, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 6, 0, 6], [5, 12, 1, 1], [7, 7, 12, 6], [0, 1]]
 g := ![![[1, 12], [8, 10, 1], []], ![[5, 4, 2, 7], [3, 9, 12], [2, 7, 11, 10, 2, 8]], ![[2, 0, 4, 8, 4, 9], [1], [9, 5, 8, 12, 0, 1]], ![[4, 9, 1, 1, 4, 2], [4, 10, 10], [8, 5, 8, 5, 11, 8]]]
 h' := ![![[11, 6, 0, 6], [10, 5, 5], [0, 0, 0, 1], [0, 1]], ![[5, 12, 1, 1], [8, 11, 5], [1, 9, 11, 5], [11, 6, 0, 6]], ![[7, 7, 12, 6], [7, 8, 5, 10], [3, 0, 1], [5, 12, 1, 1]], ![[0, 1], [9, 2, 11, 3], [2, 4, 1, 7], [7, 7, 12, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [8, 3, 12], []]
 b := ![[], [], [10, 0, 12, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 4
  hpos := by decide
  P := [2, 5, 1, 3, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1358629409618, -127536885856, 1624011047585, 466793008941, -4915437397194]
  a := ![-427, -408, 356, 115, -1224]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![104509954586, 3771295160468, 1637366202797, 4573233982713, -4915437397194]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 28561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9766641, -4871993, 1217766, 596323, -7895786]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-9766641, -4871993, 1217766, 596323, -7895786]] 
 ![![13, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-9766641, -4871993, 1217766, 596323, -7895786], ![-41080362, -21649151, 5674284, 2697586, -35647530], ![-184987620, -94268206, 25564609, 12227280, -159563532], ![-814307184, -409949796, 105630518, 51236953, -674886528], ![-125941270, -63626456, 16768896, 8088326, -106071225]]]
  hmulB := by decide  
  f := ![![![-1399212711, 684026373, -1727401924, -485981317, 5564908196]], ![![1772352294, 101973815, -140133248, -91820516, 628816686]], ![![-718046208, -1093678594, 2586795713, 805925764, -8598092664]], ![![-30643793208, -193171816, -1351462246, 440762705, 1574623176]], ![![-4138987427, 57048449, -382417624, -1198627, 871827083]]]
  g := ![![![3500297, -4871993, 1217766, 596323, -7895786], ![16034796, -21649151, 5674284, 2697586, -35647530], ![71689008, -94268206, 25564609, 12227280, -159563532], ![300761424, -409949796, 105630518, 51236953, -674886528], ![47427485, -63626456, 16768896, 8088326, -106071225]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-1399212711, 684026373, -1727401924, -485981317, 5564908196]] ![![-9766641, -4871993, 1217766, 596323, -7895786]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [3, 7, 13, 3, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 0, 10, 14, 12], [13, 13, 16, 12, 13], [11, 4, 7, 0, 3], [11, 16, 1, 8, 6], [0, 1]]
 g := ![![[6, 0, 15, 11, 4], [4, 14, 0, 1], [], []], ![[12, 14, 11, 9, 12, 12, 3, 7], [14, 3, 9, 1], [5, 16, 6, 13], [1, 4, 13, 8]], ![[16, 9, 0, 5, 11, 9, 4, 8], [2, 12, 5, 13], [8, 1, 4, 16], [3, 2, 6, 16]], ![[3, 6, 7, 0, 16, 0, 15, 10], [4, 6, 6, 8], [10, 11, 1, 15], [9, 15, 0, 9]], ![[8, 0, 1, 16, 6, 14, 4, 12], [2, 3, 6, 16], [11, 14, 5, 8], [13, 2, 11, 2]]]
 h' := ![![[16, 0, 10, 14, 12], [5, 15, 3, 7, 2], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[13, 13, 16, 12, 13], [11, 13, 15, 1, 11], [6, 10, 5, 4, 16], [15, 15, 2, 6, 9], [16, 0, 10, 14, 12]], ![[11, 4, 7, 0, 3], [7, 7, 4, 8, 7], [8, 11, 9, 5, 9], [7, 5, 4, 8, 13], [13, 13, 16, 12, 13]], ![[11, 16, 1, 8, 6], [5, 5, 6, 15, 3], [0, 13, 2, 13, 12], [9, 14, 16, 11, 7], [11, 4, 7, 0, 3]], ![[0, 1], [9, 11, 6, 3, 11], [10, 0, 1, 12, 13], [14, 0, 11, 9, 5], [11, 16, 1, 8, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 4, 13, 2], [], [], []]
 b := ![[], [12, 2, 9, 1, 14], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 5
  hpos := by decide
  P := [3, 7, 13, 3, 0, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1402911538665753, 490573699319010, -1181962551421652, -397669980130222, 4039076320102062]
  a := ![270, 258, -224, -82, 774]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![82524208156809, 28857276430530, -69527208907156, -23392351772366, 237592724711886]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 1419857 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-32791883, -6885354, 14610122, 5350236, -51264434]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-32791883, -6885354, 14610122, 5350236, -51264434]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![15, 10, 2, 6, 1]] where
  M :=![![![-32791883, -6885354, 14610122, 5350236, -51264434], ![-133651968, 17212941, -49302016, -11266674, 150014472], ![786173004, 97529844, -187887813, -78930784, 693545436], ![1218774672, -453510932, 1162520592, 319360131, -3719051808], ![336328280, -21313270, 71169816, 12279954, -203066321]]]
  hmulB := by decide  
  f := ![![![-919249, -472526, 125838, 60196, -789686]], ![![-4058592, -2059881, 540576, 260506, -3421896]], ![![-17617212, -9030244, 2355441, 1132224, -14914956]], ![![-77079312, -39565596, 10457648, 5011977, -65845152]], ![![-29685109, -15224458, 4018932, 1927188, -25322263]]]
  g := ![![![38746033, 26618894, 6165210, 16470360, -51264434], ![-125466792, -78049041, -18385840, -47965974, 150014472], ![-506158344, -359890764, -82893615, -223168600, 693545436], ![3000239568, 1933526692, 452664432, 1191245841, -3719051808], ![178017005, 105755260, 25121182, 64772520, -203066321]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [4, 10, 14, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 0, 18, 10], [16, 15, 7, 7], [18, 3, 13, 2], [0, 1]]
 g := ![![[9, 11, 17, 11], [5, 8, 10, 4], [1], []], ![[11, 3, 7, 6, 16, 14], [18, 14, 15, 13, 9, 8], [11, 12, 5], [10, 8, 5]], ![[2, 15, 6, 17, 9, 17], [16, 8, 0, 15, 15, 9], [1], [10, 0, 11]], ![[8, 0, 7, 11, 3, 15], [13, 18, 5, 4, 6, 14], [11, 12, 5], [18, 6, 4]]]
 h' := ![![[2, 0, 18, 10], [18, 10, 4, 12], [15, 9, 5, 17], [0, 0, 1], [0, 1]], ![[16, 15, 7, 7], [12, 8, 14, 16], [17, 17, 4, 15], [2, 1, 3, 10], [2, 0, 18, 10]], ![[18, 3, 13, 2], [17, 13, 12, 4], [7, 9, 10, 17], [7, 0, 18], [16, 15, 7, 7]], ![[0, 1], [5, 7, 8, 6], [0, 3, 0, 8], [5, 18, 16, 9], [18, 3, 13, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [5, 4, 18], []]
 b := ![[], [], [0, 3, 5, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [4, 10, 14, 2, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![841516330785, 149923838982, -237831359109, -97334445418, 907644130242]
  a := ![-59, -57, 54, 28, -170]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-672270822255, -469816708602, -108058927347, -291747327730, 907644130242]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-919249, -472526, 125838, 60196, -789686]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-919249, -472526, 125838, 60196, -789686]] 
 ![![19, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![-919249, -472526, 125838, 60196, -789686], ![-4058592, -2059881, 540576, 260506, -3421896], ![-17617212, -9030244, 2355441, 1132224, -14914956], ![-77079312, -39565596, 10457648, 5011977, -65845152], ![-11932120, -6123938, 1609608, 772262, -10157923]]]
  hmulB := by decide  
  f := ![![![-32791883, -6885354, 14610122, 5350236, -51264434]], ![![-15663757, -905991, 1249926, 814974, -5595142]], ![![18940975, 422118, 107567, -493564, 1426726]], ![![45161261, -27855254, 69643786, 19905933, -225418978]], ![![-13364506, -7644718, 17586948, 5714958, -59254007]]]
  g := ![![![703141, -472526, 125838, 60196, -789686], ![3049573, -2059881, 540576, 260506, -3421896], ![13312001, -9030244, 2355441, 1132224, -14914956], ![58677907, -39565596, 10457648, 5011977, -65845152], ![9058442, -6123938, 1609608, 772262, -10157923]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-32791883, -6885354, 14610122, 5350236, -51264434]] ![![-919249, -472526, 125838, 60196, -789686]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5549, 5807, -14291, -4188, 46606]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-5549, 5807, -14291, -4188, 46606]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![13, 19, 22, 1, 0], ![14, 9, 16, 0, 1]] where
  M :=![![![-5549, 5807, -14291, -4188, 46606], ![182352, 7131, -6335, -6991, 38040], ![-172710, -114554, 265176, 85369, -890718], ![-3005406, 43280, -282203, -2244, 647970], ![-359272, -25982, 41171, 22491, -169559]]]
  hmulB := by decide  
  f := ![![![6141115, 3141255, -825507, -396566, 5213744]], ![![26873988, 13746391, -3612503, -1735411, 22815828]], ![![117602946, 60155266, -15808580, -7594295, 99843834]], ![![160536719, 82116428, -21579885, -10366775, 136294246]], ![![99529470, 50910491, -13379086, -6427188, 84499633]]]
  g := ![![![-26243, -14525, -29037, -4188, 46606], ![-11275, -8800, -20051, -6991, 38040], ![486415, 273039, 549502, 85369, -890718], ![-523818, -249818, -460885, -2244, 647970], ![74877, 46640, 98231, 22491, -169559]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [10, 1, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 20, 15], [3, 2, 8], [0, 1]]
 g := ![![[5, 8, 1], [4, 15, 12], [0, 22, 1], []], ![[11, 10, 16, 21], [15, 5, 17, 11], [8, 19, 15, 14], [7, 18]], ![[5, 21, 10, 18], [5, 4, 4, 6], [18, 7, 11, 3], [14, 18]]]
 h' := ![![[19, 20, 15], [6, 7, 22], [0, 10, 14], [0, 0, 1], [0, 1]], ![[3, 2, 8], [9, 4, 11], [9, 11, 17], [15, 21, 2], [19, 20, 15]], ![[0, 1], [20, 12, 13], [13, 2, 15], [7, 2, 20], [3, 2, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 6], []]
 b := ![[], [3, 6, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [10, 1, 1, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5043867, -29608, 58620, 171864, -816648]
  a := ![23, 21, -19, -8, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![180651, 176296, 406260, 171864, -816648]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1703, 871, -229, -110, 1446]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![1703, 871, -229, -110, 1446]] 
 ![![23, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![1703, 871, -229, -110, 1446], ![7452, 3811, -1001, -481, 6324], ![32598, 16678, -4382, -2105, 27678], ![142686, 72992, -19193, -9218, 121182], ![22092, 11302, -2971, -1427, 18761]]]
  hmulB := by decide  
  f := ![![![-281, 55, -73, -20, 240]], ![![-63, 18, -34, -11, 120]], ![![-107, 9, 17, 9, -78]], ![![-838, 120, -111, -22, 330]], ![![-315, 53, -56, -13, 173]]]
  g := ![![![-1401, 871, -229, -110, 1446], ![-6128, 3811, -1001, -481, 6324], ![-26820, 16678, -4382, -2105, 27678], ![-117411, 72992, -19193, -9218, 121182], ![-18178, 11302, -2971, -1427, 18761]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![569, 304, -106, -48, 598]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![569, 304, -106, -48, 598]] 
 ![![23, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![569, 304, -106, -48, 598], ![2856, 1225, -282, -150, 1968], ![10116, 5700, -1301, -618, 8532], ![46764, 25224, -7674, -3533, 45324], ![7016, 3898, -1066, -494, 6515]]]
  hmulB := by decide  
  f := ![![![16583, 2516, -5066, -2000, 18266]], ![![12519, 1237, -2232, -1026, 8538]], ![![-11839, -808, 1241, 706, -5206]], ![![4805, 11108, -26420, -8161, 87578]], ![![10974, 3010, -6586, -2306, 22751]]]
  g := ![![![-687, 304, -106, -48, 598], ![-2385, 1225, -282, -150, 1968], ![-10699, 5700, -1301, -618, 8532], ![-53491, 25224, -7674, -3533, 45324], ![-7872, 3898, -1066, -494, 6515]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-5549, 5807, -14291, -4188, 46606]] ![![1703, 871, -229, -110, 1446]]
  ![![16583, 2516, -5066, -2000, 18266]] where
 M := ![![![16583, 2516, -5066, -2000, 18266]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![16583, 2516, -5066, -2000, 18266]] ![![569, 304, -106, -48, 598]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)


lemma PB1981I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1981I0 : PrimesBelowBoundCertificateInterval O 1 23 1981 where
  m := 9
  g := ![5, 4, 5, 1, 2, 2, 1, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1981I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1, I23N2]
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
    · exact ![9, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![16807]
    · exact ![1331, 121]
    · exact ![28561, 13]
    · exact ![1419857]
    · exact ![130321, 19]
    · exact ![12167, 23, 23]
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
      exact NI3N1
      exact NI3N1
      exact NI3N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
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
      exact NI23N1
      exact NI23N2
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I11N0, I11N1, I13N1, I19N1, I23N1, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [I11N0, I11N1], [I13N1], [], [I19N1], [I23N1, I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
