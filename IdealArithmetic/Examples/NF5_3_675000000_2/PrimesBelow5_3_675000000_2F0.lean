
import IdealArithmetic.Examples.NF5_3_675000000_2.RI5_3_675000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![534801, 164414, 70921, -152675, -267248]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![534801, 164414, 70921, -152675, -267248]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![534801, 164414, 70921, -152675, -267248], ![1527284, 469483, 202516, -435986, -763108], ![4360920, 1340770, 578347, -1245000, -2179400], ![481878, 148084, 63879, -137540, -240686], ![375264, 115426, 49788, -107158, -187641]]]
  hmulB := by decide  
  f := ![![![9908, -1298, -1077, 1349, 1946]], ![![-5086, 3909, -1025, -741, 4202]], ![![-36580, -6750, 9593, -4810, -25700]], ![![26133, -4516, -2309, 3574, 3380]], ![![-15022, 1524, 1849, -2039, -3663]]]
  g := ![![![343738, 164414, 70921, -152675, -267248], ![981635, 469483, 202516, -435986, -763108], ![2802960, 1340770, 578347, -1245000, -2179400], ![309709, 148084, 63879, -137540, -240686], ![241211, 115426, 49788, -107158, -187641]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4908404, -1508960, -650900, 1401235, 2452737]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-4908404, -1508960, -650900, 1401235, 2452737]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-4908404, -1508960, -650900, 1401235, 2452737], ![-14016956, -4308932, -1858693, 4001414, 7003872], ![-40025320, -12305135, -5307888, 11426470, 20001480], ![-4422118, -1359215, -586313, 1262289, 2209236], ![-3444694, -1059233, -456899, 983494, 1721810]]]
  hmulB := by decide  
  f := ![![![148530, -20273, -15749, 20236, 27867]], ![![-70996, 58944, -16439, -10406, 65682]], ![![-567080, -97915, 145438, -74650, -387600]], ![![315718, -59686, -25402, 43261, 32619]], ![![-225917, 24092, 27236, -30679, -53203]]]
  g := ![![![-2454202, -1508960, -650900, 1401235, 2452737], ![-7008478, -4308932, -1858693, 4001414, 7003872], ![-20012660, -12305135, -5307888, 11426470, 20001480], ![-2211059, -1359215, -586313, 1262289, 2209236], ![-1722347, -1059233, -456899, 983494, 1721810]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1075, 41, -176, 1244, 1814]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-1075, 41, -176, 1244, 1814]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-1075, 41, -176, 1244, 1814], ![-9536, 1103, -633, 6844, 7672], ![-34000, 1815, -4913, 36390, 51440], ![-21828, 2375, -1636, 16509, 19256], ![-4572, -115, -1111, 6926, 11001]]]
  hmulB := by decide  
  f := ![![![658, 929, -565, 74, 1756]], ![![-6547, 296, 986, -884, -2190]], ![![21189, -4058, -1677, 2902, 2098]], ![![3937, 2346, -1820, 493, 5362]], ![![-100, -1450, 723, 8, -2367]]]
  g := ![![![-1092, 41, -176, 1244, 1814], ![-8425, 1103, -633, 6844, 7672], ![-33646, 1815, -4913, 36390, 51440], ![-19538, 2375, -1636, 16509, 19256], ![-5136, -115, -1111, 6926, 11001]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![534801, 164414, 70921, -152675, -267248]] ![![-4908404, -1508960, -650900, 1401235, 2452737]]
  ![![-6172504443346, -1897538491234, -818517165423, 1762090261914, 3084340389245]] where
 M := ![![![-6172504443346, -1897538491234, -818517165423, 1762090261914, 3084340389245]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-6172504443346, -1897538491234, -818517165423, 1762090261914, 3084340389245]] ![![-4908404, -1508960, -650900, 1401235, 2452737]]
  ![![71239490613594623966, 21900296212420042758, 9446853625964630849, -20337030761824200820, -35597680084924250936]] where
 M := ![![![71239490613594623966, 21900296212420042758, 9446853625964630849, -20337030761824200820, -35597680084924250936]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![71239490613594623966, 21900296212420042758, 9446853625964630849, -20337030761824200820, -35597680084924250936]] ![![-1075, 41, -176, 1244, 1814]]
  ![![52600443323133408614, 16170319016303645755, 6975185876463086449, -15016065173691875550, -26283929570668750596]] where
 M := ![![![52600443323133408614, 16170319016303645755, 6975185876463086449, -15016065173691875550, -26283929570668750596]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![52600443323133408614, 16170319016303645755, 6975185876463086449, -15016065173691875550, -26283929570668750596]] ![![-1075, 41, -176, 1244, 1814]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![38838096858867784582, 11939530120594813164, 5150203918058909040, -11087272879112340700, -19407025030940502680]]]
 hmul := by decide  
 g := ![![![![19419048429433892291, 5969765060297406582, 2575101959029454520, -5543636439556170350, -9703512515470251340]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 0, 0, 2, 2]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-3, 0, 0, 2, 2]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-3, 0, 0, 2, 2], ![-8, 1, -2, 12, 16], ![-80, 10, -7, 60, 80], ![-36, 2, -2, 27, 32], ![-12, 2, -2, 12, 17]]]
  hmulB := by decide  
  f := ![![![15, 0, 0, -2, 2]], ![![-3, 5, 2, -2, -10]], ![![90, -10, -3, -8, 28]], ![![-10, 6, 2, -1, -12]], ![![33, -6, -2, -2, 15]]]
  g := ![![![-3, 0, 0, 2, 2], ![-15, 1, -2, 12, 16], ![-92, 10, -7, 60, 80], ![-40, 2, -2, 27, 32], ![-17, 2, -2, 12, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3485, 1127, 615, -1160, -2206]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3485, 1127, 615, -1160, -2206]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![3485, 1127, 615, -1160, -2206], ![13008, 3194, 1241, -2902, -5096], ![29160, 11215, 3902, -9390, -14440], ![1292, 887, 935, -1291, -2944], ![3716, 1076, 74, -648, -575]]]
  hmulB := by decide  
  f := ![![![-701905, 62377, -70157, 610072, 778338]], ![![-1496107, 132699, -149862, 1301822, 1661950]], ![![-7294110, 648033, -729290, 6340818, 8090452]], ![![-3520474, 312321, -352553, 3062917, 3909940]], ![![-1780250, 158308, -177814, 1546764, 1972965]]]
  g := ![![![2620, 1127, 615, -1160, -2206], ![7776, 3194, 1241, -2902, -5096], ![19267, 11215, 3902, -9390, -14440], ![2335, 887, 935, -1291, -2944], ![1646, 1076, 74, -648, -575]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1143, -93, 125, -1042, -1365]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![1143, -93, 125, -1042, -1365]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![1143, -93, 125, -1042, -1365], ![6752, -639, 626, -5648, -7044], ![33760, -2810, 3613, -30420, -39600], ![16136, -1500, 1530, -13651, -17142], ![6182, -468, 720, -5834, -7781]]]
  hmulB := by decide  
  f := ![![![731, 193, 99, -196, -375]], ![![1226, 347, 136, -312, -534]], ![![2034, 752, 363, -724, -1290]], ![![469, 95, 75, -123, -279]], ![![367, 137, 51, -118, -188]]]
  g := ![![![1162, -93, 125, -1042, -1365], ![6490, -639, 626, -5648, -7044], ![34058, -2810, 3613, -30420, -39600], ![15623, -1500, 1530, -13651, -17142], ![6431, -468, 720, -5834, -7781]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-3, 0, 0, 2, 2]] ![![3485, 1127, 615, -1160, -2206]]
  ![![-439, 545, 173, -398, -420]] where
 M := ![![![-439, 545, 173, -398, -420]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-439, 545, 173, -398, -420]] ![![3485, 1127, 615, -1160, -2206]]
  ![![8529189, 2381226, 678196, -1910842, -2893794]] where
 M := ![![![8529189, 2381226, 678196, -1910842, -2893794]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![8529189, 2381226, 678196, -1910842, -2893794]] ![![3485, 1127, 615, -1160, -2206]]
  ![![67253260465, 20015360789, 8846095467, -18830361998, -33453818472]] where
 M := ![![![67253260465, 20015360789, 8846095467, -18830361998, -33453818472]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![67253260465, 20015360789, 8846095467, -18830361998, -33453818472]] ![![1143, -93, 125, -1042, -1365]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![148731111, 33012210, 13177530, -30646596, -55525293]]]
 hmul := by decide  
 g := ![![![![49577037, 11004070, 4392510, -10215532, -18508431]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1, I3N1, I3N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-40375, -12412, -5354, 11526, 20175]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-40375, -12412, -5354, 11526, 20175]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-40375, -12412, -5354, 11526, 20175], ![-115296, -35444, -15289, 32914, 57612], ![-329240, -101215, -43660, 93990, 164520], ![-36372, -11181, -4823, 10383, 18174], ![-28338, -8712, -3758, 8090, 14161]]]
  hmulB := by decide  
  f := ![![![35, 0, 4, -40, -45]], ![![40, -6, 7, -42, -60]], ![![312, -27, 18, -218, -264]], ![![104, -5, 11, -101, -126]], ![![76, -8, 6, -58, -71]]]
  g := ![![![-16145, -12412, -5354, 11526, 20175], ![-46104, -35444, -15289, 32914, 57612], ![-131656, -101215, -43660, 93990, 164520], ![-14544, -11181, -4823, 10383, 18174], ![-11332, -8712, -3758, 8090, 14161]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-40375, -12412, -5354, 11526, 20175]] ![![-40375, -12412, -5354, 11526, 20175]]
  ![![3833002715, 1178333732, 508282910, -1094223070, -1915314150]] where
 M := ![![![3833002715, 1178333732, 508282910, -1094223070, -1915314150]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![3833002715, 1178333732, 508282910, -1094223070, -1915314150]] ![![-40375, -12412, -5354, 11526, 20175]]
  ![![-363886461986457, -111865220210768, -48253884372948, 103880166849728, 181830523343979]] where
 M := ![![![-363886461986457, -111865220210768, -48253884372948, 103880166849728, 181830523343979]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-363886461986457, -111865220210768, -48253884372948, 103880166849728, 181830523343979]] ![![-40375, -12412, -5354, 11526, 20175]]
  ![![34545594423893324505, 10619934873214743280, 4580986909557921184, -9861873104832987920, -17262097300995897660]] where
 M := ![![![34545594423893324505, 10619934873214743280, 4580986909557921184, -9861873104832987920, -17262097300995897660]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![34545594423893324505, 10619934873214743280, 4580986909557921184, -9861873104832987920, -17262097300995897660]] ![![-40375, -12412, -5354, 11526, 20175]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-3279589154225102804205095, -1008204484815078398863500, -434896409651651824156690, 936237821763595805003950, 1638778780091527175706075]]]
 hmul := by decide  
 g := ![![![![-655917830845020560841019, -201640896963015679772700, -86979281930330364831338, 187247564352719161000790, 327755756018305435141215]]]]
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


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [6, 4, 3, 5, 5, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 6, 3, 2, 6], [6, 3, 4, 1], [6, 6, 0, 4], [5, 5, 0, 0, 1], [0, 1]]
 g := ![![[6, 2, 1], []], ![[1, 1, 6, 0, 1, 5], [4, 6, 1, 2, 0, 3, 4, 6]], ![[6, 2, 6, 0, 4], [1, 3, 3, 0, 1]], ![[2, 5, 6, 6, 6, 1, 2], [6, 2, 0, 2, 1]], ![[4, 3, 5, 3, 1, 6, 2, 4], [4, 0, 2, 3, 0, 6, 2, 1]]]
 h' := ![![[6, 6, 3, 2, 6], [0, 0, 0, 1], [0, 1]], ![[6, 3, 4, 1], [3, 1, 6, 4], [6, 6, 3, 2, 6]], ![[6, 6, 0, 4], [0, 1, 1, 2], [6, 3, 4, 1]], ![[5, 5, 0, 0, 1], [5, 3, 6, 5, 5], [6, 6, 0, 4]], ![[0, 1], [3, 2, 1, 2, 2], [5, 5, 0, 0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 1, 6, 2], [], [], []]
 b := ![[], [1, 3, 3, 6, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [6, 4, 3, 5, 5, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4802005129404, -383730134466, 533565831246, -4416171776184, -5811942414516]
  a := ![-25, -8, 9, -28, -75]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![686000732772, -54818590638, 76223690178, -630881682312, -830277487788]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![65327, 19792, 8546, -18512, -32067]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![65327, 19792, 8546, -18512, -32067]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![1, 4, 6, 5, 1]] where
  M :=![![![65327, 19792, 8546, -18512, -32067], ![182488, 57478, 24749, -52722, -93876], ![540120, 159635, 69046, -151150, -257160], ![54024, 18965, 8103, -16485, -31578], ![50586, 12770, 5592, -13138, -19781]]]
  hmulB := by decide  
  f := ![![![1723, 1428, -992, 210, 2991]], ![![-23088, -36, 3999, -3098, -9444]], ![![63160, -15635, -3284, 8710, 600]], ![![14548, 5623, -5245, 1869, 14934]], ![![32615, -6267, -2575, 4471, 3208]]]
  g := ![![![8854, 13460, 18268, 12893, -32067], ![25124, 39362, 53455, 37878, -93876], ![72480, 108025, 146546, 103150, -257160], ![7782, 13207, 17961, 12855, -31578], ![6397, 8354, 11298, 7797, -19781]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 4 2 3 [7, 3, 1, 9, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 0, 0, 9], [7, 10, 9, 6], [9, 0, 2, 7], [0, 1]]
 g := ![![[2, 2, 10, 9], [2, 1], []], ![[10, 10, 9, 0, 4, 4], [3, 8, 1, 7, 3, 5], [1, 8, 4]], ![[5, 1, 1, 4, 10, 6], [5, 0, 7, 10, 7, 10], [8, 4, 3]], ![[0, 3, 1, 2, 4, 2], [8, 8, 4, 7, 3, 8], [9, 5, 5]]]
 h' := ![![[8, 0, 0, 9], [8, 9, 6, 3], [0, 0, 1], [0, 1]], ![[7, 10, 9, 6], [0, 5, 4, 3], [2, 7, 2, 5], [8, 0, 0, 9]], ![[9, 0, 2, 7], [0, 2, 0, 1], [4, 0, 9, 3], [7, 10, 9, 6]], ![[0, 1], [0, 6, 1, 4], [7, 4, 10, 3], [9, 0, 2, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 7], []]
 b := ![[], [], [9, 7, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 4
  hpos := by decide
  P := [7, 3, 1, 9, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13126503125459, 625457377872, -1990416304568, 14472632028920, 20738877561360]
  a := ![-169, -58, 56, -170, -510]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3078670971529, -7484550260688, -11493061970248, -8111068707080, 20738877561360]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 14641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1723, -1428, 992, -210, -2991]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-1723, -1428, 992, -210, -2991]] 
 ![![11, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-1723, -1428, 992, -210, -2991], ![23088, 36, -3999, 3098, 9444], ![-63160, 15635, 3284, -8710, -600], ![-14548, -5623, 5245, -1869, -14934], ![2306, 4526, -2600, 242, 8197]]]
  hmulB := by decide  
  f := ![![![-65327, -19792, -8546, 18512, 32067]], ![![-75978, -23218, -10019, 21622, 37686]], ![![-108490, -32505, -14046, 30570, 52530]], ![![-46483, -14319, -6175, 13279, 23277]], ![![-28354, -8358, -3616, 7926, 13459]]]
  g := ![![![1461, -1428, 992, -210, -2991], ![296, 36, -3999, 3098, 9444], ![-17180, 15635, 3284, -8710, -600], ![5641, -5623, 5245, -1869, -14934], ![-4676, 4526, -2600, 242, 8197]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![65327, 19792, 8546, -18512, -32067]] ![![-1723, -1428, 992, -210, -2991]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![-11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [9, 4, 8, 0, 9, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 7, 4, 10, 3], [4, 6, 2, 6], [11, 8, 10, 10, 9], [3, 4, 10, 0, 1], [0, 1]]
 g := ![![[3, 9, 8, 1, 9], [4, 1], []], ![[10, 1, 10, 10, 9, 7, 10, 1], [6, 7, 5, 12], [6, 3, 9, 10, 8, 11, 1, 1]], ![[3, 6, 6, 2, 0, 7, 11], [3, 1], [2, 12, 9, 1, 8]], ![[12, 11, 9, 1, 12, 2, 8, 1], [0, 3, 8, 4], [6, 8, 10, 10, 5, 7, 3, 1]], ![[3, 10, 4, 12, 8, 10, 4, 3], [8, 2, 5, 9], [8, 4, 8, 11, 6, 7, 4, 1]]]
 h' := ![![[12, 7, 4, 10, 3], [3, 1, 3, 5, 3], [0, 0, 0, 1], [0, 1]], ![[4, 6, 2, 6], [7, 2, 4, 4, 3], [10, 9, 10, 3, 8], [12, 7, 4, 10, 3]], ![[11, 8, 10, 10, 9], [9, 8, 0, 3, 2], [7, 3, 6, 1], [4, 6, 2, 6]], ![[3, 4, 10, 0, 1], [9, 12, 3, 0, 9], [3, 0, 8, 11, 2], [11, 8, 10, 10, 9]], ![[0, 1], [3, 3, 3, 1, 9], [7, 1, 2, 10, 3], [3, 4, 10, 0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 4, 8, 7], [], [], []]
 b := ![[], [11, 12, 11, 0, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 5
  hpos := by decide
  P := [9, 4, 8, 0, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![319358727701, -25675339560, 35288071624, -292817675124, -384738012672]
  a := ![-14, -5, 5, -16, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![24566055977, -1975026120, 2714467048, -22524436548, -29595231744]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 371293 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-766731, -234912, -101400, 218784, 382054]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-766731, -234912, -101400, 218784, 382054]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![12, 10, 3, 10, 1]] where
  M :=![![![-766731, -234912, -101400, 218784, 382054], ![-2181296, -672893, -290426, 625244, 1097192], ![-6276560, -1910990, -826189, 1791100, 3114160], ![-684240, -213778, -92690, 200461, 355060], ![-550548, -162208, -70436, 155420, 263997]]]
  hmulB := by decide  
  f := ![![![260053, -27024, -31696, 35304, 62378]], ![![-357808, 199255, -35254, -50988, 174136]], ![![-1597040, -410930, 475367, -208220, -1308400]], ![![1142336, -173310, -112662, 155893, 186428]], ![![317568, -72892, -19295, 43706, 12189]]]
  g := ![![![-314787, -238556, -73386, -211868, 382054], ![-902800, -684989, -210706, -608628, 1097192], ![-2567440, -1944270, -598157, -1726500, 3114160], ![-290880, -221434, -68110, -197067, 355060], ![-218736, -164834, -50731, -146150, 263997]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [2, 16, 3, 6, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 1, 10, 6], [14, 16], [12, 16, 7, 11], [0, 1]]
 g := ![![[16, 7, 13, 1], [0, 7, 2], [1], []], ![[12, 11, 5, 14], [13, 5, 8], [5, 5, 1], [2, 6, 2]], ![[0, 10, 4, 16], [14, 5, 2], [1], []], ![[3, 15, 15, 3], [2, 9, 8], [16, 1, 1], [2, 6, 2]]]
 h' := ![![[2, 1, 10, 6], [4, 16, 16, 16], [15, 1, 14, 11], [0, 0, 1], [0, 1]], ![[14, 16], [6, 1, 5], [7, 12, 7, 5], [0, 11, 3, 16], [2, 1, 10, 6]], ![[12, 16, 7, 11], [8, 5, 8, 1], [11, 7, 0, 6], [9, 6, 1], [14, 16]], ![[0, 1], [14, 12, 5], [1, 14, 13, 12], [4, 0, 12, 1], [12, 16, 7, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [14], []]
 b := ![[], [], [9, 12, 6, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [2, 16, 3, 6, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-861315704984, 35650509700, -137567661124, 980663202408, 1423400196348]
  a := ![90, 27, -31, 89, 269]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1055418709480, -835197144340, -259280485304, -779608162416, 1423400196348]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![260053, -27024, -31696, 35304, 62378]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![260053, -27024, -31696, 35304, 62378]] 
 ![![17, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![260053, -27024, -31696, 35304, 62378], ![-357808, 199255, -35254, -50988, 174136], ![-1597040, -410930, 475367, -208220, -1308400], ![1142336, -173310, -112662, 155893, 186428], ![-776140, 58464, 105396, -105036, -221763]]]
  hmulB := by decide  
  f := ![![![-766731, -234912, -101400, 218784, 382054]], ![![-263617, -81037, -34978, 75388, 131962]], ![![-730024, -222958, -96317, 208316, 362976]], ![![-401064, -123122, -53170, 114749, 200676]], ![![-77487, -23360, -10108, 22012, 38003]]]
  g := ![![![14699, -27024, -31696, 35304, 62378], ![-25869, 199255, -35254, -50988, 174136], ![-70178, -410930, 475367, -208220, -1308400], ![66470, -173310, -112662, 155893, 186428], ![-43097, 58464, 105396, -105036, -221763]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-766731, -234912, -101400, 218784, 382054]] ![![260053, -27024, -31696, 35304, 62378]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [8, 17, 11, 8, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 10, 1, 13, 8], [6, 9, 11, 9, 11], [11, 2, 4, 7], [11, 16, 3, 9], [0, 1]]
 g := ![![[6, 4, 4, 12, 7], [8, 4, 12, 18, 1], [], []], ![[3, 7, 4, 4, 10, 14, 6, 12], [8, 16, 9, 17, 11, 17, 14, 10], [0, 18, 4, 4], [17, 4, 11, 7]], ![[3, 18, 10, 11, 4, 9], [17, 16, 14, 16, 11, 18, 1, 11], [12, 18, 0, 11], [7, 0, 1, 7]], ![[9, 16, 18, 0, 8, 9, 16], [1, 16, 11, 14, 12, 16, 4], [7, 2, 13, 17], [7, 11]], ![[8, 7, 15, 8, 8, 14, 6], [14, 13, 5, 8, 0, 9, 17], [5, 7, 1, 1], [11, 5]]]
 h' := ![![[9, 10, 1, 13, 8], [12, 3, 14, 0, 8], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[6, 9, 11, 9, 11], [4, 11, 1, 4, 12], [4, 14, 4, 4, 14], [2, 11, 3, 2, 2], [9, 10, 1, 13, 8]], ![[11, 2, 4, 7], [16, 1, 15, 5], [0, 16, 16, 1, 1], [18, 8, 14, 6, 12], [6, 9, 11, 9, 11]], ![[11, 16, 3, 9], [12, 5, 11, 17, 10], [8, 12, 4, 7, 5], [8, 8, 18, 12, 6], [11, 2, 4, 7]], ![[0, 1], [7, 18, 16, 12, 8], [4, 15, 14, 7, 17], [14, 11, 2, 18, 18], [11, 16, 3, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 4, 0, 2], [], [], []]
 b := ![[], [14, 8, 7, 15, 14], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [8, 17, 11, 8, 1, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7248802487410, 53298158085, 1594717311957, -10235289334502, -15935901154984]
  a := ![-37, -7, 14, -32, -110]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![381515920390, 2805166215, 83932490103, -538699438658, -838731639736]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 2476099 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2231, 175, -237, 2050, 2589]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-2231, 175, -237, 2050, 2589]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 17, 3, 2, 1]] where
  M :=![![![-2231, 175, -237, 2050, 2589], ![-12512, 1223, -1336, 11008, 14244], ![-69920, 6060, -6549, 59160, 75120], ![-30176, 2550, -3046, 26635, 33822], ![-13478, 1254, -1294, 11358, 14557]]]
  hmulB := by decide  
  f := ![![![-16287, -4995, -2155, 4644, 8115]], ![![-46344, -14303, -6168, 13256, 23268]], ![![-133120, -40660, -17547, 37880, 66000]], ![![-14476, -4546, -1958, 4177, 7422]], ![![-53382, -16421, -7083, 15244, 26695]]]
  g := ![![![-97, -1906, -348, -136, 2589], ![-544, -10475, -1916, -760, 14244], ![-3040, -55260, -10083, -3960, 75120], ![-1312, -24888, -4544, -1783, 33822], ![-586, -10705, -1955, -772, 14557]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [9, 15, 8, 18, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 20, 18, 14], [5, 18, 6, 8], [22, 7, 22, 1], [0, 1]]
 g := ![![[5, 17, 13, 3], [17, 10, 12, 13], [5, 1], []], ![[5, 3, 11, 9, 5, 17], [21, 11, 12, 2, 22, 7], [1, 15, 16, 7, 6, 11], [20, 12, 12]], ![[12, 6, 7, 6, 6, 6], [6, 16, 2, 8, 8, 6], [9, 9, 13, 0, 22, 12], [6, 2, 18]], ![[5, 9, 17, 5, 20, 16], [5, 15, 1, 10, 8, 2], [15, 2, 8, 7, 0, 12], [22, 3, 1]]]
 h' := ![![[1, 20, 18, 14], [8, 1, 13, 7], [1, 8, 14, 17], [0, 0, 1], [0, 1]], ![[5, 18, 6, 8], [21, 13, 0, 4], [16, 5, 22, 9], [5, 0, 11, 20], [1, 20, 18, 14]], ![[22, 7, 22, 1], [7, 3, 4, 8], [7, 22, 10, 15], [17, 3, 6, 17], [5, 18, 6, 8]], ![[0, 1], [22, 6, 6, 4], [18, 11, 0, 5], [10, 20, 5, 9], [22, 7, 22, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 17, 21], []]
 b := ![[], [], [6, 20, 18, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [9, 15, 8, 18, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13693714861, -3406375918, -1307737510, 242915702, 9230629356]
  a := ![28, -2, -10, 10, 84]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![595378907, -6970742390, -1260853286, -792101870, 9230629356]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16287, 4995, 2155, -4644, -8115]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![16287, 4995, 2155, -4644, -8115]] 
 ![![23, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![16287, 4995, 2155, -4644, -8115], ![46344, 14303, 6168, -13256, -23268], ![133120, 40660, 17547, -37880, -66000], ![14476, 4546, 1958, -4177, -7422], ![11626, 3460, 1496, -3266, -5585]]]
  hmulB := by decide  
  f := ![![![2231, -175, 237, -2050, -2589]], ![![835, -76, 89, -746, -957]], ![![4398, -370, 429, -3820, -4842]], ![![2767, -225, 287, -2495, -3159]], ![![1459, -123, 149, -1296, -1646]]]
  g := ![![![4949, 4995, 2155, -4644, -8115], ![14145, 14303, 6168, -13256, -23268], ![40334, 40660, 17547, -37880, -66000], ![4473, 4546, 1958, -4177, -7422], ![3459, 3460, 1496, -3266, -5585]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-2231, 175, -237, 2050, 2589]] ![![16287, 4995, 2155, -4644, -8115]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![-23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB1271I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1271I0 : PrimesBelowBoundCertificateInterval O 1 23 1271 where
  m := 9
  g := ![5, 5, 5, 1, 2, 1, 2, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1271I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1, I3N2]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
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
    · exact ![16807]
    · exact ![14641, 11]
    · exact ![371293]
    · exact ![83521, 17]
    · exact ![2476099]
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
      exact NI3N1
      exact NI3N1
      exact NI3N1
      exact NI3N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I3N2, I5N0, I11N1, I17N1, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1, I3N1, I3N2], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [I11N1], [], [I17N1], [], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
