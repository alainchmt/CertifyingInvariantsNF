
import IdealArithmetic.Examples.NF5_3_12000000000_4.RI5_3_12000000000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6681361, -2664735, 10859050, 3193804, -44485427]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-6681361, -2664735, 10859050, 3193804, -44485427]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-6681361, -2664735, 10859050, 3193804, -44485427], ![18707166, 7460829, -30404121, -8942302, 124554158], ![-52377672, -20890462, 85128740, 25037563, -348740456], ![31425618, 12531558, -51073327, -15021512, 209227634], ![-19947468, -7955926, 32420377, 9535289, -132814106]]]
  hmulB := by decide  
  f := ![![![388, -2218, 1387, 431, -5173]], ![![432, 3639, -4602, -721, 14216]], ![![-12570, 22280, -4642, -4433, 30310]], ![![8112, -66178, 57151, 13090, -194224]], ![![-2347, -473, 3835, 84, -9595]]]
  g := ![![![18902033, -2664735, 10859050, 3193804, -44485427], ![-52923496, 7460829, -30404121, -8942302, 124554158], ![148181392, -20890462, 85128740, 25037563, -348740456], ![-88901008, 12531558, -51073327, -15021512, 209227634], ![56433319, -7955926, 32420377, 9535289, -132814106]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6230, -1319, 8965, 2700, -36429]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-6230, -1319, 8965, 2700, -36429]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-6230, -1319, 8965, 2700, -36429], ![13458, 12796, -29268, -8205, 121794], ![-63078, 22182, 55393, 18861, -214854], ![-16104, 109916, -89641, -20051, 396888], ![-24492, 9520, 20605, 7107, -79493]]]
  hmulB := by decide  
  f := ![![![561242, -53744, 151783, 33021, -584916]], ![![221685, -21203, 59928, 13038, -230955]], ![![175074, -16701, 47371, 10290, -182478]], ![![104550, -10325, 28507, 6211, -109770]], ![![-5184, 488, -1378, -303, 5335]]]
  g := ![![![-3115, -1319, 8965, 2700, -36429], ![6729, 12796, -29268, -8205, 121794], ![-31539, 22182, 55393, 18861, -214854], ![-8052, 109916, -89641, -20051, 396888], ![-12246, 9520, 20605, 7107, -79493]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-6681361, -2664735, 10859050, 3193804, -44485427]] ![![-6230, -1319, 8965, 2700, -36429]]
  ![![358899777968, 143139108623, -583309588434, -171559875668, 2389598767042]] where
 M := ![![![358899777968, 143139108623, -583309588434, -171559875668, 2389598767042]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![358899777968, 143139108623, -583309588434, -171559875668, 2389598767042]] ![![-6230, -1319, 8965, 2700, -36429]]
  ![![-19278830038287646, -7688949095526920, 31333354455836192, 9215596371194773, -128360907825158864]] where
 M := ![![![-19278830038287646, -7688949095526920, 31333354455836192, 9215596371194773, -128360907825158864]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-19278830038287646, -7688949095526920, 31333354455836192, 9215596371194773, -128360907825158864]] ![![-6230, -1319, 8965, 2700, -36429]]
  ![![1035591292337765698940, 413023100974229631486, -1683117825840901707587, -495029510135282288159, 6895097353386050408062]] where
 M := ![![![1035591292337765698940, 413023100974229631486, -1683117825840901707587, -495029510135282288159, 6895097353386050408062]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![1035591292337765698940, 413023100974229631486, -1683117825840901707587, -495029510135282288159, 6895097353386050408062]] ![![-6230, -1319, 8965, 2700, -36429]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-55628331787873260638426794, -22186157759124640370636242, 90411191374245656599276590, 26591250230870371563969706, -370380468406585269298503836]]]
 hmul := by decide  
 g := ![![![![-27814165893936630319213397, -11093078879562320185318121, 45205595687122828299638295, 13295625115435185781984853, -185190234203292634649251918]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N1, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8949, 20441, -9357, -1449, 44454]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-8949, 20441, -9357, -1449, 44454]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-8949, 20441, -9357, -1449, 44454], ![-57030, 130263, -59629, -9234, 283290], ![-363432, 830118, -379994, -58845, 1805304], ![-893150, 2040050, -933851, -144614, 4436610], ![-148078, 338226, -154826, -23976, 735559]]]
  hmulB := by decide  
  f := ![![![15, 13, -17, -6, 72]], ![![-4, -27, 36, 9, -132]], ![![66, -4, -84, -9, 258]], ![![-79, 277, -168, -50, 612]], ![![24, 30, -52, -12, 187]]]
  g := ![![![-32136, 20441, -9357, -1449, 44454], ![-204792, 130263, -59629, -9234, 283290], ![-1305065, 830118, -379994, -58845, 1805304], ![-3207252, 2040050, -933851, -144614, 4436610], ![-531740, 338226, -154826, -23976, 735559]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-160763, 367502, -168390, -26102, 799880]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-160763, 367502, -168390, -26102, 799880]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-160763, 367502, -168390, -26102, 799880], ![-1025516, 2341541, -1071406, -165844, 5090452], ![-6532336, 14922924, -6832377, -1058246, 32458832], ![-16056196, 36672644, -16786466, -2599393, 79750972], ![-2661580, 6080236, -2783768, -431164, 13224977]]]
  hmulB := by decide  
  f := ![![![2071, -7562, 4798, 1498, -18024]], ![![1721, 6063, -8948, -1194, 26724]], ![![-26830, 43368, -5305, -8630, 49992]], ![![19868, -151692, 129242, 30011, -440996]], ![![-4935, -1730, 9194, 330, -23591]]]
  g := ![![![-330455, 367502, -168390, -26102, 799880], ![-2104899, 2341541, -1071406, -165844, 5090452], ![-13416446, 14922924, -6832377, -1058246, 32458832], ![-32968960, 36672644, -16786466, -2599393, 79750972], ![-5466419, 6080236, -2783768, -431164, 13224977]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16349, -40786, 18269, 8095, -78944]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![16349, -40786, 18269, 8095, -78944]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![16349, -40786, 18269, 8095, -78944], ![-20202, 255045, -237074, -50428, 789014], ![-468612, 276218, 412171, -55658, -753956], ![754592, -3204678, 2229060, 634803, -8111104], ![-61460, -171804, 272104, 33794, -801783]]]
  hmulB := by decide  
  f := ![![![529791, 13178, 120639, 28159, -437504]], ![![261767, 131979, 15165, 8003, 8882]], ![![74194, 900522, -301423, -38388, 1550664]], ![![-725447, 2216592, -956719, -143820, 4607300]], ![![12105, 372590, -129111, -16893, 657769]]]
  g := ![![![30482, -40786, 18269, 8095, -78944], ![-179895, 255045, -237074, -50428, 789014], ![-253186, 276218, 412171, -55658, -753956], ![2325817, -3204678, 2229060, 634803, -8111104], ![111375, -171804, 272104, 33794, -801783]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2

def I3N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24613923, 9816728, -40004326, -11765856, 163882598]] i)))

def SI3N3: IdealEqSpanCertificate' Table ![![24613923, 9816728, -40004326, -11765856, 163882598]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![24613923, 9816728, -40004326, -11765856, 163882598], ![-68916364, -27485817, 112007878, 32943150, -458853932], ![192958564, 76957244, -313610117, -92237316, 1284742052], ![-115768196, -46171896, 188155104, 55339147, -770800388], ![73486204, 29308340, -119435054, -35127594, 489280249]]]
  hmulB := by decide  
  f := ![![![-2303, 5384, -2154, -1068, 9794]], ![![535, -10713, 10452, 2118, -34334]], ![![19234, -2988, -25633, 636, 59064]], ![![-38753, 151136, -100366, -29945, 371082]], ![![2380, 9596, -13622, -1890, 40993]]]
  g := ![![![35523901, 9816728, -40004326, -11765856, 163882598], ![-99463151, -27485817, 112007878, 32943150, -458853932], ![278486290, 76957244, -313610117, -92237316, 1284742052], ![-167081885, -46171896, 188155104, 55339147, -770800388], ![106058522, 29308340, -119435054, -35127594, 489280249]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N3 : Nat.card (O ⧸ I3N3) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N3)

lemma isPrimeI3N3 : Ideal.IsPrime I3N3 := prime_ideal_of_norm_prime hp3.out _ NI3N3
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-8949, 20441, -9357, -1449, 44454]] ![![-8949, 20441, -9357, -1449, 44454]]
  ![![-2973517467, 6791831502, -3109021643, -481455846, 14770574412]] where
 M := ![![![-2973517467, 6791831502, -3109021643, -481455846, 14770574412]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-2973517467, 6791831502, -3109021643, -481455846, 14770574412]] ![![-160763, 367502, -168390, -26102, 799880]]
  ![![-17760642297478807, 40567204056467424, -18570000650192451, -2875707022949966, 88223759088920180]] where
 M := ![![![-17760642297478807, 40567204056467424, -18570000650192451, -2875707022949966, 88223759088920180]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-17760642297478807, 40567204056467424, -18570000650192451, -2875707022949966, 88223759088920180]] ![![16349, -40786, 18269, 8095, -78944]]
  ![![-49146073951, 112254882292, -51385676820, -7957466157, 244126947424]] where
 M := ![![![-49146073951, 112254882292, -51385676820, -7957466157, 244126947424]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![-49146073951, 112254882292, -51385676820, -7957466157, 244126947424]] ![![24613923, 9816728, -40004326, -11765856, 163882598]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![1743874148727, -3983331949140, 1823479580118, 282391366041, -8663069913990]]]
 hmul := by decide  
 g := ![![![![581291382909, -1327777316380, 607826526706, 94130455347, -2887689971330]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1, I3N2, I3N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N2
    exact isPrimeI3N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5887, -31884, 24604, 6312, -86534]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5887, -31884, 24604, 6312, -86534]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![5887, -31884, 24604, 6312, -86534], ![34204, 42139, -95384, -8244, 265532], ![-349696, 901924, -421721, -178980, 1788352], ![3720, -1489300, 1555432, 294199, -5018680], ![-88028, 115504, 10746, -23022, 73321]]]
  hmulB := by decide  
  f := ![![![-4621, 3004, 1128, 588, -3598]], ![![-1148, 5107, -3920, -852, 17444]], ![![-16144, 28540, -8777, -684, 44848]], ![![-30264, 73764, -36376, -6041, 170888]], ![![-8286, 12856, -3238, -78, 17301]]]
  g := ![![![35791, -31884, 24604, 6312, -86534], ![-99372, 42139, -95384, -8244, 265532], ![-785280, 901924, -421721, -178980, 1788352], ![2008216, -1489300, 1555432, 294199, -5018680], ![-46934, 115504, 10746, -23022, 73321]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5887, -31884, 24604, 6312, -86534]] ![![5887, -31884, 24604, 6312, -86534]]
  ![![-2018928359, 1264192376, 1698036140, -254443644, -2997702912]] where
 M := ![![![-2018928359, 1264192376, 1698036140, -254443644, -2997702912]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-2018928359, 1264192376, 1698036140, -254443644, -2997702912]] ![![5887, -31884, 24604, 6312, -86534]]
  ![![-299506179652313, 1681839103725532, -1314338039500720, -332923935268044, 4604252455702186]] where
 M := ![![![-299506179652313, 1681839103725532, -1314338039500720, -332923935268044, 4604252455702186]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-299506179652313, 1681839103725532, -1314338039500720, -332923935268044, 4604252455702186]] ![![5887, -31884, 24604, 6312, -86534]]
  ![![108839574675709558129, -77379356476599623696, -81868884350507038472, 15539668865661177288, 130427596778856644352]] where
 M := ![![![108839574675709558129, -77379356476599623696, -81868884350507038472, 15539668865661177288, 130427596778856644352]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![108839574675709558129, -77379356476599623696, -81868884350507038472, 15539668865661177288, 130427596778856644352]] ![![5887, -31884, 24604, 6312, -86534]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![15199803527956264855805455, -88648761053758598746915900, 70156942388704005057910500, 17546854638765730805059200, -244800945624224154659066150]]]
 hmul := by decide  
 g := ![![![![3039960705591252971161091, -17729752210751719749383180, 14031388477740801011582100, 3509370927753146161011840, -48960189124844830931813230]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![216501, -20715, 58550, 12735, -225620]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![216501, -20715, 58550, 12735, -225620]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![3, 5, 1, 0, 0], ![3, 6, 0, 1, 0], ![0, 1, 0, 0, 1]] where
  M :=![![![216501, -20715, 58550, 12735, -225620], ![171070, -16539, 46380, 10095, -178690], ![135290, -12710, 36046, 7905, -139430], ![80080, -6120, 20935, 4426, -80560], ![-3990, 560, -1270, -270, 4771]]]
  hmulB := by decide  
  f := ![![![-218643, -86845, 355000, 104430, -1454210]], ![![610960, 245937, -995235, -292590, 4077680]], ![![97213, 42610, -161819, -47385, 663890]], ![![574903, 236461, -941515, -276524, 3858860]], ![![-6230, -1319, 8965, 2700, -36429]]]
  g := ![![![378, -23465, 58550, 12735, -225620], ![235, -18617, 46380, 10095, -178690], ![491, -14420, 36046, 7905, -139430], ![571, -8113, 20935, 4426, -80560], ![90, 537, -1270, -270, 4771]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [5, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 6], [0, 1]]
 g := ![![[1, 1], [2, 1]], ![[3, 6], [4, 6]]]
 h' := ![![[2, 6], [4, 6], [0, 1]], ![[0, 1], [2, 1], [2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [6, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [5, 5, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-297123, 521737, -128379, -51869, 846456]
  a := ![99, -397, 273, 62, -1053]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![34803, 89770, -128379, -51869, 846456]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![218643, 86845, -355000, -104430, 1454210]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![218643, 86845, -355000, -104430, 1454210]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![2, 5, 5, 1, 0], ![3, 1, 2, 0, 1]] where
  M :=![![![218643, 86845, -355000, -104430, 1454210], ![-610960, -245937, 995235, 292590, -4077680], ![1718380, 670880, -2778442, -817965, 11378540], ![-1014490, -440140, 1684195, 493418, -6908570], ![654570, 255170, -1057990, -311490, 4332683]]]
  hmulB := by decide  
  f := ![![![-216501, 20715, -58550, -12735, 225620]], ![![-171070, 16539, -46380, -10095, 178690]], ![![-135290, 12710, -36046, -7905, 139430]], ![![-292126, 27685, -78595, -17128, 303200]], ![![-155309, 14792, -41836, -9120, 161377]]]
  g := ![![![-562161, -120745, -391610, -104430, 1454210], ![1576700, 338399, 1098235, 292590, -4077680], ![-4397330, -945405, -3063671, -817965, 11378540], ![2674912, 571620, 1862035, 493418, -6908570], ![-1674357, -360009, -1166558, -311490, 4332683]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 3 2 2 [4, 4, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 4, 5], [3, 2, 2], [0, 1]]
 g := ![![[0, 3, 2], [1]], ![[1, 6], [3, 1, 3, 6]], ![[3, 1, 0, 4], [1, 4, 6, 1]]]
 h' := ![![[0, 4, 5], [3, 3, 3], [0, 1]], ![[3, 2, 2], [2, 5], [0, 4, 5]], ![[0, 1], [2, 6, 4], [3, 2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2], []]
 b := ![[], [2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 3
  hpos := by decide
  P := [4, 4, 4, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-300550869, 451251915, -67180071, -3140013, 701127264]
  a := ![-97, 327, -267, -60, 1032]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-342521805, -33453612, -207676362, -3140013, 701127264]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![216501, -20715, 58550, 12735, -225620]] ![![218643, 86845, -355000, -104430, 1454210]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14075, -10095, 27337, 7797, -113132]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-14075, -10095, 27337, 7797, -113132]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![5, 9, 1, 0, 0], ![5, 7, 0, 1, 0], ![9, 7, 0, 0, 1]] where
  M :=![![![-14075, -10095, 27337, 7797, -113132], ![54730, -6731, -60521, -19350, 240650], ![-55600, -204170, 271540, 69987, -1158800], ![240762, -351238, 53941, -8408, -335014], ![-19370, -81878, 105300, 26946, -450281]]]
  hmulB := by decide  
  f := ![![![-36511, 3301, -9777, -2112, 37670]], ![![-28876, 3653, -8770, -1875, 33172]], ![![-42503, 4958, -12155, -2670, 46596]], ![![-35997, 2726, -9402, -1985, 36174]], ![![-48223, 4996, -13485, -2913, 51657]]]
  g := ![![![75313, 43747, 27337, 7797, -113132], ![-155615, -91922, -60521, -19350, 240650], ![787815, 452151, 271540, 69987, -1158800], ![275293, 142477, 53941, -8408, -335014], ![306539, 175797, 105300, 26946, -450281]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [2, 5, 1] where
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
 g := ![![[8, 3], [5, 3], [1]], ![[4, 8], [1, 8], [1]]]
 h' := ![![[6, 10], [1, 6], [9, 6], [0, 1]], ![[0, 1], [4, 5], [1, 5], [6, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [1, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [2, 5, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27038, 44862, -8826, -4444, 67398]
  a := ![30, -122, 83, 19, -319]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-51570, -28762, -8826, -4444, 67398]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-331861, 31774, -89749, -19525, 345860]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-331861, 31774, -89749, -19525, 345860]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![7, 4, 1, 0, 0], ![4, 2, 0, 1, 0], ![1, 8, 0, 0, 1]] where
  M :=![![![-331861, 31774, -89749, -19525, 345860], ![-262170, 25099, -70892, -15422, 273190], ![-207096, 19834, -56027, -12190, 215912], ![-123580, 11830, -33408, -7267, 128740], ![6124, -584, 1648, 358, -6349]]]
  hmulB := by decide  
  f := ![![![49, -94, 25, 19, -140]], ![![-138, 881, -718, -172, 2486]], ![![-127, 228, -50, -43, 320]], ![![232, -692, 376, 141, -1492]], ![![-105, 562, -433, -109, 1527]]]
  g := ![![![2602, -212460, -89749, -19525, 345860], ![2052, -167819, -70892, -15422, 273190], ![1631, -132634, -56027, -12190, 215912], ![964, -79084, -33408, -7267, 128740], ![-45, 3900, 1648, 358, -6349]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [1, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 10], [0, 1]]
 g := ![![[6, 1], [5, 3], [1]], ![[0, 10], [9, 8], [1]]]
 h' := ![![[5, 10], [6, 1], [10, 5], [0, 1]], ![[0, 1], [0, 10], [2, 6], [5, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [6, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [1, 6, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-400670, 639408, -104966, -58038, 919146]
  a := ![-113, 472, -311, -72, 1202]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-32082, -561620, -104966, -58038, 919146]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4065, -21553, 16504, 4267, -58188]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![4065, -21553, 16504, 4267, -58188]] 
 ![![11, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![4065, -21553, 16504, 4267, -58188], ![22502, 30433, -65592, -5959, 183846], ![-236594, 601186, -275860, -119309, 1179438], ![9776, -1019324, 1053761, 201376, -3408912], ![-59010, 74984, 9766, -14950, 40891]]]
  hmulB := by decide  
  f := ![![![-207255, -83799, 338104, 99380, -1385358]], ![![-116449, -48014, 190935, 56072, -782574]], ![![-278435, -115823, 457372, 134261, -1874886]], ![![-39349, -26367, 74661, 21380, -308568]], ![![-149979, -61983, 245970, 72226, -1008191]]]
  g := ![![![31235, -21553, 16504, 4267, -58188], ![-60888, 30433, -65592, -5959, 183846], ![-798025, 601186, -275860, -119309, 1179438], ![1585663, -1019324, 1053761, 201376, -3408912], ![-82003, 74984, 9766, -14950, 40891]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-14075, -10095, 27337, 7797, -113132]] ![![-331861, 31774, -89749, -19525, 345860]]
  ![![-207255, -83799, 338104, 99380, -1385358]] where
 M := ![![![-207255, -83799, 338104, 99380, -1385358]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![-207255, -83799, 338104, 99380, -1385358]] ![![4065, -21553, 16504, 4267, -58188]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, 116, -75, -23, 280]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-31, 116, -75, -23, 280]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![5, 10, 1, 0, 0], ![11, 2, 0, 1, 0], ![11, 4, 0, 0, 1]] where
  M :=![![![-31, 116, -75, -23, 280], ![-54, -375, 474, 74, -1462], ![1296, -2314, 485, 460, -3152], ![-840, 6850, -5922, -1355, 20120], ![264, -68, -324, 14, 721]]]
  hmulB := by decide  
  f := ![![![53, 128, -39, -5, 208]], ![![-306, 861, -360, -52, 1742]], ![![-395, 1140, -490, -73, 2360]], ![![-461, 1292, -567, -86, 2720]], ![![-125, 548, -225, -33, 1097]]]
  g := ![![![-191, -16, -75, -23, 280], ![988, 45, 474, 74, -1462], ![2191, 348, 485, 460, -3152], ![-13665, -900, -5922, -1355, 20120], ![-477, 20, -324, 14, 721]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [8, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 12], [0, 1]]
 g := ![![[12, 10], [3], [8, 1]], ![[1, 3], [3], [3, 12]]]
 h' := ![![[8, 12], [3, 6], [1, 4], [0, 1]], ![[0, 1], [12, 7], [7, 9], [8, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [10, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [8, 5, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-507634, 794533, -115313, -74295, 1106382]
  a := ![135, -541, 372, 87, -1436]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-868002, -179175, -115313, -74295, 1106382]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-533, 75, -151, -32, 592]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-533, 75, -151, -32, 592]] 
 ![![13, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-533, 75, -151, -32, 592], ![-480, 203, -190, -37, 800], ![-786, 1064, -550, -89, 2542], ![-1304, 2566, -1225, -194, 5768], ![-178, 420, -186, -28, 889]]]
  hmulB := by decide  
  f := ![![![-23, -491, 549, 97, -1742]], ![![95, -338, 212, 67, -800]], ![![-395, 1899, -1399, -376, 4994]], ![![-743, -591, 1732, 115, -4672]], ![![-162, 302, -74, -60, 437]]]
  g := ![![![-233, 75, -151, -32, 592], ![-338, 203, -190, -37, 800], ![-1189, 1064, -550, -89, 2542], ![-2723, 2566, -1225, -194, 5768], ![-428, 420, -186, -28, 889]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, 0, 0, 0]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![-1, 1, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![0, 0, 0, 0, 13]] where
  M :=![![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 0, -2, 3, 0], ![-22, 88, -61, -14, 234], ![-2, 6, -4, 0, 13]]]
  hmulB := by decide  
  f := ![![![-55, 5, -14, -3, 54]], ![![-54, 5, -14, -3, 54]], ![![-54, 6, -14, -3, 54]], ![![-36, 4, -9, -2, 36]], ![![-2, 4, 0, 0, 1]]]
  g := ![![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 0, -2, 3, 0], ![-18, 88, -61, -14, 18], ![-2, 6, -4, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P2 : CertificateIrreducibleZModOfList' 13 2 2 3 [4, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 12], [0, 1]]
 g := ![![[10, 10], [9], [12, 1]], ![[0, 3], [9], [11, 12]]]
 h' := ![![[12, 12], [6, 6], [4, 10], [0, 1]], ![[0, 1], [0, 7], [7, 3], [12, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [7, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N2 : CertifiedPrimeIdeal' SI13N2 13 where
  n := 2
  hpos := by decide
  P := [4, 1, 1]
  hirr := P13P2
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1490, 4760, -2999, -426, 12350]
  a := ![3, -16, 9, 0, -32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1478, 4760, -2999, -426, 950]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N2 B_one_repr
lemma NI13N2 : Nat.card (O ⧸ I13N2) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-31, 116, -75, -23, 280]] ![![-533, 75, -151, -32, 592]]
  ![![-55, 5, -14, -3, 54]] where
 M := ![![![-55, 5, -14, -3, 54]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-55, 5, -14, -3, 54]] ![![-1, 1, 0, 0, 0]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [4, 0, 9, 1, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 16, 4, 12, 13], [6, 15, 3, 16, 13], [13, 15, 0, 5, 6], [14, 4, 10, 1, 2], [0, 1]]
 g := ![![[0, 14, 16], [9, 0, 16, 1], [], []], ![[7, 13, 14, 2, 11, 7, 4, 9], [15, 0, 14, 15], [14, 7, 1, 15], [0, 4, 7, 16]], ![[6, 6, 15, 3, 7, 13, 7, 15], [3, 6, 16, 2], [5, 11, 10, 15], [7, 3, 9, 16]], ![[7, 2, 9, 0, 7, 9, 8, 3], [8, 9, 14, 4], [1, 10, 11, 9], [3, 16, 7, 2]], ![[3, 5, 9, 7, 13, 5, 4, 16], [11, 13, 10, 16], [8, 0, 15, 2], [14, 3, 0, 4]]]
 h' := ![![[0, 16, 4, 12, 13], [15, 0, 8, 4], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[6, 15, 3, 16, 13], [16, 8, 13, 15, 11], [12, 6, 7, 13, 7], [0, 1, 7, 11, 10], [0, 16, 4, 12, 13]], ![[13, 15, 0, 5, 6], [3, 3, 9, 2, 14], [10, 9, 12, 7, 11], [8, 15, 9, 14, 10], [6, 15, 3, 16, 13]], ![[14, 4, 10, 1, 2], [10, 5, 7, 0, 14], [12, 1, 7, 13, 2], [4, 3, 0, 9, 3], [13, 15, 0, 5, 6]], ![[0, 1], [8, 1, 14, 13, 12], [1, 1, 8, 1, 13], [4, 15, 0, 0, 11], [14, 4, 10, 1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 5, 7, 10], [], [], []]
 b := ![[], [10, 16, 5, 16, 11], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 5
  hpos := by decide
  P := [4, 0, 9, 1, 1, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-385495489370802, 939790633006078, -455021933129276, -94053069634317, 2057088947809938]
  a := ![-64, 259, -173, -42, 681]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-22676205257106, 55281801941534, -26765996066428, -5532533507901, 121005232224114]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3935849, -1569729, 6396830, 1881401, -26205394]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-3935849, -1569729, 6396830, 1881401, -26205394]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![15, 5, 18, 11, 1]] where
  M :=![![![-3935849, -1569729, 6396830, 1881401, -26205394], ![11019966, 4395075, -17910444, -5267723, 73372318], ![-30854730, -12305750, 50147350, 14749067, -205434730], ![18511752, 7383012, -30086639, -8848918, 123253576], ![-11750694, -4686512, 19098080, 5617024, -78237613]]]
  hmulB := by decide  
  f := ![![![-725, 1673, -764, -118, 3632]], ![![-4668, 10683, -4893, -758, 23236]], ![![-29796, 68044, -31130, -4825, 147932]], ![![-73170, 167080, -76453, -11830, 363310]], ![![-73029, 166784, -76312, -11816, 362637]]]
  g := ![![![20481319, 6813539, 25162838, 15270565, -26205394], ![-57345516, -19077185, -70453272, -42755959, 73372318], ![160561380, 53414100, 197261710, 119712163, -205434730], ![-96331152, -32046572, -118350053, -71823066, 123253576], ![61148079, 20342187, 75125006, 45591093, -78237613]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [15, 18, 10, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 10, 12, 5], [9, 8, 10, 4], [6, 0, 16, 10], [0, 1]]
 g := ![![[1, 3, 13, 16], [18, 5], [1], []], ![[17, 10, 8, 16, 14, 11], [12, 9, 18, 5, 1, 9], [6, 15, 4], [13, 6, 6]], ![[14, 4, 5, 11], [6, 14, 6, 3, 8, 5], [2, 7, 1], [4, 4, 16]], ![[2, 12, 8, 14, 3, 12], [1, 8, 3, 13, 15, 10], [17, 9, 9], [16, 16, 5]]]
 h' := ![![[4, 10, 12, 5], [15, 16, 4, 4], [4, 1, 9], [0, 0, 1], [0, 1]], ![[9, 8, 10, 4], [16, 5, 11, 5], [12, 18, 2, 6], [11, 3, 1, 17], [4, 10, 12, 5]], ![[6, 0, 16, 10], [9, 12, 6], [12, 2, 7, 14], [2, 12, 6, 18], [9, 8, 10, 4]], ![[0, 1], [9, 5, 17, 10], [17, 17, 1, 18], [5, 4, 11, 3], [6, 0, 16, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 4, 3], []]
 b := ![[], [], [18, 16, 8, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [15, 18, 10, 0, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-448983347440, 1393079695260, -895565459538, -65238383160, 3705630618060]
  a := ![-91, 366, -251, -58, 968]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2949128558860, -901845968160, -3557732451822, -2148798693780, 3705630618060]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-725, 1673, -764, -118, 3632]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-725, 1673, -764, -118, 3632]] 
 ![![19, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![-725, 1673, -764, -118, 3632], ![-4668, 10683, -4893, -758, 23236], ![-29796, 68044, -31130, -4825, 147932], ![-73170, 167080, -76453, -11830, 363310], ![-12138, 27714, -12680, -1964, 60257]]]
  hmulB := by decide  
  f := ![![![-3935849, -1569729, 6396830, 1881401, -26205394]], ![![-2527251, -1007940, 4107474, 1208068, -16826768]], ![![-2245383, -895523, 3649360, 1073330, -14950048]], ![![-61447, -24507, 99869, 29373, -409126]], ![![-2897107, -1155449, 4708590, 1384865, -19289313]]]
  g := ![![![-3310, 1673, -764, -118, 3632], ![-21160, 10683, -4893, -758, 23236], ![-134747, 68044, -31130, -4825, 147932], ![-330909, 167080, -76453, -11830, 363310], ![-54885, 27714, -12680, -1964, 60257]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-3935849, -1569729, 6396830, 1881401, -26205394]] ![![-725, 1673, -764, -118, 3632]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97351, -218423, 83168, 43374, -387498]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![97351, -218423, 83168, 43374, -387498]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![14, 20, 14, 1, 0], ![8, 7, 17, 0, 1]] where
  M :=![![![97351, -218423, 83168, 43374, -387498], ![-179232, 1589275, -1397413, -314358, 4724544], ![-2533212, 504528, 3264350, -105585, -7416156], ![4873990, -18605700, 12203279, 3686690, -45316410], ![-272326, -1275022, 1744182, 251226, -5288581]]]
  hmulB := by decide  
  f := ![![![-214897, 21463, -61734, -13671, 238632]], ![![-176502, 13847, -37400, -7479, 141834]], ![![-119130, 16350, -59870, -14973, 235590]], ![![-360582, 34958, -106725, -23938, 412428]], ![![-216074, 23801, -77444, -18204, 301679]]]
  g := ![![![112613, 70721, 263626, 43374, -387498], ![-1459764, -1095451, -3361463, -314358, 4724544], ![2533662, 2370840, 5687704, -105585, -7416156], ![13730070, 9777190, 31781243, 3686690, -45316410], ![1674746, 1335675, 3831865, 251226, -5288581]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [9, 14, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 13, 4], [8, 9, 19], [0, 1]]
 g := ![![[12, 12, 8], [7, 9, 4], [4, 15, 1], []], ![[13, 8, 9, 18], [18, 4, 4, 9], [14, 8, 20, 2], [22, 16]], ![[12, 12, 22, 21], [3, 10, 18, 20], [16, 7, 9, 14], [7, 16]]]
 h' := ![![[7, 13, 4], [6, 13, 10], [10, 16, 2], [0, 0, 1], [0, 1]], ![[8, 9, 19], [10, 22, 4], [8, 13, 13], [12, 6, 9], [7, 13, 4]], ![[0, 1], [5, 11, 9], [2, 17, 8], [1, 17, 13], [8, 9, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 9], []]
 b := ![[], [5, 21, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [9, 14, 8, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-890677678, 1384551008, -253097437, -10019616, 2245674225]
  a := ![-111, 448, -307, -66, 1181]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-813730298, -614555489, -1664751506, -10019616, 2245674225]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![30583, -10431, -34861, 2132, 74870]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![30583, -10431, -34861, 2132, 74870]] 
 ![![23, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![30583, -10431, -34861, 2132, 74870], ![-196644, 667419, -405102, -132299, 1547068], ![-183558, -2556548, 2954488, 504581, -9299014], ![2437896, -4710354, 1286689, 936164, -7137752], ![137406, -1000652, 843080, 197986, -2886289]]]
  hmulB := by decide  
  f := ![![![-24201757, -9653111, 39337151, 11569597, -161149364]], ![![-4419335, -1762834, 7183558, 2112777, -29428302]], ![![-29294416, -11684266, 47613966, 14003925, -195056388]], ![![-1363944, -544532, 2217869, 652280, -9085838]], ![![-8402965, -3351563, 13657749, 4016933, -55950633]]]
  g := ![![![17986, -10431, -34861, 2132, 74870], ![-161221, 667419, -405102, -132299, 1547068], ![90874, -2556548, 2954488, 504581, -9299014], ![1728190, -4710354, 1286689, 936164, -7137752], ![153213, -1000652, 843080, 197986, -2886289]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, 70, -32, -14, 138]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![-31, 70, -32, -14, 138]] 
 ![![23, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-31, 70, -32, -14, 138], ![32, -435, 404, 86, -1344], ![796, -464, -709, 94, 1308], ![-1296, 5484, -3810, -1085, 13872], ![104, 296, -466, -58, 1375]]]
  hmulB := by decide  
  f := ![![![-247961, -98890, 402992, 118526, -1650906]], ![![-174653, -69653, 283848, 83484, -1162818]], ![![-159981, -63802, 260007, 76472, -1065150]], ![![7580, 3028, -12326, -3625, 50496]], ![![-86091, -34334, 139918, 41152, -573191]]]
  g := ![![![-77, 70, -32, -14, 138], ![515, -435, 404, 86, -1344], ![333, -464, -709, 94, 1308], ![-6254, 5484, -3810, -1085, 13872], ![-387, 296, -466, -58, 1375]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![97351, -218423, 83168, 43374, -387498]] ![![30583, -10431, -34861, 2132, 74870]]
  ![![83159457217, -175974358282, 59925733765, 34955687725, -295168601072]] where
 M := ![![![83159457217, -175974358282, 59925733765, 34955687725, -295168601072]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![83159457217, -175974358282, 59925733765, 34955687725, -295168601072]] ![![-31, 70, -32, -14, 138]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![-36508344364899, 158891552957488, -111874690748955, -31472150558829, 405416876038774]]]
 hmul := by decide  
 g := ![![![![-1587319320213, 6908328389456, -4864116989085, -1368354372123, 17626820697338]]]]
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


lemma PB5356I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB5356I0 : PrimesBelowBoundCertificateInterval O 1 23 5356 where
  m := 9
  g := ![5, 5, 5, 2, 3, 3, 1, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB5356I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N1, I2N1]
    · exact ![I3N0, I3N0, I3N1, I3N2, I3N3]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N1, I13N2]
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
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![49, 343]
    · exact ![121, 121, 11]
    · exact ![169, 13, 169]
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
      exact NI2N1
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N1
      exact NI3N2
      exact NI3N3
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
      exact NI11N2
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
      exact NI23N1
      exact NI23N2
  β := ![I2N0, I2N1, I3N0, I3N1, I3N2, I3N3, I5N0, I7N0, I7N1, I11N0, I11N1, I11N2, I13N0, I13N1, I13N2, I19N1, I23N1, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N1, I2N1], [I3N0, I3N0, I3N1, I3N2, I3N3], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1], [I11N0, I11N1, I11N2], [I13N0, I13N1, I13N2], [], [I19N1], [I23N1, I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
