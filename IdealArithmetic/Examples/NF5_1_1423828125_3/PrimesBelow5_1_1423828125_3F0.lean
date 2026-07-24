
import IdealArithmetic.Examples.NF5_1_1423828125_3.RI5_1_1423828125_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8870856621, 3370584761, -46427484, 581071464, -1785255799]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-8870856621, 3370584761, -46427484, 581071464, -1785255799]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-8870856621, 3370584761, -46427484, 581071464, -1785255799], ![-20139188516, -21683312005, -6145537852, 3161436396, 30552047384], ![206656477260, 88891250616, 35551699671, -24050146588, -155896159984], ![-205139396824, -75612116831, -32690912756, 23080649867, 139856984761], ![115810347752, 39797820167, 17860720848, -12848654886, -75548028372]]]
  hmulB := by decide  
  f := ![![![-4857565411959523462, -332748387569010799, 494334455701090420, -3407020878951916678, -7347043598407400153]], ![![-12105902771019472012, -829267191586614277, 1231967940637193164, -8490892041901933564, -18310117911697232880]], ![![-60340054933921334236, -4133357820700647384, 6140559247909608359, -42321576666951249236, -91264033879676276752]], ![![-32995177114440347321, -2260204660415479203, 3357783485420588252, -23142304384999898451, -49905041772598015741]], ![![-21596014024944877613, -1479349887296593324, 2197737535772621284, -15147108570884792710, -32663864124699884743]]]
  g := ![![![-3833336143, 3370584761, -46427484, 581071464, -1785255799], ![-26926336148, -21683312005, -6145537852, 3161436396, 30552047384], ![193301391916, 88891250616, 35551699671, -24050146588, -155896159984], ![-184038515726, -75612116831, -32690912756, 23080649867, 139856984761], ![102103515505, 39797820167, 17860720848, -12848654886, -75548028372]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 5, 1, -2, -4]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![7, 5, 1, -2, -4]] 
 ![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![1, 1, 1, 0, 0], ![0, 1, 0, 1, 0], ![0, 1, 0, 0, 1]] where
  M :=![![![7, 5, 1, -2, -4], ![-11, 8, 9, -5, -24], ![-133, -84, -11, 33, 52], ![43, -5, -19, 6, 48], ![-33, -7, 7, 1, -15]]]
  hmulB := by decide  
  f := ![![![-1, -1, -1, 3, 8]], ![![33, 4, 0, 11, 20]], ![![41, 3, -7, 40, 88]], ![![53, 4, -1, 20, 40]], ![![24, 3, -2, 16, 33]]]
  g := ![![![3, 5, 1, -2, -4], ![-10, 14, 9, -5, -24], ![-61, -79, -11, 33, 52], ![31, -20, -19, 6, 48], ![-20, 0, 7, 1, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P1 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
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

def PI2N1 : CertifiedPrimeIdeal' SI2N1 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![31013, -173521, -97415, 240798, 562022]
  a := ![200, 227, 138, -177, -581]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![64214, -439463, -97415, 240798, 562022]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N1 B_one_repr
lemma NI2N1 : Nat.card (O ⧸ I2N1) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1147857084, 228780537, -231891103, -30135664, 488123191]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![1147857084, 228780537, -231891103, -30135664, 488123191]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![1147857084, 228780537, -231891103, -30135664, 488123191], ![3974451065, 4097379797, 1440317552, -1804051705, -4748784120], ![-18509438358, -1301121021, 5360024476, -742087366, -12523174780], ![-5658589611, -8942248050, -4160455720, 4167114631, 12816975143], ![439741063, 3722384868, 2378040488, -1880702689, -6893831253]]]
  hmulB := by decide  
  f := ![![![-1018004024, -467452368, -181218130, 120329531, 802834553]], ![![2519081492, 766846634, 368154157, -273274862, -1526724778]], ![![-9112895447, -1959531471, -1164095352, 937429927, 4562102088]], ![![6955349340, 1152963633, 817939055, -693969107, -3077807657]], ![![-3852124788, -655089597, -456409175, 385383763, 1724108580]]]
  g := ![![![588996374, 228780537, -231891103, -30135664, 488123191], ![2889251385, 4097379797, 1440317552, -1804051705, -4748784120], ![-8883675496, -1301121021, 5360024476, -742087366, -12523174780], ![-4912852121, -8942248050, -4160455720, 4167114631, 12816975143], ![1160221876, 3722384868, 2378040488, -1880702689, -6893831253]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2

def I2N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 1, -2, 14, 30]] i)))

def SI2N3: IdealEqSpanCertificate' Table ![![19, 1, -2, 14, 30]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![19, 1, -2, 14, 30], ![98, 5, -11, 70, 152], ![505, 39, -51, 343, 744], ![248, 20, -23, 173, 370], ![158, 10, -17, 110, 239]]]
  hmulB := by decide  
  f := ![![![-55, -2, -5, 5, 16]], ![![9, -14, -2, 0, 14]], ![![46, 83, 21, -9, -110]], ![![-144, -81, -29, 18, 132]], ![![48, 43, 13, -7, -63]]]
  g := ![![![-12, 1, -2, 14, 30], ![-59, 5, -11, 70, 152], ![-285, 39, -51, 343, 744], ![-146, 20, -23, 173, 370], ![-92, 10, -17, 110, 239]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N3 : Nat.card (O ⧸ I2N3) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N3)

lemma isPrimeI2N3 : Ideal.IsPrime I2N3 := prime_ideal_of_norm_prime hp2.out _ NI2N3
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-8870856621, 3370584761, -46427484, 581071464, -1785255799]] ![![7, 5, 1, -2, -4]]
  ![![-9098059027, -3898263088, -1562039857, 1057855450, 6845430309]] where
 M := ![![![-9098059027, -3898263088, -1562039857, 1057855450, 6845430309]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-9098059027, -3898263088, -1562039857, 1057855450, 6845430309]] ![![1147857084, 228780537, -231891103, -30135664, 488123191]]
  ![![799097335, 5791535074, 3661153065, -2917361321, -10632393964]] where
 M := ![![![799097335, 5791535074, 3661153065, -2917361321, -10632393964]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![799097335, 5791535074, 3661153065, -2917361321, -10632393964]] ![![19, 1, -2, 14, 30]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![28211730522, 7870576180, -4173879028, -1896525408, 7618285492]]]
 hmul := by decide  
 g := ![![![![14105865261, 3935288090, -2086939514, -948262704, 3809142746]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N2, I2N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-48, -29, -7, -1, 2]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-48, -29, -7, -1, 2]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-48, -29, -7, -1, 2], ![19, -9, -30, -55, -44], ![168, 483, 184, -540, -1188], ![-593, -100, 88, -148, -482], ![77, 82, 2, -133, -219]]]
  hmulB := by decide  
  f := ![![![-4456, -554, -486, 433, 1754]], ![![3072, -104, 235, -268, -636]], ![![-2173, 2503, 334, 37, -2416]], ![![-2102, -2805, -753, 364, 3828]], ![![-1988, 1141, 69, 106, -855]]]
  g := ![![![-17, -29, -7, -1, 2], ![54, -9, -30, -55, -44], ![1028, 483, 184, -540, -1188], ![173, -100, 88, -148, -482], ![216, 82, 2, -133, -219]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![572888632174, 59845768626, 60139715152, -54954376407, -212079958922]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![572888632174, 59845768626, 60139715152, -54954376407, -212079958922]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![572888632174, 59845768626, 60139715152, -54954376407, -212079958922], ![-1086956192154, 93693415100, -71434042987, 91251747622, 157917131980], ![279385536633, -1153503011493, -214185508288, 47472184823, 1291711877576], ![750322768884, 1163186889033, 302126497623, -140100028493, -1557438035122], ![-658688962682, -660823541319, -191041958705, 100363017474, 942203091697]]]
  hmulB := by decide  
  f := ![![![-1567677814, -59181927, 488599497, -89085945, -1160050130]], ![![-3678765907, -2300393743, -320444238, 902502973, 1488631440]], ![![6785753738, -1305513531, -3174821240, 1188730336, 8063668584]], ![![3479794517, 5241758874, 2383847588, -2430250584, -7380550806]], ![![-2151768437, -2458237656, -942615730, 1100096219, 3038379445]]]
  g := ![![![288995445092, 59845768626, 60139715152, -54954376407, -212079958922], ![-543270898528, 93693415100, -71434042987, 91251747622, 157917131980], ![112131483799, -1153503011493, -214185508288, 47472184823, 1291711877576], ![404924040934, 1163186889033, 302126497623, -140100028493, -1557438035122], ![-346696726992, -660823541319, -191041958705, 100363017474, 942203091697]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-48, -29, -7, -1, 2]] ![![-48, -29, -7, -1, 2]]
  ![![1324, -1464, -166, 5305, 9540]] where
 M := ![![![1324, -1464, -166, 5305, 9540]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![1324, -1464, -166, 5305, 9540]] ![![572888632174, 59845768626, 60139715152, -54954376407, -212079958922]]
  ![![174094, -933, 14339, -15499, -41894]] where
 M := ![![![174094, -933, 14339, -15499, -41894]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![174094, -933, 14339, -15499, -41894]] ![![572888632174, 59845768626, 60139715152, -54954376407, -212079958922]]
  ![![120722575674427217, 3447601451984136, 10786258759765920, -11004859340997336, -33881252657339984]] where
 M := ![![![120722575674427217, 3447601451984136, 10786258759765920, -11004859340997336, -33881252657339984]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![120722575674427217, 3447601451984136, 10786258759765920, -11004859340997336, -33881252657339984]] ![![572888632174, 59845768626, 60139715152, -54954376407, -212079958922]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![82486734831505091920911542238, 4694592187800665250846411690, 7851566149674318431590121184, -7666230582699445299180898335, -25909299497361379645383578730]]]
 hmul := by decide  
 g := ![![![![27495578277168363973637180746, 1564864062600221750282137230, 2617188716558106143863373728, -2555410194233148433060299445, -8636433165787126548461192910]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![124394, -42253, 1683, -8463, 19122]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![124394, -42253, 1683, -8463, 19122]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![124394, -42253, 1683, -8463, 19122], ![239289, 280463, 77720, -38997, -389940], ![-2651830, -1163661, -460938, 310058, 2027604], ![2650921, 993112, 425746, -299266, -1826194], ![-1500809, -523594, -233076, 167001, 988297]]]
  hmulB := by decide  
  f := ![![![-947671862, -64916530, 96440668, -664682311, -1433348986]], ![![-944705622, -64713340, 96138805, -662601838, -1428862564]], ![![-4708743327, -322553913, 479189444, -3302639393, -7121950952]], ![![-2953905986, -202345693, 300606867, -2071823746, -4467768160]], ![![-2253886422, -154393615, 229368751, -1580840902, -3408992031]]]
  g := ![![![14659, -42253, 1683, -8463, 19122], ![383208, 280463, 77720, -38997, -389940], ![-2338484, -1163661, -460938, 310058, 2027604], ![2170699, 993112, 425746, -299266, -1826194], ![-1191000, -523594, -233076, 167001, 988297]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![124394, -42253, 1683, -8463, 19122]] ![![124394, -42253, 1683, -8463, 19122]]
  ![![-50233054892, -37481735608, -11910274382, 6842902713, 56620549476]] where
 M := ![![![-50233054892, -37481735608, -11910274382, 6842902713, 56620549476]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-50233054892, -37481735608, -11910274382, 6842902713, 56620549476]] ![![124394, -42253, 1683, -8463, 19122]]
  ![![-50470270483396511, -17380632131066214, -7791277400965958, 5601761992454834, 32967202837716018]] where
 M := ![![![-50470270483396511, -17380632131066214, -7791277400965958, 5601761992454834, 32967202837716018]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-50470270483396511, -17380632131066214, -7791277400965958, 5601761992454834, 32967202837716018]] ![![124394, -42253, 1683, -8463, 19122]]
  ![![-24403695979188150724488, -5373950785715098770845, -3143404379167398586693, 2518313458594895184561, 12366169480553435418736]] where
 M := ![![![-24403695979188150724488, -5373950785715098770845, -3143404379167398586693, 2518313458594895184561, 12366169480553435418736]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-24403695979188150724488, -5373950785715098770845, -3143404379167398586693, 2518313458594895184561, 12366169480553435418736]] ![![124394, -42253, 1683, -8463, 19122]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-7869235052358711216654718030, -792092737247864525323860050, -819915783780619032797493100, 752975836788560121416624725, 2877810872967648299932907950]]]
 hmul := by decide  
 g := ![![![![-1573847010471742243330943606, -158418547449572905064772010, -163983156756123806559498620, 150595167357712024283324945, 575562174593529659986581590]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 2, -2, 16, 34]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![23, 2, -2, 16, 34]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![6, 4, 1, 0, 0], ![3, 0, 0, 1, 0], ![6, 4, 0, 0, 1]] where
  M :=![![![23, 2, -2, 16, 34], ![110, 5, -12, 82, 176], ![576, 30, -65, 408, 888], ![302, 28, -28, 201, 434], ![178, 8, -20, 130, 281]]]
  hmulB := by decide  
  f := ![![![9, -14, -2, 0, 14]], ![![110, 71, 24, -14, -112]], ![![-34, -10, -5, 4, 20]], ![![103, 26, 14, -11, -56]], ![![16, 12, 4, -2, -19]]]
  g := ![![![-31, -18, -2, 16, 34], ![-160, -93, -12, 82, 176], ![-798, -466, -65, 408, 888], ![-391, -228, -28, 201, 434], ![-254, -148, -20, 130, 281]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [2, 5, 1] where
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
 g := ![![[6, 4], [2, 1]], ![[0, 3], [4, 6]]]
 h' := ![![[2, 6], [3, 2], [0, 1]], ![[0, 1], [0, 5], [2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [3, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [2, 5, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10926886, -75053309, -40539567, 100997902, 234446066]
  a := ![4052, 4619, 2807, -3627, -11786]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-207929402, -121525615, -40539567, 100997902, 234446066]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -14, -2, 0, 14]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![9, -14, -2, 0, 14]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]] where
  M :=![![![9, -14, -2, 0, 14], ![110, 71, 24, -14, -112], ![-732, -270, -119, 84, 504], ![694, 224, 104, -77, -434], ![-382, -116, -56, 42, 231]]]
  hmulB := by decide  
  f := ![![![23, 2, -2, 16, 34]], ![![19, 1, -2, 14, 30]], ![![102, 6, -11, 72, 156]], ![![302, 28, -28, 201, 434]], ![![178, 8, -20, 130, 281]]]
  g := ![![![5, -14, -2, 0, 2], ![-15, 71, 24, -2, -16], ![36, -270, -119, 12, 72], ![-22, 224, 104, -11, -62], ![10, -116, -56, 6, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 3 2 2 [6, 2, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 3, 1], [2, 3, 6], [0, 1]]
 g := ![![[4, 3, 1], [1]], ![[2, 0, 1, 4], [6, 1, 1, 1]], ![[0, 1, 1, 6], [6, 6, 3, 6]]]
 h' := ![![[4, 3, 1], [1, 5, 6], [0, 1]], ![[2, 3, 6], [0, 0, 2], [4, 3, 1]], ![[0, 1], [0, 2, 6], [2, 3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5], []]
 b := ![[], [5, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 3
  hpos := by decide
  P := [6, 2, 1, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-296011822, 376641660, 177405288, -795637388, -1679588568]
  a := ![249, 285, 173, -225, -725]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-248155030, 376641660, 177405288, -113662484, -239941224]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![23, 2, -2, 16, 34]] ![![9, -14, -2, 0, 14]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![108626, 620597, 384557, -310859, -1120614]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![108626, 620597, 384557, -310859, -1120614]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![1, 10, 8, 1, 0], ![4, 3, 3, 0, 1]] where
  M :=![![![108626, 620597, 384557, -310859, -1120614], ![-5471765, -2418911, 203882, 826745, 260860], ![-5976688, -13307421, -7015782, 6387644, 21061980], ![13290439, 7739950, 770300, -2966972, -4266082], ![-6389267, -4785352, -1092742, 1973731, 4124509]]]
  hmulB := by decide  
  f := ![![![357892, 93842, 49196, -37883, -199102]], ![![-1164790, -207274, -139891, 117074, 532092]], ![![2946105, 212511, 289702, -276793, -978664]], ![![927736, -28079, 71695, -81306, -196372]], ![![704673, 33332, 65696, -65129, -213495]]]
  g := ![![![445631, 644639, 566661, -310859, -1120614], ![-667450, -1042631, -653878, 826745, 260860], ![-8782932, -12760891, -11027534, 6387644, 21061980], ![3029249, 4564356, 3391302, -2966972, -4266082], ![-2260094, -3354199, -2659647, 1973731, 4124509]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [8, 2, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 3, 6], [3, 7, 5], [0, 1]]
 g := ![![[3], [10, 1, 1], []], ![[0, 6, 3, 10], [3, 7, 6, 8], [6, 3]], ![[10, 8, 3, 1], [6, 4, 8, 1], [7, 3]]]
 h' := ![![[9, 3, 6], [8, 5], [0, 0, 1], [0, 1]], ![[3, 7, 5], [9, 4, 8], [0, 7, 7], [9, 3, 6]], ![[0, 1], [1, 2, 3], [8, 4, 3], [3, 7, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 5], []]
 b := ![[], [2, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [8, 2, 10, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![65380970782, -69493177622, -35895493647, 145852824052, 313931355489]
  a := ![-1453, -1643, -1008, 1275, 4217]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-121472479566, -224528680419, -194955650230, 145852824052, 313931355489]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18583374624, 5123341042, 2604457806, -1976304599, -10618912620]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![18583374624, 5123341042, 2604457806, -1976304599, -10618912620]] 
 ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![18583374624, 5123341042, 2604457806, -1976304599, -10618912620], ![-62583797164, -11942603284, -7690349013, 6373377048, 29614772188], ![165494058011, 15212568147, 16907375918, -15592180803, -58463620160], ![-118886094210, -4933861363, -10958361651, 11011334851, 35359766900], ![56913470392, 471901165, 4835437905, -5067252596, -14500218079]]]
  hmulB := by decide  
  f := ![![![-97558575152884, 33890990911981, 55907365270407, -24866382918821, -145389296872728]], ![![-104656264180169, -45136459684624, 4665873370689, 15232191874860, 2789796603332]], ![![91072544836368, -90516246661655, -92150921098930, 53491306300582, 250424312986700]], ![![155647023705135, 138600790101832, 41569060223580, -59408432945046, -143385250978196]], ![![-73195812094115, -64189925489028, -18876969877020, 27428989949289, 65501676943865]]]
  g := ![![![1749296466, 5123341042, 2604457806, -1976304599, -10618912620], ![-6418621242, -11942603284, -7690349013, 6373377048, 29614772188], ![18451712914, 15212568147, 16907375918, -15592180803, -58463620160], ![-13898847329, -4933861363, -10958361651, 11011334851, 35359766900], ![6802484295, 471901165, 4835437905, -5067252596, -14500218079]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37069323, -5412650, 8829656, -42774, -19612438]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![-37069323, -5412650, 8829656, -42774, -19612438]] 
 ![![11, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-37069323, -5412650, 8829656, -42774, -19612438], ![-147642108, -141580303, -46291234, 61550948, 155701832], ![583813942, -1470558, -197913911, 45267050, 477811888], ![228346544, 317106512, 138198914, -145661937, -431989078], ![-35413940, -137158916, -81144142, 67833696, 238388929]]]
  hmulB := by decide  
  f := ![![![-21545, -19130, -106660, 405654, 959598]], ![![301789, -8353, -104834, 485290, 1119810]], ![![1112285, 164768, -165395, 1055524, 2228134]], ![![503128, -66324, -123826, 566107, 1358754]], ![![409614, 70628, -78722, 467304, 992165]]]
  g := ![![![6152969, -5412650, 8829656, -42774, -19612438], ![24564043, -141580303, -46291234, 61550948, 155701832], ![-96863017, -1470558, -197913911, 45267050, 477811888], ![-38038386, 317106512, 138198914, -145661937, -431989078], ![5941540, -137158916, -81144142, 67833696, 238388929]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![108626, 620597, 384557, -310859, -1120614]] ![![18583374624, 5123341042, 2604457806, -1976304599, -10618912620]]
  ![![21545, 19130, 106660, -405654, -959598]] where
 M := ![![![21545, 19130, 106660, -405654, -959598]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![21545, 19130, 106660, -405654, -959598]] ![![-37069323, -5412650, 8829656, -42774, -19612438]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![-11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-101323, -46454, -18022, 11972, 79822]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-101323, -46454, -18022, 11972, 79822]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 4, 9, 1, 0], ![6, 6, 9, 0, 1]] where
  M :=![![![-101323, -46454, -18022, 11972, 79822], ![500834, 152311, 73164, -54322, -303360], ![-1810496, -388878, -231187, 186216, 905864], ![1482626, 275072, 180388, -149769, -690642], ![-765042, -129908, -90604, 76526, 342183]]]
  hmulB := by decide  
  f := ![![![-1135, -514, 14, 108, -10]], ![![-1146, -2297, -1272, 746, 3104]], ![![16100, 7626, -751, -4428, -3944]], ![![10546, 4850, -659, -3065, -2602]], ![![10248, 3920, -1207, -2670, -1109]]]
  g := ![![![-44635, -44098, -64936, 11972, 79822], ![178538, 168443, 253254, -54322, -303360], ![-557360, -505302, -773839, 186216, 905864], ![432806, 386000, 595699, -149769, -690642], ![-216780, -191470, -296845, 76526, 342183]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [4, 11, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 5, 1], [3, 7, 12], [0, 1]]
 g := ![![[3, 0, 1], [2, 3], [1]], ![[9, 6, 10, 12], [10, 3], [7, 0, 6, 1]], ![[12, 0, 0, 3], [11, 12], [6, 6, 4, 12]]]
 h' := ![![[1, 5, 1], [8, 2, 12], [9, 2, 4], [0, 1]], ![[3, 7, 12], [0, 2, 8], [12, 3, 4], [1, 5, 1]], ![[0, 1], [4, 9, 6], [3, 8, 5], [3, 7, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 4], []]
 b := ![[], [1, 6, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [4, 11, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-871210486, 891977439, 566284742, -1396446001, -3345042032]
  a := ![355, 384, 253, -278, -1018]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1476849362, 2042154895, 3326129003, -1396446001, -3345042032]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1135, -514, 14, 108, -10]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-1135, -514, 14, 108, -10]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![11, 4, 1, 0, 0], ![0, 7, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-1135, -514, 14, 108, -10], ![-1146, -2297, -1272, 746, 3104], ![16100, 7626, -751, -4428, -3944], ![-3218, 3604, 3280, -2977, -10746], ![2010, -808, -1384, 18, 2515]]]
  hmulB := by decide  
  f := ![![![-101323, -46454, -18022, 11972, 79822]], ![![500834, 152311, 73164, -54322, -303360]], ![![-70901, -22356, -10521, 7740, 43882]], ![![383728, 103173, 53272, -40771, -216474]], ![![-121202, -38580, -18060, 13254, 75443]]]
  g := ![![![-93, -102, 14, 108, -10], ![-922, -187, -1272, 746, 3104], ![4301, 3202, -751, -4428, -3944], ![3590, 871, 3280, -2977, -10746], ![-222, 354, -1384, 18, 2515]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [8, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 12], [0, 1]]
 g := ![![[8, 12], [10], [1, 1]], ![[7, 1], [10], [2, 12]]]
 h' := ![![[1, 12], [10, 5], [5, 6], [0, 1]], ![[0, 1], [2, 8], [11, 7], [1, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [5, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [8, 12, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![36524, 121320, -26580, -26292, 44688]
  a := ![-146, -120, -114, 42, 392]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2200, 31668, -26580, -26292, 44688]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-101323, -46454, -18022, 11972, 79822]] ![![-1135, -514, 14, 108, -10]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![110194443, 7548428, -11214040, 77288682, 166668586]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![110194443, 7548428, -11214040, 77288682, 166668586]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![15, 8, 0, 1, 0], ![11, 10, 14, 0, 1]] where
  M :=![![![110194443, 7548428, -11214040, 77288682, 166668586], ![549247828, 37624087, -55894668, 385233812, 830734408], ![2737642476, 187531344, -278598709, 1920140196, 4140671472], ![1386805028, 94997668, -141129368, 972683225, 2097535058], ![869621740, 59569988, -88497868, 609939312, 1315298919]]]
  hmulB := by decide  
  f := ![![![46595, 71060, 32512, -32990, -100526]], ![![-441796, -123145, 65436, 29644, -119512]], ![![-1187100, -1412592, -558317, 635916, 1786128]], ![![-96423, 35488, 56608, -25601, -147576]], ![![-1245307, -1212050, -402578, 528350, 1348101]]]
  g := ![![![-169558249, -133967464, -137916132, 77288682, 166668586], ![-845137520, -667740617, -687422140, 385233812, 830734408], ![-4212461568, -3328253232, -3426352901, 1920140196, 4140671472], ![-2133901705, -1685989336, -1735683540, 972683225, 2097535058], ![-1338103297, -1057231394, -1088393102, 609939312, 1315298919]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [15, 0, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 12, 11], [15, 4, 6], [0, 1]]
 g := ![![[3, 15, 8], [0, 1], [4, 1], []], ![[10, 6, 10, 14], [11, 1], [7, 16], [0, 2]], ![[4, 3, 4, 10], [], [16, 8], [5, 2]]]
 h' := ![![[6, 12, 11], [13, 0, 5], [8, 2, 16], [0, 0, 1], [0, 1]], ![[15, 4, 6], [6, 9, 3], [1, 12, 1], [2, 12, 4], [6, 12, 11]], ![[0, 1], [15, 8, 9], [7, 3], [14, 5, 12], [15, 4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 7], []]
 b := ![[], [9, 0, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [15, 0, 13, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33392407, 174894700, 119039906, -110922934, -381467530]
  a := ![169, 176, 136, -119, -479]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![342740849, 286879616, 321152078, -110922934, -381467530]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46595, -71060, -32512, 32990, 100526]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-46595, -71060, -32512, 32990, 100526]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![13, 2, 1, 0, 0], ![0, 10, 0, 1, 0], ![11, 7, 0, 0, 1]] where
  M :=![![![-46595, -71060, -32512, 32990, 100526], ![441796, 123145, -65436, -29644, 119512], ![1187100, 1412592, 558317, -635916, -1786128], ![-1196252, -522556, 48832, 177519, 44806], ![645404, 378772, 39380, -145576, -212831]]]
  hmulB := by decide  
  f := ![![![-110194443, -7548428, 11214040, -77288682, -166668586]], ![![-549247828, -37624087, 55894668, -385233812, -830734408]], ![![-309921523, -21229946, 31539445, -217374158, -468754818]], ![![-404663724, -27719914, 41180944, -283824785, -612051714]], ![![-348617377, -23880665, 35477352, -244514794, -527282013]]]
  g := ![![![-42925, -61154, -32512, 32990, 100526], ![-1304, -16831, -65436, -29644, 119512], ![798611, 1126942, 558317, -635916, -1786128], ![-136702, -159356, 48832, 177519, 44806], ![145565, 190917, 39380, -145576, -212831]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [15, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 16], [0, 1]]
 g := ![![[5, 8], [9], [15], [1]], ![[0, 9], [9], [15], [1]]]
 h' := ![![[10, 16], [1, 5], [0, 3], [2, 10], [0, 1]], ![[0, 1], [0, 12], [13, 14], [0, 7], [10, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [13, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [15, 7, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7017, -100395, -43123, 145298, 312230]
  a := ![139, 165, 94, -137, -409]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-168642, -214867, -43123, 145298, 312230]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![110194443, 7548428, -11214040, 77288682, 166668586]] ![![-46595, -71060, -32512, 32990, 100526]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![-17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [1, 16, 11, 9, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 11, 8, 11, 3], [5, 9, 15, 14], [3, 3, 10, 12, 11], [8, 14, 5, 1, 5], [0, 1]]
 g := ![![[18, 9, 14, 3, 17], [17, 17, 14, 17, 1], [], []], ![[2, 14, 14, 7, 18, 2, 12, 2], [0, 7, 10, 8, 7, 7, 4, 8], [14, 0, 13, 7], [12, 11, 10, 9]], ![[4, 5, 4, 17, 17, 0, 2], [9, 7, 4, 10, 15, 0, 8], [0, 10, 6, 17], [9, 6]], ![[14, 16, 1, 0, 9, 2, 14, 4], [4, 10, 10, 6, 8, 13, 18, 5], [5, 1], [11, 10, 3, 7]], ![[15, 2, 4, 11, 17, 18, 12, 17], [16, 4, 9, 18, 15, 6, 3, 7], [4, 1, 2, 4], [5, 1, 17, 6]]]
 h' := ![![[1, 11, 8, 11, 3], [2, 15, 2, 8, 13], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[5, 9, 15, 14], [11, 18, 14, 11, 8], [12, 15, 1, 3, 3], [8, 9, 9, 9, 11], [1, 11, 8, 11, 3]], ![[3, 3, 10, 12, 11], [16, 6, 16, 8, 7], [9, 8, 7, 16, 14], [16, 16, 17, 16, 6], [5, 9, 15, 14]], ![[8, 14, 5, 1, 5], [18, 12, 5, 1, 3], [18, 2, 0, 18, 4], [17, 3, 13, 1], [3, 3, 10, 12, 11]], ![[0, 1], [3, 6, 1, 10, 7], [0, 13, 11, 1, 16], [2, 10, 17, 12, 2], [8, 14, 5, 1, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 6, 8, 7], [], [], []]
 b := ![[], [16, 17, 10, 16, 4], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [1, 16, 11, 9, 2, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![589776976462, -192514728033, -64013038795, 14884073054, 243807368288]
  a := ![-43, -33, -25, 8, 114]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![31040893498, -10132354107, -3369107305, 783372266, 12831966752]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23477071169, 7924840686, 3591287038, -2595700432, -15146439484]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23477071169, 7924840686, 3591287038, -2595700432, -15146439484]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![2, 10, 10, 4, 1]] where
  M :=![![![23477071169, 7924840686, 3591287038, -2595700432, -15146439484], ![-91623224514, -21925543561, -12162000666, 9564806674, 48491903776], ![280125162802, 43182325848, 32272519717, -27745164618, -120120643336], ![-215691150158, -25684206654, -23291534410, 20888157143, 83566282124], ![107497094938, 10569339366, 11148720682, -10270208242, -39016050363]]]
  hmulB := by decide  
  f := ![![![1691522987631, 115871120250, -172139338270, 1186407932488, 2558420131556]], ![![8431142389298, 577542203785, -858002689038, 5913472227038, 12752061057216]], ![![42023763498310, 2878672414896, -4276585591909, 29474814538962, 63560733899336]], ![![21287931056686, 1458245877582, -2166385198382, 14931023965873, 32197890162524]], ![![26366644600228, 1806143147168, -2683224990444, 18493154704746, 39879419210181]]]
  g := ![![![2337823919, 6929966762, 6741551386, 2521306848, -15146439484], ![-8200305742, -22036720927, -21612219062, -8017513410, 48491903776], ![22624628238, 54103859096, 53629519699, 19684235162, -120120643336], ![-16644509322, -37449870778, -37345841550, -13625085711, 83566282124], ![8066486768, 17423036652, 17448227144, 6338869270, -39016050363]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [7, 17, 15, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 14, 17, 17], [10, 14, 10, 2], [20, 17, 19, 4], [0, 1]]
 g := ![![[21, 16, 9, 9], [0, 12, 1, 6], [21, 1], []], ![[0, 4, 20, 2, 22, 14], [15, 6, 8, 15, 8, 5], [7, 7, 3, 9, 5, 11], [18, 0, 13]], ![[9, 12, 18, 1, 9, 4], [22, 8, 5, 7, 15, 3], [2, 17, 17, 22, 4, 6], [9, 9, 4]], ![[8, 7, 5, 0, 2, 16], [4, 6, 7, 5, 14, 4], [16, 14, 1, 18, 1, 1], [17, 5, 16]]]
 h' := ![![[14, 14, 17, 17], [0, 20, 16, 3], [14, 4, 13, 12], [0, 0, 1], [0, 1]], ![[10, 14, 10, 2], [2, 17, 12, 17], [11, 0, 7, 16], [1, 17, 12, 5], [14, 14, 17, 17]], ![[20, 17, 19, 4], [12, 17, 1, 5], [14, 18, 17, 17], [14, 18, 11, 7], [10, 14, 10, 2]], ![[0, 1], [14, 15, 17, 21], [20, 1, 9, 1], [5, 11, 22, 11], [20, 17, 19, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [9, 10, 18], []]
 b := ![[], [], [3, 6, 22, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [7, 17, 15, 2, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1075019791852, -707086318512, -444682020253, 1842186346171, 4026117282225]
  a := ![-283, -311, -200, 231, 815]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-303357164026, -1781228658294, -1769819775761, -620099251423, 4026117282225]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1691522987631, 115871120250, -172139338270, 1186407932488, 2558420131556]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![1691522987631, 115871120250, -172139338270, 1186407932488, 2558420131556]] 
 ![![23, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![1691522987631, 115871120250, -172139338270, 1186407932488, 2558420131556], ![8431142389298, 577542203785, -858002689038, 5913472227038, 12752061057216], ![42023763498310, 2878672414896, -4276585591909, 29474814538962, 63560733899336], ![21287931056686, 1458245877582, -2166385198382, 14931023965873, 32197890162524], ![13348996727158, 914420447226, -1358472500674, 9362778820690, 20190291355435]]]
  hmulB := by decide  
  f := ![![![23477071169, 7924840686, 3591287038, -2595700432, -15146439484]], ![![7244546015, 2836856695, 1188789424, -825560786, -5135605676]], ![![29531972725, 7734983370, 4057582581, -3124872694, -16417831068]], ![![6953999502, 4396228014, 1485611226, -897523903, -6903336940]], ![![22026404557, 6317027436, 3139156536, -2365091982, -12891544417]]]
  g := ![![![-2570972162643, 115871120250, -172139338270, 1186407932488, 2558420131556], ![-12814624771477, 577542203785, -858002689038, 5913472227038, 12752061057216], ![-63872573344139, 2878672414896, -4276585591909, 29474814538962, 63560733899336], ![-32355858323526, 1458245877582, -2166385198382, 14931023965873, 32197890162524], ![-20289348254535, 914420447226, -1358472500674, 9362778820690, 20190291355435]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23477071169, 7924840686, 3591287038, -2595700432, -15146439484]] ![![1691522987631, 115871120250, -172139338270, 1186407932488, 2558420131556]]
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


lemma PB2349I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB2349I0 : PrimesBelowBoundCertificateInterval O 1 23 2349 where
  m := 9
  g := ![4, 5, 5, 2, 3, 2, 2, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB2349I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N2, I2N3]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N1]
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
    · exact ![2, 4, 2, 2]
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![49, 343]
    · exact ![1331, 11, 11]
    · exact ![2197, 169]
    · exact ![4913, 289]
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
      exact NI2N2
      exact NI2N3
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
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
  β := ![I2N0, I2N1, I2N2, I2N3, I3N0, I3N1, I5N0, I7N0, I7N1, I11N0, I11N1, I11N2, I13N0, I13N1, I17N1, I23N1]
  Il := ![[I2N0, I2N1, I2N2, I2N3], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1], [I11N0, I11N1, I11N2], [I13N0, I13N1], [I17N1], [], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
