
import IdealArithmetic.Examples.NF5_3_6075000000_7.RI5_3_6075000000_7
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![318535, 202190, 37190, -49673, -55339]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![318535, 202190, 37190, -49673, -55339]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![318535, 202190, 37190, -49673, -55339], ![1162119, 829069, 177483, -223917, -308049], ![6469029, 3980994, 698020, -950355, -978495], ![5774762, 4053146, 851472, -1081617, -1453424], ![-987129, -898752, -239709, 281040, 487543]]]
  hmulB := by decide  
  f := ![![![9822771, 627352, -789945, 416344, 1167086]], ![![-12254403, -153701, 895449, -496287, -1170393]], ![![24578253, -2120028, -1448312, 906111, 1244733]], ![![1793785, 1587350, -355115, 130177, 881916]], ![![3315639, -1291924, -51360, 85253, -288874]]]
  g := ![![![186937, 202190, 37190, -49673, -55339], ![735084, 829069, 177483, -223917, -308049], ![3723762, 3980994, 698020, -950355, -978495], ![3614093, 4053146, 851472, -1081617, -1453424], ![-737336, -898752, -239709, 281040, 487543]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![166, 6, 3, -18, -25]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![166, 6, 3, -18, -25]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![166, 6, 3, -18, -25], ![525, 406, 18, -144, -77], ![1617, 1344, 514, -1188, -1477], ![5796, 3113, 425, -1688, -1554], ![-1242, -373, 47, 87, -23]]]
  hmulB := by decide  
  f := ![![![-124582, -31015, 7433, -3018, -34168]], ![![296473, 73750, -17715, 7209, 81378]], ![![-2129993, -530188, 127119, -51636, -584266]], ![![1293406, 321752, -77281, 31447, 355015]], ![![-1614026, -401644, 96377, -39180, -442864]]]
  g := ![![![100, 6, 3, -18, -25], ![161, 406, 18, -144, -77], ![1212, 1344, 514, -1188, -1477], ![2750, 3113, 425, -1688, -1554], ![-490, -373, 47, 87, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![84, 21, -5, 2, 23]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![84, 21, -5, 2, 23]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![84, 21, -5, 2, 23], ![-483, -120, 29, -12, -133], ![2793, 697, -166, 66, 763], ![-1820, -450, 110, -47, -504], ![2091, 520, -125, 51, 574]]]
  hmulB := by decide  
  f := ![![![-7, 4, 1, -1, -1]], ![![7, 3, 2, -2, -4]], ![![70, 44, 0, -5, 3]], ![![14, 22, 8, -9, -14]], ![![18, -1, -4, 3, 7]]]
  g := ![![![34, 21, -5, 2, 23], ![-196, -120, 29, -12, -133], ![1131, 697, -166, 66, 763], ![-740, -450, 110, -47, -504], ![848, 520, -125, 51, 574]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![318535, 202190, 37190, -49673, -55339]] ![![166, 6, 3, -18, -25]]
  ![![-10880, -6892, -1273, 2821, 3004]] where
 M := ![![![-10880, -6892, -1273, 2821, 3004]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-10880, -6892, -1273, 2821, 3004]] ![![166, 6, 3, -18, -25]]
  ![![5136727, 3086937, 529095, -1799888, -1770021]] where
 M := ![![![5136727, 3086937, 529095, -1799888, -1770021]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![5136727, 3086937, 529095, -1799888, -1770021]] ![![84, 21, -5, 2, 23]]
  ![![-7060919, -4243278, -727287, 2474145, 2433083]] where
 M := ![![![-7060919, -4243278, -727287, 2474145, 2433083]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-7060919, -4243278, -727287, 2474145, 2433083]] ![![84, 21, -5, 2, 23]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![9706140, 5832932, 999750, -3401026, -3344582]]]
 hmul := by decide  
 g := ![![![![4853070, 2916466, 499875, -1700513, -1672291]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![236555, 10633, -18383, 9862, 26074]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![236555, 10633, -18383, 9862, 26074]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![236555, 10633, -18383, 9862, 26074], ![-547554, 10410, 37537, -21540, -44450], ![933450, -163501, -43124, 31362, 9590], ![186326, 90385, -26221, 10783, 57778], ![-178884, -91771, 25889, -10536, -57739]]]
  hmulB := by decide  
  f := ![![![16769, 4029, -1067, 460, 4754]], ![![-33278, -8470, 1901, -754, -8946]], ![![187866, 46089, -11518, 4620, 52066]], ![![-113976, -29001, 6517, -2867, -30930]], ![![142648, 35749, -8403, 3374, 38877]]]
  g := ![![![72277, 10633, -18383, 9862, 26074], ![-168158, 10410, 37537, -21540, -44450], ![290242, -163501, -43124, 31362, 9590], ![54920, 90385, -26221, 10783, 57778], ![-52604, -91771, 25889, -10536, -57739]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46125871, -8545104, 4511068, -2160924, -8022988]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-46125871, -8545104, 4511068, -2160924, -8022988]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-46125871, -8545104, 4511068, -2160924, -8022988], ![168482748, 23730877, -15406316, 7618092, 25907980], ![-544067580, -56900848, 46925417, -23875068, -74702572], ![108183600, 2522400, -8072016, 4424141, 10861648], ![-112666560, -2985352, 8457824, -4620648, -11474499]]]
  hmulB := by decide  
  f := ![![![-2752797, -1359088, -143860, 247956, 27396]], ![![-1109371, -1487515, -487728, 538800, 1102336]], ![![-24792482, -10953040, -706991, 1631988, -1248092]], ![![-3252144, -5590688, -1992240, 2153861, 4659760]], ![![-6552480, -436920, 937088, -716472, -3183947]]]
  g := ![![![-15534301, -8545104, 4511068, -2160924, -8022988], ![58521501, 23730877, -15406316, 7618092, 25907980], ![-193672522, -56900848, 46925417, -23875068, -74702572], ![40601744, 2522400, -8072016, 4424141, 10861648], ![-42198952, -2985352, 8457824, -4620648, -11474499]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![236555, 10633, -18383, 9862, 26074]] ![![236555, 10633, -18383, 9862, 26074]]
  ![![30149840589, 4130157544, -2740272868, 1358969226, 4583325200]] where
 M := ![![![30149840589, 4130157544, -2740272868, 1358969226, 4583325200]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![30149840589, 4130157544, -2740272868, 1358969226, 4583325200]] ![![-46125871, -8545104, 4511068, -2160924, -8022988]]
  ![![426696962352273933, -13952387885356104, -28415641650609624, 16570946133552102, 31986945972327332]] where
 M := ![![![426696962352273933, -13952387885356104, -28415641650609624, 16570946133552102, 31986945972327332]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![426696962352273933, -13952387885356104, -28415641650609624, 16570946133552102, 31986945972327332]] ![![-46125871, -8545104, 4511068, -2160924, -8022988]]
  ![![-8383630866119394204815235, -2414091952769241399792152, 943177092509773406998036, -424413120267419446829982, -1849187674186849568851368]] where
 M := ![![![-8383630866119394204815235, -2414091952769241399792152, 943177092509773406998036, -424413120267419446829982, -1849187674186849568851368]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![-8383630866119394204815235, -2414091952769241399792152, 943177092509773406998036, -424413120267419446829982, -1849187674186849568851368]] ![![-46125871, -8545104, 4511068, -2160924, -8022988]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-370755573710964357424779057463011, -34867161460290411369283660987656, 31417878530492035693348344272544, -16126020824587583960152930852290, -49131554657819997877327520765076]]]
 hmul := by decide  
 g := ![![![![-123585191236988119141593019154337, -11622387153430137123094553662552, 10472626176830678564449448090848, -5375340274862527986717643617430, -16377184885939999292442506921692]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8836, -8411, 1834, -663, -4613]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-8836, -8411, 1834, -663, -4613]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-8836, -8411, 1834, -663, -4613], ![96873, 31510, -11416, 5037, 23009], ![-483189, -103829, 49305, -23163, -90545], ![171990, 21571, -15347, 7679, 25242], ![-176022, -22427, 15757, -7872, -25993]]]
  hmulB := by decide  
  f := ![![![52396, 34961, 6896, -8967, -11081]], ![![88457, 58808, 11544, -15039, -18459]], ![![243395, 162695, 32167, -41799, -51821]], ![![235742, 156384, 30609, -39934, -48811]], ![![-57204, -37531, -7237, 9492, 11357]]]
  g := ![![![3627, -8411, 1834, -663, -4613], ![2292, 31510, -11416, 5037, 23009], ![-48386, -103829, 49305, -23163, -90545], ![27883, 21571, -15347, 7679, 25242], ![-28294, -22427, 15757, -7872, -25993]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-8836, -8411, 1834, -663, -4613]] ![![-8836, -8411, 1834, -663, -4613]]
  ![![-924932417, -291979222, 107728142, -47766522, -215657498]] where
 M := ![![![-924932417, -291979222, 107728142, -47766522, -215657498]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-924932417, -291979222, 107728142, -47766522, -215657498]] ![![-8836, -8411, 1834, -663, -4613]]
  ![![-42420153546856, -8799784919967, 4283402404032, -2021919400071, -7805818499577]] where
 M := ![![![-42420153546856, -8799784919967, 4283402404032, -2021919400071, -7805818499577]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-42420153546856, -8799784919967, 4283402404032, -2021919400071, -7805818499577]] ![![-8836, -8411, 1834, -663, -4613]]
  ![![-1521084145699430219, -233780431442711044, 141887053507261976, -69495320569376532, -242771402822038636]] where
 M := ![![![-1521084145699430219, -233780431442711044, 141887053507261976, -69495320569376532, -242771402822038636]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-1521084145699430219, -233780431442711044, 141887053507261976, -69495320569376532, -242771402822038636]] ![![-8836, -8411, 1834, -663, -4613]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-46984368038056173424480, -5359022832799581812735, 4116105945824144832490, -2078161148604076690155, -6653299851027854583265]]]
 hmul := by decide  
 g := ![![![![-9396873607611234684896, -1071804566559916362547, 823221189164828966498, -415632229720815338031, -1330659970205570916653]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11935, 7929, 1557, -2028, -2492]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![11935, 7929, 1557, -2028, -2492]] 
 ![![7, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 7]] where
  M :=![![![11935, 7929, 1557, -2028, -2492], ![52332, 34834, 6843, -8910, -10948], ![229908, 152931, 30058, -39132, -48104], ![253722, 168769, 33151, -43169, -53046], ![-63378, -42143, -8273, 10776, 13237]]]
  hmulB := by decide  
  f := ![![![-4619, -2783, -479, 1626, 1604]], ![![-4812, -2886, -493, 1680, 1648]], ![![-34608, -20831, -3580, 12162, 11984]], ![![-54282, -32599, -5581, 18997, 18666]], ![![28566, 16991, 2861, -9822, -9533]]]
  g := ![![![1705, 7929, 1557, -2028, -356], ![7476, 34834, 6843, -8910, -1564], ![32844, 152931, 30058, -39132, -6872], ![36246, 168769, 33151, -43169, -7578], ![-9054, -42143, -8273, 10776, 1891]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [4, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 6], [0, 1]]
 g := ![![[0, 2], [0, 1]], ![[0, 5], [0, 6]]]
 h' := ![![[0, 6], [0, 3], [0, 1]], ![[0, 1], [0, 4], [0, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [0, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [4, 0, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2623341, -2231762, -582150, 1740272, 2204818]
  a := ![0, 14, 13, -137, -247]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-374763, -2231762, -582150, 1740272, 314974]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5105, 1309, -287, 86, 1336]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![5105, 1309, -287, 86, 1336]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![4, 6, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![5105, 1309, -287, 86, 1336], ![-28056, -6718, 1797, -948, -8148], ![171108, 44427, -9364, 2250, 43764], ![-100814, -22253, 7329, -5397, -32578], ![123894, 30603, -7503, 3234, 34379]]]
  hmulB := by decide  
  f := ![![![4011, 10429, -1779, 544, 5096]], ![![-107016, -40618, 13443, -5778, -28056]], ![![-5268, -9167, 1688, -548, -4636]], ![![-31096, -1359, 2411, -1295, -3410]], ![![34092, 7481, -3501, 1640, 6459]]]
  g := ![![![487, 433, -287, 86, 1336], ![-2436, -2500, 1797, -948, -8148], ![16648, 14373, -9364, 2250, 43764], ![-7740, -9461, 7329, -5397, -32578], ![11240, 10803, -7503, 3234, 34379]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [1, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 6], [0, 1]]
 g := ![![[0, 1], [0, 1]], ![[0, 6], [0, 6]]]
 h' := ![![[0, 6], [0, 6], [0, 1]], ![[0, 1], [0, 1], [0, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [0, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [1, 0, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-939515550, -711733587, -166586023, 523070693, 623805422]
  a := ![3, 252, 254, -2387, -4062]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-366703384, 41111793, -166586023, 523070693, 623805422]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3237, 1188, -400, 172, 828]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![3237, 1188, -400, 172, 828]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![3237, 1188, -400, 172, 828], ![-17388, -3987, 1816, -852, -3388], ![71148, 12140, -6767, 3228, 11788], ![-20440, -1852, 1788, -991, -2856], ![21264, 2092, -1820, 936, 2873]]]
  hmulB := by decide  
  f := ![![![594251, 395140, 77584, -101044, -124068]], ![![457097, 304209, 59800, -77848, -95744]], ![![2147778, 1427772, 280241, -365028, -447988]], ![![1803928, 1200636, 236036, -307263, -377944]], ![![-279350, -186548, -36836, 47872, 59249]]]
  g := ![![![399, 1188, -400, 172, 828], ![-2503, -3987, 1816, -852, -3388], ![10862, 12140, -6767, 3228, 11788], ![-3372, -1852, 1788, -991, -2856], ![3478, 2092, -1820, 936, 2873]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![11935, 7929, 1557, -2028, -2492]] ![![5105, 1309, -287, 86, 1336]]
  ![![594251, 395140, 77584, -101044, -124068]] where
 M := ![![![594251, 395140, 77584, -101044, -124068]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![594251, 395140, 77584, -101044, -124068]] ![![3237, 1188, -400, 172, 828]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, 6, 1, 1, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![10, 6, 1, 1, 1]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![1, 7, 5, 1, 0], ![9, 10, 7, 0, 1]] where
  M :=![![![10, 6, 1, 1, 1], ![-21, -1, 3, 15, 7], ![-147, -102, -22, 153, 161], ![-616, -322, -42, 261, 224], ![48, -4, -10, -6, 17]]]
  hmulB := by decide  
  f := ![![![-234, -44, 23, -11, -41]], ![![861, 123, -79, 39, 133]], ![![-2793, -296, 242, -123, -385]], ![![-692, -59, 58, -30, -89]], ![![-1239, -114, 105, -54, -163]]]
  g := ![![![0, -1, -1, 1, 1], ![-9, -16, -11, 15, 7], ![-159, -253, -174, 153, 161], ![-263, -399, -265, 261, 224], ![-9, -12, -9, -6, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [2, 1, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2, 9], [6, 8, 2], [0, 1]]
 g := ![![[10, 1, 1], [8, 8, 1], []], ![[1, 8, 8, 1], [10, 7, 4, 4], [2, 4]], ![[1, 0, 9, 6], [5, 6, 2, 8], [9, 4]]]
 h' := ![![[2, 2, 9], [6, 9, 10], [0, 0, 1], [0, 1]], ![[6, 8, 2], [2, 9, 7], [0, 9, 8], [2, 2, 9]], ![[0, 1], [9, 4, 5], [7, 2, 2], [6, 8, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 1], []]
 b := ![[], [1, 7, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [2, 1, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![66517992052, 42258352373, 7908812504, -25977312765, -27171086598]
  a := ![1, 17, 17, -162, -279]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![30639553109, 45073673428, 29817543865, -25977312765, -27171086598]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-234, -44, 23, -11, -41]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-234, -44, 23, -11, -41]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![8, 1, 1, 0, 0], ![5, 5, 0, 1, 0], ![0, 7, 0, 0, 1]] where
  M :=![![![-234, -44, 23, -11, -41], ![861, 123, -79, 39, 133], ![-2793, -296, 242, -123, -385], ![560, 14, -42, 23, 56], ![-582, -16, 44, -24, -59]]]
  hmulB := by decide  
  f := ![![![10, 6, 1, 1, 1]], ![![-21, -1, 3, 15, 7]], ![![-8, -5, -1, 16, 16]], ![![-61, -27, -2, 31, 24]], ![![-9, -1, 1, 9, 6]]]
  g := ![![![-33, 25, 23, -11, -41], ![118, -84, -79, 39, 133], ![-374, 252, 242, -123, -385], ![71, -41, -42, 23, 56], ![-74, 43, 44, -24, -59]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [6, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 10], [0, 1]]
 g := ![![[9, 9], [0, 1], [1]], ![[7, 2], [1, 10], [1]]]
 h' := ![![[1, 10], [0, 8], [5, 1], [0, 1]], ![[0, 1], [8, 3], [6, 10], [1, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [10, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [6, 10, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-108615086, -87943122, -21969097, 66961700, 82859260]
  a := ![1, -88, -84, 851, 1501]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-24333710, -89163395, -21969097, 66961700, 82859260]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![10, 6, 1, 1, 1]] ![![-234, -44, 23, -11, -41]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![119939527, 29848299, -7161017, 2910646, 32907454]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![119939527, 29848299, -7161017, 2910646, 32907454]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![4, 11, 1, 1, 0], ![5, 6, 6, 0, 1]] where
  M :=![![![119939527, 29848299, -7161017, 2910646, 32907454], ![-691056534, -171977188, 41259687, -16770288, -189603134], ![3981665814, 990882273, -237726274, 96625530, 1092437906], ![-2611486822, -649897873, 155919405, -63374517, -716505874], ![2988615288, 743750507, -178435957, 72526548, 819977537]]]
  hmulB := by decide  
  f := ![![![-38133, -3667, 3241, -1660, -5086]], ![![106806, 6060, -8489, 4506, 12362]], ![![-259602, -469, 18532, -10380, -23450]], ![![59698, 3302, -4742, 2523, 6890]], ![![-86385, 1826, 5874, -3374, -6885]]]
  g := ![![![-4326179, -15354887, -15962799, 2910646, 32907454], ![24926176, 88470368, 91972983, -16770288, -189603134], ![-143617372, -509740461, -529921480, 96625530, 1092437906], ![94195432, 334327466, 347563782, -63374517, -716505874], ![-107798353, -382608211, -397755979, 72526548, 819977537]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [12, 1, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 3], [11, 9], [0, 1]]
 g := ![![[6, 10, 3], [4, 3], [1]], ![[5, 8, 1], [9, 9], [1]], ![[11, 8, 9], [11, 1], [1]]]
 h' := ![![[6, 3], [5, 10, 9], [1, 12, 4], [0, 1]], ![[11, 9], [12, 3, 3], [9, 11, 10], [6, 3]], ![[0, 1], [8, 0, 1], [6, 3, 12], [11, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6], []]
 b := ![[], [12, 8, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [12, 1, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![68708851363, 58609223155, 15095008460, -42774309579, -54383593810]
  a := ![-1, 17, 10, -189, -406]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![39363389133, 65802168568, 29551606223, -42774309579, -54383593810]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2586, -1725, -340, 427, 531]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-2586, -1725, -340, 427, 531]] 
 ![![13, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![-2586, -1725, -340, 427, 531], ![-11151, -7452, -1472, 1803, 2261], ![-47481, -31831, -6311, 7395, 9415], ![-50638, -34069, -6783, 7547, 9786], ![13686, 9133, 1801, -2250, -2803]]]
  hmulB := by decide  
  f := ![![![-7762, -749, 658, -337, -1041]], ![![-3095, -362, 272, -137, -443]], ![![-4747, -92, 345, -190, -478]], ![![-5084, -630, 455, -228, -739]], ![![-7500, -583, 611, -318, -949]]]
  g := ![![![103, -1725, -340, 427, 531], ![506, -7452, -1472, 1803, 2261], ![2611, -31831, -6311, 7395, 9415], ![3334, -34069, -6783, 7547, 9786], ![-561, 9133, 1801, -2250, -2803]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4375262, 1356638, -506081, 225051, 1008999]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![4375262, 1356638, -506081, 225051, 1008999]] 
 ![![13, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![4375262, 1356638, -506081, 225051, 1008999], ![-21188979, -4424699, 2143749, -1011027, -3912279], ![82157859, 12888810, -7701170, 3763251, 13231575], ![-22456056, -1939246, 1878218, -970381, -2897440], ![23137116, 2045028, -1941906, 1001538, 3006643]]]
  hmulB := by decide  
  f := ![![![-7627498, -1897288, 455815, -185727, -2093985]], ![![-2484715, -617277, 148843, -61071, -683241]], ![![-21824773, -5428852, 1304198, -531687, -5991777]], ![![9853654, 2455614, -586739, 236156, 2698175]], ![![-20492710, -5099536, 1223662, -497514, -5622941]]]
  g := ![![![-1414003, 1356638, -506081, 225051, 1008999], ![4512380, -4424699, 2143749, -1011027, -3912279], ![-12850582, 12888810, -7701170, 3763251, 13231575], ![1788449, -1939246, 1878218, -970381, -2897440], ![-1893820, 2045028, -1941906, 1001538, 3006643]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![119939527, 29848299, -7161017, 2910646, 32907454]] ![![-2586, -1725, -340, 427, 531]]
  ![![-7627498, -1897288, 455815, -185727, -2093985]] where
 M := ![![![-7627498, -1897288, 455815, -185727, -2093985]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-7627498, -1897288, 455815, -185727, -2093985]] ![![4375262, 1356638, -506081, 225051, 1008999]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![468, 363, 86, -251, -305]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![468, 363, 86, -251, -305]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![3, 10, 15, 1, 0], ![14, 0, 9, 0, 1]] where
  M :=![![![468, 363, 86, -251, -305], ![6405, 3378, 442, -1743, -1379], ![28959, 20117, 4237, -13035, -14749], ![62342, 35685, 5599, -19951, -18354], ![-10020, -3985, -91, 1344, -127]]]
  hmulB := by decide  
  f := ![![![412, 131, 8, -23, -17]], ![![357, 580, 138, -159, -203]], ![![4263, 2205, 463, -603, -805]], ![![4297, 2473, 520, -669, -878]], ![![2521, 1230, 246, -329, -432]]]
  g := ![![![323, 169, 388, -251, -305], ![1820, 1224, 2294, -1743, -1379], ![16150, 8851, 19559, -13035, -14749], ![22303, 13835, 27650, -19951, -18354], ![-722, -1025, -1124, 1344, -127]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [13, 2, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 7, 1], [2, 9, 16], [0, 1]]
 g := ![![[4, 4, 13], [14, 1], [1, 1], []], ![[0, 3, 8, 16], [7, 15], [7, 13], [15, 1]], ![[4, 3, 4, 1], [1, 13], [14, 15], [0, 1]]]
 h' := ![![[16, 7, 1], [4, 9, 8], [4, 2, 16], [0, 0, 1], [0, 1]], ![[2, 9, 16], [7, 15, 13], [9, 3, 10], [10, 11, 9], [16, 7, 1]], ![[0, 1], [3, 10, 13], [4, 12, 8], [4, 6, 7], [2, 9, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 9], []]
 b := ![[], [2, 0, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [13, 2, 16, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19979903677, 4469565472, -1444032152, 1053570444, 6432384392]
  a := ![0, 0, 12, 42, 196]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4307893479, -356831704, -4419944020, 1053570444, 6432384392]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![412, 131, 8, -23, -17]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![412, 131, 8, -23, -17]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![13, 10, 1, 0, 0], ![11, 0, 0, 1, 0], ![6, 16, 0, 0, 1]] where
  M :=![![![412, 131, 8, -23, -17], ![357, 580, 138, -159, -203], ![4263, 2205, 463, -603, -805], ![4298, 2773, 491, -669, -770], ![-1278, -769, -97, 156, 139]]]
  hmulB := by decide  
  f := ![![![468, 363, 86, -251, -305]], ![![6405, 3378, 442, -1743, -1379]], ![![5829, 3448, 575, -1984, -1912]], ![![3970, 2334, 385, -1336, -1277]], ![![5604, 3073, 441, -1650, -1413]]]
  g := ![![![39, 19, 8, -23, -17], ![90, 144, 138, -159, -203], ![571, 615, 463, -603, -805], ![582, 599, 491, -669, -770], ![-151, -119, -97, 156, 139]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [9, 8, 1] where
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
 g := ![![[16, 2], [2], [13], [1]], ![[0, 15], [2], [13], [1]]]
 h' := ![![[9, 16], [3, 11], [15, 6], [8, 9], [0, 1]], ![[0, 1], [0, 6], [1, 11], [4, 8], [9, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [7, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [9, 8, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2588959, -3722258, -1303664, 3466890, 5069556]
  a := ![13, 18, 13, -191, -387]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3187909, -4223442, -1303664, 3466890, 5069556]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![468, 363, 86, -251, -305]] ![![412, 131, 8, -23, -17]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55007, 146740, -24930, 7598, 71576]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![55007, 146740, -24930, 7598, 71576]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![2, 4, 12, 1, 0], ![2, 10, 1, 0, 1]] where
  M :=![![![55007, 146740, -24930, 7598, 71576], ![-1503096, -571845, 189002, -81198, -394660], ![8287860, 1941040, -868651, 403230, 1625848], ![-3178364, -428186, 287802, -142929, -479780], ![3247530, 444118, -295052, 146346, 493333]]]
  hmulB := by decide  
  f := ![![![686349, 191136, -31682, 7162, 164704]], ![![-3458784, -771467, 247338, -125634, -1052660]], ![![22105860, 5893452, -1140509, 353322, 5609744]], ![![12629786, 3434454, -620818, 170419, 3126836]], ![![237732, 123252, 15113, -24160, -9195]]]
  g := ![![![-5439, -31548, -9878, 7598, 71576], ![-29020, 194713, 82002, -81198, -394660], ![222616, -838440, -385961, 403230, 1625848], ![-101734, 260070, 130670, -142929, -479780], ![103588, -267084, -133923, 146346, 493333]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [17, 17, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 8, 15], [3, 10, 4], [0, 1]]
 g := ![![[4, 16, 17], [12, 12, 5], [11, 1], []], ![[4, 5, 12, 2], [10, 10, 15, 8], [2, 5], [17, 16]], ![[14, 8, 3, 1], [8, 8, 17, 17], [13, 7], [9, 16]]]
 h' := ![![[8, 8, 15], [5, 0, 6], [3, 5, 9], [0, 0, 1], [0, 1]], ![[3, 10, 4], [4, 5, 3], [13, 0, 13], [3, 4, 10], [8, 8, 15]], ![[0, 1], [15, 14, 10], [14, 14, 16], [8, 15, 8], [3, 10, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 6], []]
 b := ![[], [4, 9, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [17, 17, 8, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5498184295, 3320225270, 573946424, -1967605944, -1946789562]
  a := ![-1, 8, 10, -69, -97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![701419753, 1613607614, 1375368806, -1967605944, -1946789562]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1534, -805, -104, 413, 323]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-1534, -805, -104, 413, 323]] 
 ![![19, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-1534, -805, -104, 413, 323], ![-6783, -4750, -1010, 3093, 3521], ![-73941, -40555, -5823, 21777, 18655], ![-91070, -57275, -10557, 34617, 35854], ![-1002, 2311, 1243, -2748, -4775]]]
  hmulB := by decide  
  f := ![![![-45114, 2633, 2838, -1709, -2855]], ![![-11091, -250, 826, -453, -1109]], ![![-393, 5283, -729, 179, 2365]], ![![-21598, -841, 1659, -895, -2320]], ![![-4482, 2406, -25, -91, 690]]]
  g := ![![![-31, -805, -104, 413, 323], ![-654, -4750, -1010, 3093, 3521], ![-2258, -40555, -5823, 21777, 18655], ![-5962, -57275, -10557, 34617, 35854], ![1211, 2311, 1243, -2748, -4775]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![81335, 54101, 10627, -13806, -16970]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![81335, 54101, 10627, -13806, -16970]] 
 ![![19, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![81335, 54101, 10627, -13806, -16970], ![356370, 237244, 46653, -60492, -74494], ![1564374, 1040655, 204430, -264510, -325430], ![1719858, 1145313, 225303, -290587, -358414], ![-430806, -287075, -56525, 73344, 90463]]]
  hmulB := by decide  
  f := ![![![-2737795, -22995, 198431, -110460, -256330]], ![![-1878105, -45459, 140372, -76866, -189320]], ![![-706245, 168214, 26255, -22092, 12956]], ![![-2392521, -89606, 183358, -99085, -255568]], ![![229038, 72893, -26761, 11850, 53671]]]
  g := ![![![-29209, 54101, 10627, -13806, -16970], ![-128151, 237244, 46653, -60492, -74494], ![-562689, 1040655, 204430, -264510, -325430], ![-619839, 1145313, 225303, -290587, -358414], ![154986, -287075, -56525, 73344, 90463]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![55007, 146740, -24930, 7598, 71576]] ![![-1534, -805, -104, 413, 323]]
  ![![-38040, -22799, -3856, 13219, 12943]] where
 M := ![![![-38040, -22799, -3856, 13219, 12943]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![-38040, -22799, -3856, 13219, 12943]] ![![81335, 54101, 10627, -13806, -16970]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![-92208330, -55412854, -9497625, 32309747, 31773529]]]
 hmul := by decide  
 g := ![![![![-4853070, -2916466, -499875, 1700513, 1672291]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26935, 6716, -1606, 652, 7402]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![26935, 6716, -1606, 652, 7402]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![2, 9, 4, 1, 0], ![15, 18, 7, 0, 1]] where
  M :=![![![26935, 6716, -1606, 652, 7402], ![-155442, -38729, 9276, -3768, -42686], ![896406, 223224, -53513, 21744, 246050], ![-588280, -146426, 35126, -14277, -161420], ![673236, 167570, -40198, 16338, 184729]]]
  hmulB := by decide  
  f := ![![![20493, 13632, 2678, -3488, -4286]], ![![90006, 59877, 11764, -15324, -18830]], ![![395430, 263036, 51673, -67332, -82726]], ![![124744, 82981, 16302, -21241, -26098]], ![![199419, 132656, 26061, -33954, -41719]]]
  g := ![![![-3713, -5756, -2436, 652, 7402], ![21408, 33197, 14050, -3768, -42686], ![-123384, -191364, -80993, 21744, 246050], ![80938, 125549, 53138, -14277, -161420], ![-92625, -143678, -60811, 16338, 184729]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [21, 4, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 6, 20], [12, 16, 3], [0, 1]]
 g := ![![[15, 8, 3], [22, 13, 3], [12, 19, 1], []], ![[1, 14, 7, 21], [14, 19, 12, 22], [2, 10, 12, 14], [20, 9]], ![[21, 5, 21, 4], [15, 2, 6, 4], [4, 9, 19, 16], [14, 9]]]
 h' := ![![[7, 6, 20], [21, 8, 7], [1, 13, 16], [0, 0, 1], [0, 1]], ![[12, 16, 3], [10, 18, 19], [21, 16, 10], [20, 22, 16], [7, 6, 20]], ![[0, 1], [10, 20, 20], [11, 17, 20], [11, 1, 6], [12, 16, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 14], []]
 b := ![[], [2, 12, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [21, 4, 4, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6799140, -399495047, -186499535, 430287765, 711300618]
  a := ![3, -3, 1, 39, 98]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-501012420, -742412872, -299424127, 430287765, 711300618]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20493, 13632, 2678, -3488, -4286]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![20493, 13632, 2678, -3488, -4286]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![9, 20, 1, 0, 0], ![19, 18, 0, 1, 0], ![13, 18, 0, 0, 1]] where
  M :=![![![20493, 13632, 2678, -3488, -4286], ![90006, 59877, 11764, -15324, -18830], ![395430, 263036, 51673, -67332, -82726], ![436352, 290262, 57022, -74323, -91308], ![-108876, -72430, -14230, 18534, 22775]]]
  hmulB := by decide  
  f := ![![![26935, 6716, -1606, 652, 7402]], ![![-155442, -38729, 9276, -3768, -42686]], ![![-85653, -21344, 5111, -2076, -23524]], ![![-124977, -31128, 7460, -3031, -34310]], ![![-77155, -19228, 4604, -1870, -21191]]]
  g := ![![![5147, 4348, 2678, -3488, -4286], ![22612, 19103, 11764, -15324, -18830], ![99353, 83940, 51673, -67332, -82726], ![109665, 92660, 57022, -74323, -91308], ![-27349, -23104, -14230, 18534, 22775]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [4, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 22], [0, 1]]
 g := ![![[10, 6], [18, 13], [7, 13], [1]], ![[0, 17], [4, 10], [16, 10], [1]]]
 h' := ![![[6, 22], [20, 12], [18, 6], [19, 6], [0, 1]], ![[0, 1], [0, 11], [8, 17], [9, 17], [6, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [21, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [4, 17, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1518177, -2251668, -797751, 2118775, 3117341]
  a := ![1, -14, -10, 149, 303]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3266112, -3502032, -797751, 2118775, 3117341]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![26935, 6716, -1606, 652, 7402]] ![![20493, 13632, 2678, -3488, -4286]]
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


lemma PB3811I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB3811I0 : PrimesBelowBoundCertificateInterval O 1 23 3811 where
  m := 9
  g := ![5, 5, 5, 3, 2, 3, 2, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB3811I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N2]
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
    · exact ![49, 49, 7]
    · exact ![1331, 121]
    · exact ![2197, 13, 13]
    · exact ![4913, 289]
    · exact ![6859, 19, 19]
    · exact ![12167, 529]
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
      exact NI7N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N0, I7N1, I7N2, I11N0, I11N1, I13N0, I13N1, I13N2, I17N1, I19N1, I19N2, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [I11N0, I11N1], [I13N0, I13N1, I13N2], [I17N1], [I19N1, I19N2], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
