
import IdealArithmetic.Examples.NF5_3_3037500000_1.RI5_3_3037500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1391392, -980839, -261644, -29256, 53550]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-1391392, -980839, -261644, -29256, 53550]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-1391392, -980839, -261644, -29256, 53550], ![2915994, 2054126, 547817, 60930, -112062], ![-6102480, -4293453, -1144540, -126090, 233922], ![665273, 463560, 123167, 12577, -24986], ![-3369007, -2357647, -627344, -66199, 127749]]]
  hmulB := by decide  
  f := ![![![-469967, -519298, -158623, -11322, 29712]], ![![811419, 700706, 161980, -20994, -26178]], ![![-1460784, -770703, -11284, 139368, -15810]], ![![-762390, -1067273, -385760, -64905, 77036]], ![![1331131, 1881019, 683568, 116959, -136757]]]
  g := ![![![-681068, -980839, -261644, -29256, 53550], ![1427532, 2054126, 547817, 60930, -112062], ![-2988195, -4293453, -1144540, -126090, 233922], ![326348, 463560, 123167, 12577, -24986], ![-1651404, -2357647, -627344, -66199, 127749]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2349, 3666, 1236, 2152, 389]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2349, 3666, 1236, 2152, 389]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2349, 3666, 1236, 2152, 389], ![23547, 36788, 12406, 21627, 3915], ![236952, 370050, 124781, 217428, 39339], ![385072, 601452, 202816, 353457, 63962], ![1860449, 2905725, 979830, 1707497, 308970]]]
  hmulB := by decide  
  f := ![![![-57259, -40419, -10790, -1217, 2210]], ![![31537, 22271, 5944, 668, -1217]], ![![-155063, -109464, -29207, -3280, 5980]], ![![14159, 9969, 2650, 292, -542]], ![![-99370, -70071, -18678, -2091, 3824]]]
  g := ![![![-1471, 3666, 1236, 2152, 389], ![-14781, 36788, 12406, 21627, 3915], ![-148609, 370050, 124781, 217428, 39339], ![-241579, 601452, 202816, 353457, 63962], ![-1167038, 2905725, 979830, 1707497, 308970]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28038, 13034, -788, -3039, 529]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![28038, 13034, -788, -3039, 529]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![28038, 13034, -788, -3039, 529], ![26056, 67465, 30885, 8632, -6607], ![-354753, -403242, -126163, -10875, 23871], ![203977, 158362, 30561, -8958, -4300], ![-416113, -309339, -54508, 21115, 7013]]]
  hmulB := by decide  
  f := ![![![660659, 639948, 186509, 59855, -45078]], ![![-879388, -850514, -247791, -79327, 59855]], ![![4752745, 4596246, 1339053, 428614, -323442]], ![![-2086971, -2016677, -587427, -187792, 141849]], ![![6896480, 6664897, 1941429, 620758, -468823]]]
  g := ![![![7896, 13034, -788, -3039, 529], ![-36147, 67465, 30885, 8632, -6607], ![87326, -403242, -126163, -10875, 23871], ![7527, 158362, 30561, -8958, -4300], ![-26133, -309339, -54508, 21115, 7013]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-1391392, -980839, -261644, -29256, 53550]] ![![2349, 3666, 1236, 2152, 389]]
  ![![112689, 183634, 62494, 114089, 21739]] where
 M := ![![![112689, 183634, 62494, 114089, 21739]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![112689, 183634, 62494, 114089, 21739]] ![![2349, 3666, 1236, 2152, 389]]
  ![![103773594766, 162081163169, 54655109816, 95246737634, 17235274045]] where
 M := ![![![103773594766, 162081163169, 54655109816, 95246737634, 17235274045]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![103773594766, 162081163169, 54655109816, 95246737634, 17235274045]] ![![28038, 13034, -788, -3039, 529]]
  ![![48878708457, 76342342410, 25743270763, 44862466737, 8118042752]] where
 M := ![![![48878708457, 76342342410, 25743270763, 44862466737, 8118042752]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![48878708457, 76342342410, 25743270763, 44862466737, 8118042752]] ![![28038, 13034, -788, -3039, 529]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![23022515860, 35958249408, 12125419806, 21130813106, 3823705132]]]
 hmul := by decide  
 g := ![![![![11511257930, 17979124704, 6062709903, 10565406553, 1911852566]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![159140, 58856, -13111, -20379, 4942]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![159140, 58856, -13111, -20379, 4942]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![159140, 58856, -13111, -20379, 4942], ![251431, 510225, 217611, 54157, -45700], ![-2459343, -2706036, -823532, -56877, 154014], ![1276600, 951082, 168400, -64351, -21778], ![-2578612, -1827318, -286586, 149392, 31963]]]
  hmulB := by decide  
  f := ![![![-2944562, -2843734, -828227, -264527, 199952]], ![![3577611, 3455655, 1006483, 321541, -243002]], ![![-13043569, -12600098, -3669942, -1172623, 886084]], ![![6138194, 5930046, 1727238, 551951, -417054]], ![![-22256172, -21500618, -6262412, -2001198, 1512023]]]
  g := ![![![49752, 58856, -13111, -20379, 4942], ![114277, 510225, 217611, 54157, -45700], ![-922457, -2706036, -823532, -56877, 154014], ![440052, 951082, 168400, -64351, -21778], ![-880846, -1827318, -286586, 149392, 31963]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![890, 1184, 415, 63, -82]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![890, 1184, 415, 63, -82]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![890, 1184, 415, 63, -82], ![-4447, -4343, -1175, 11, 208], ![11451, 8460, 1470, -591, -186], ![420, 2366, 1228, 405, -270], ![-2152, -6158, -2886, -828, 623]]]
  hmulB := by decide  
  f := ![![![-388848, -375702, -109433, -34977, 26424]], ![![472781, 456783, 133049, 42523, -32126]], ![![-1724407, -1666026, -485268, -155089, 117172]], ![![552606, 533870, 155500, 49693, -37546]], ![![-2813380, -2718096, -791705, -253019, 191163]]]
  g := ![![![282, 1184, 415, 63, -82], ![-1559, -4343, -1175, 11, 208], ![4273, 8460, 1470, -591, -186], ![-40, 2366, 1228, 405, -270], ![-373, -6158, -2886, -828, 623]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![159140, 58856, -13111, -20379, 4942]] ![![159140, 58856, -13111, -20379, 4942]]
  ![![33608876705, 46462278802, 16670424916, 2739768972, -3320751866]] where
 M := ![![![33608876705, 46462278802, 16670424916, 2739768972, -3320751866]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![33608876705, 46462278802, 16670424916, 2739768972, -3320751866]] ![![890, 1184, 415, 63, -82]]
  ![![22484143131944, 5970511349574, -3191842950363, -3364587847411, 998961031672]] where
 M := ![![![22484143131944, 5970511349574, -3191842950363, -3364587847411, 998961031672]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![22484143131944, 5970511349574, -3191842950363, -3364587847411, 998961031672]] ![![890, 1184, 415, 63, -82]]
  ![![-46652661244802895, -40423913563059768, -9391155987052400, 1178758013396448, 1522640854192128]] where
 M := ![![![-46652661244802895, -40423913563059768, -9391155987052400, 1178758013396448, 1522640854192128]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![-46652661244802895, -40423913563059768, -9391155987052400, 1178758013396448, 1522640854192128]] ![![890, 1184, 415, 63, -82]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![27924503146720228050, 34287645119639512488, 11385418054287354711, 1383042848886208023, -2205560196906193170]]]
 hmul := by decide  
 g := ![![![![9308167715573409350, 11429215039879837496, 3795139351429118237, 461014282962069341, -735186732302064390]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8697, 4958, 1124, 102, -238]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![8697, 4958, 1124, 102, -238]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![8697, 4958, 1124, 102, -238], ![-12988, -6733, -1808, -532, 442], ![23778, 16506, 6175, 2322, -1506], ![-6924, -9412, -3760, -953, 804], ![32636, 33136, 11432, 2292, -2391]]]
  hmulB := by decide  
  f := ![![![-1065827, -1664594, -561308, -978122, -176982]], ![![-2995088, -4677941, -1577440, -2748980, -497438]], ![![-22391026, -34971622, -11792697, -20550766, -3718698]], ![![-35440026, -55352904, -18665464, -32528117, -5886104]], ![![-169145244, -264183032, -89084680, -155246468, -28092415]]]
  g := ![![![-3167, 4958, 1124, 102, -238], ![4448, -6733, -1808, -532, 442], ![-14318, 16506, 6175, 2322, -1506], ![9534, -9412, -3760, -953, 804], ![-30044, 33136, 11432, 2292, -2391]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![8697, 4958, 1124, 102, -238]] ![![8697, 4958, 1124, 102, -238]]
  ![![29496161, 19443864, 4647728, 216664, -920128]] where
 M := ![![![29496161, 19443864, 4647728, 216664, -920128]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![29496161, 19443864, 4647728, 216664, -920128]] ![![8697, 4958, 1124, 102, -238]]
  ![![82975404025, 59513225318, 15365339316, 1141083022, -3051152894]] where
 M := ![![![82975404025, 59513225318, 15365339316, 1141083022, -3051152894]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![82975404025, 59513225318, 15365339316, 1141083022, -3051152894]] ![![8697, 4958, 1124, 102, -238]]
  ![![206558071938177, 152466922141104, 41374160978528, 4400078680112, -8370764258048]] where
 M := ![![![206558071938177, 152466922141104, 41374160978528, 4400078680112, -8370764258048]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![206558071938177, 152466922141104, 41374160978528, 4400078680112, -8370764258048]] ![![8697, 4958, 1124, 102, -238]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![496335559518355385, 361689850013118830, 99757648834579460, 12648255889175990, -20527767368778510]]]
 hmul := by decide  
 g := ![![![![99267111903671077, 72337970002623766, 19951529766915892, 2529651177835198, -4105553473755702]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2001, 2035, 575, 12, -104]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![2001, 2035, 575, 12, -104]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![5, 2, 3, 1, 0], ![2, 2, 0, 0, 1]] where
  M :=![![![2001, 2035, 575, 12, -104], ![-5708, -4490, -889, 238, 128], ![7278, 1737, -1144, -1128, 348], ![5856, 7468, 2546, 347, -498], ![-13811, -16807, -5544, -651, 1071]]]
  hmulB := by decide  
  f := ![![![97, 91, 27, 22, 0]], ![![22, 178, 69, 184, 44]], ![![2604, 3705, 1226, 1962, 324]], ![![1661, 2450, 817, 1357, 234]], ![![2473, 3837, 1292, 2235, 401]]]
  g := ![![![307, 317, 77, 12, -104], ![-1022, -746, -229, 238, 128], ![1746, 471, 320, -1128, 348], ![731, 1110, 215, 347, -498], ![-1814, -2521, -513, -651, 1071]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [1, 0, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2, 5], [4, 4, 2], [0, 1]]
 g := ![![[6, 6, 4], [1]], ![[3, 3, 6, 5], [1, 6, 5, 6]], ![[1, 0, 0, 4], [4, 3, 4, 1]]]
 h' := ![![[1, 2, 5], [6, 0, 5], [0, 1]], ![[4, 4, 2], [0, 0, 6], [1, 2, 5]], ![[0, 1], [4, 0, 3], [4, 4, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2], []]
 b := ![[], [6, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [1, 0, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2116044254, -3306441522, -1115059522, -1944169116, -352024458]
  a := ![-5, -2, 2, -8, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1186978606, 183706518, 673921118, -1944169116, -352024458]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8060, 5680, 1515, 169, -310]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![8060, 5680, 1515, 169, -310]] 
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![8060, 5680, 1515, 169, -310], ![-16881, -11885, -3169, -351, 648], ![35289, 24804, 6610, 723, -1350], ![-3814, -2646, -702, -69, 142], ![19392, 13534, 3598, 372, -731]]]
  hmulB := by decide  
  f := ![![![114, 134, 43, 5, -8]], ![![3, 21, 11, 5, -2]], ![![225, 196, 45, 4, -4]], ![![112, 158, 56, 25, -6]], ![![12, 14, -2, 72, 25]]]
  g := ![![![-3273, 5680, 1515, 169, -310], ![6844, -11885, -3169, -351, 648], ![-14267, 24804, 6610, 723, -1350], ![1508, -2646, -702, -69, 142], ![-7746, 13534, 3598, 372, -731]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![832, 1299, 438, 763, 138]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![832, 1299, 438, 763, 138]] 
 ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![832, 1299, 438, 763, 138], ![8353, 13048, 4400, 7669, 1388], ![84009, 131205, 44243, 77097, 13950], ![136548, 213274, 71918, 125333, 22680], ![659681, 1030327, 347434, 605461, 109559]]]
  hmulB := by decide  
  f := ![![![3864, 2717, 734, 93, -152]], ![![2131, 1480, 396, 49, -82]], ![![5937, 4263, 1163, 147, -240]], ![![2356, 1625, 440, 60, -92]], ![![1691, 1257, 334, 31, -67]]]
  g := ![![![-1915, 1299, 438, 763, 138], ![-19240, 13048, 4400, 7669, 1388], ![-193452, 131205, 44243, 77097, 13950], ![-314467, 213274, 71918, 125333, 22680], ![-1519170, 1030327, 347434, 605461, 109559]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![2001, 2035, 575, 12, -104]] ![![8060, 5680, 1515, 169, -310]]
  ![![3864, 2717, 734, 93, -152]] where
 M := ![![![3864, 2717, 734, 93, -152]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![3864, 2717, 734, 93, -152]] ![![832, 1299, 438, 763, 138]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7061, -5423, -1487, -266, 322]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-7061, -5423, -1487, -266, 322]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![4, 9, 1, 0, 0], ![5, 6, 0, 1, 0], ![10, 10, 0, 0, 1]] where
  M :=![![![-7061, -5423, -1487, -266, 322], ![17444, 13916, 3859, 794, -854], ![-46176, -38445, -10790, -2526, 2442], ![13242, 12104, 3480, 1009, -822], ![-48279, -43191, -12352, -3431, 2891]]]
  hmulB := by decide  
  f := ![![![47, -3, -15, -16, 2]], ![![94, 160, 69, -44, -34]], ![![-80, -87, -17, -104, -32]], ![![13, -49, -21, -133, -36]], ![![-487, -731, -232, -525, -115]]]
  g := ![![![-273, 576, -1487, -266, 322], ![598, -1549, 3859, 794, -854], ![-1346, 4491, -10790, -2526, 2442], ![227, -1550, 3480, 1009, -822], ![-966, 5423, -12352, -3431, 2891]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [1, 6, 1] where
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

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [1, 6, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-512351, -566835, -182060, -55479, 53361]
  a := ![6, -62, -1, -57, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3666, 79179, -182060, -55479, 53361]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-142, -381, -176, -49, 38]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-142, -381, -176, -49, 38]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![8, 7, 1, 0, 0], ![9, 1, 0, 1, 0], ![7, 4, 0, 0, 1]] where
  M :=![![![-142, -381, -176, -49, 38], ![2041, 2332, 732, 73, -136], ![-7407, -6507, -1549, 249, 282], ![1606, 538, -176, -87, 104], ![-1619, 1315, 1170, 1233, -69]]]
  hmulB := by decide  
  f := ![![![2029246, 1431913, 382100, 43045, -78260]], ![![-4261255, -3006994, -802412, -90415, 164350]], ![![-422362, -298045, -79533, -8962, 16290]], ![![1181827, 833903, 222520, 25059, -45574]], ![![197577, 139482, 37226, 4208, -7627]]]
  g := ![![![131, 68, -176, -49, 38], ![-320, -211, 732, 73, -136], ![70, 269, -1549, 249, 282], ![279, 131, -176, -87, 104], ![-1963, -712, 1170, 1233, -69]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 10], [0, 1]]
 g := ![![[1, 1], [1, 1], [1]], ![[0, 10], [0, 10], [1]]]
 h' := ![![[10, 10], [10, 10], [10, 10], [0, 1]], ![[0, 1], [0, 1], [0, 1], [10, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [4, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27913, 43696, 14772, 25572, 4596]
  a := ![-1, -3, 1, -5, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-32053, -9424, 14772, 25572, 4596]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1556, 1098, 293, 33, -60]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![1556, 1098, 293, 33, -60]] 
 ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![1556, 1098, 293, 33, -60], ![-3267, -2305, -615, -69, 126], ![6861, 4842, 1292, 147, -264], ![-762, -534, -142, -13, 30], ![3852, 2730, 730, 96, -145]]]
  hmulB := by decide  
  f := ![![![-14, -36, -19, -15, 6]], ![![21, 17, 3, -3, 0]], ![![-185, -216, -74, -27, 18]], ![![108, 102, 28, 5, -6]], ![![-316, -318, -96, -30, 23]]]
  g := ![![![-616, 1098, 293, 33, -60], ![1293, -2305, -615, -69, 126], ![-2717, 4842, 1292, 147, -264], ![298, -534, -142, -13, 30], ![-1538, 2730, 730, 96, -145]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-7061, -5423, -1487, -266, 322]] ![![-142, -381, -176, -49, 38]]
  ![![14, 36, 19, 15, -6]] where
 M := ![![![14, 36, 19, 15, -6]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![14, 36, 19, 15, -6]] ![![1556, 1098, 293, 33, -60]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![54397795, 38383387, 10242257, 1153460, -2097710]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![54397795, 38383387, 10242257, 1153460, -2097710]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![4, 9, 10, 1, 1]] where
  M :=![![![54397795, 38383387, 10242257, 1153460, -2097710], ![-114220590, -80594524, -21505953, -2422008, 4404630], ![239832642, 169227321, 45157124, 5085804, -9248646], ![-26821326, -18925908, -5050452, -568909, 1034394], ![134289467, 94757143, 25285676, 2847923, -5178771]]]
  hmulB := by decide  
  f := ![![![15525, 22913, 7627, 12394, 2054]], ![![125364, 200672, 68031, 121830, 22734]], ![![1372200, 2125443, 715394, 1234770, 220926]], ![![2168268, 3394920, 1145418, 2001725, 363402]], ![![2128405, 3312115, 1115965, 1936588, 348711]]]
  g := ![![![4829895, 4404829, 2401489, 250090, -2097710], ![-10141470, -9248938, -5042481, -525126, 4404630], ![21294402, 19420395, 10587968, 1102650, -9248646], ![-2381454, -2171958, -1184184, -123331, 1034394], ![11923427, 10874314, 5928722, 617438, -5178771]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 4 2 3 [12, 11, 8, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 1, 12, 6], [0, 9, 9, 11], [4, 2, 5, 9], [0, 1]]
 g := ![![[4, 3, 1, 3], [4, 8, 1], []], ![[10, 6, 11, 2, 10, 6], [12, 8, 3], [6, 9, 3, 9, 8, 8]], ![[4, 8, 3, 9, 5, 2], [6, 7, 12], [12, 9, 5, 12, 5, 5]], ![[1, 7, 9, 7, 9, 10], [0, 10, 12], [11, 1, 12, 4, 1, 1]]]
 h' := ![![[4, 1, 12, 6], [4, 3, 11, 9], [0, 0, 0, 1], [0, 1]], ![[0, 9, 9, 11], [11, 7, 11, 1], [5, 4, 2, 9], [4, 1, 12, 6]], ![[4, 2, 5, 9], [7, 5, 4, 5], [12, 7, 5, 8], [0, 9, 9, 11]], ![[0, 1], [9, 11, 0, 11], [10, 2, 6, 8], [4, 2, 5, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [12, 12, 4], []]
 b := ![[], [], [11, 10, 12, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 4
  hpos := by decide
  P := [12, 11, 8, 5, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![189302976844870, 295667174965937, 99701414837849, 173748332657092, 31440452358781]
  a := ![8, 19, -3, 26, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4887782108442, 977161825916, -16515623749997, 10946760022947, 31440452358781]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 28561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15525, 22913, 7627, 12394, 2054]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![15525, 22913, 7627, 12394, 2054]] 
 ![![13, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![15525, 22913, 7627, 12394, 2054], ![125364, 200672, 68031, 121830, 22734], ![1372200, 2125443, 715394, 1234770, 220926], ![2168268, 3394920, 1145418, 2001725, 363402], ![10588621, 16510445, 5565400, 9680173, 1747759]]]
  hmulB := by decide  
  f := ![![![54397795, 38383387, 10242257, 1153460, -2097710]], ![![41427150, 29231240, 7800087, 878424, -1597530]], ![![68662014, 48448305, 12928016, 1455948, -2647782]], ![![35596833, 25117275, 6702297, 754787, -1372692]], ![![10329959, 7289011, 1945052, 219071, -398367]]]
  g := ![![![-35577, 22913, 7627, 12394, 2054], ![-322734, 200672, 68031, 121830, 22734], ![-3371598, 2125443, 715394, 1234770, 220926], ![-5410101, 3394920, 1145418, 2001725, 363402], ![-26264852, 16510445, 5565400, 9680173, 1747759]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![54397795, 38383387, 10242257, 1153460, -2097710]] ![![15525, 22913, 7627, 12394, 2054]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-222583, -215031, -62631, -20002, 15128]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-222583, -215031, -62631, -20002, 15128]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![1, 16, 10, 5, 1]] where
  M :=![![![-222583, -215031, -62631, -20002, 15128], ![812038, 784636, 228555, 73180, -55132], ![-2959080, -2857725, -832240, -264582, 201492], ![1396894, 1351360, 393828, 128115, -94210], ![-4593413, -4429133, -1289036, -401061, 315507]]]
  hmulB := by decide  
  f := ![![![-1745, -1541, -449, -44, 88]], ![![4796, 3860, 967, -10, -176]], ![![-9690, -6207, -1058, 336, 156]], ![![-912, -2020, -846, -191, 174]], ![![-1488, -478, 109, 150, -37]]]
  g := ![![![-13983, -26887, -12583, -5626, 15128], ![51010, 98044, 45875, 20520, -55132], ![-185916, -357741, -167480, -74826, 201492], ![87712, 168160, 78584, 35245, -94210], ![-288760, -557485, -261418, -116388, 315507]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [6, 0, 16, 9, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 2, 5, 2], [4, 16], [8, 15, 12, 15], [0, 1]]
 g := ![![[12, 0, 9, 16], [5, 1, 13], [1], []], ![[2, 1, 9, 1, 15, 9], [0, 9, 4], [5, 0, 13], [11, 1, 4]], ![[7, 10, 14, 1], [13, 14, 13], [1], []], ![[10, 6, 13, 2, 8, 8], [15, 10, 4], [9, 15, 13], [11, 1, 4]]]
 h' := ![![[13, 2, 5, 2], [6, 11, 0, 13], [11, 0, 1, 8], [0, 0, 1], [0, 1]], ![[4, 16], [8, 16, 10, 8], [5, 7, 7, 2], [1, 12, 2, 8], [13, 2, 5, 2]], ![[8, 15, 12, 15], [15, 11, 3, 4], [12, 16, 12, 9], [16, 9, 1], [4, 16]], ![[0, 1], [13, 13, 4, 9], [1, 11, 14, 15], [15, 13, 13, 9], [8, 15, 12, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7], []]
 b := ![[], [], [11, 14, 13, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [6, 0, 16, 9, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![173264734594640, 270623650935348, 91256991775446, 159036618744744, 28779183214716]
  a := ![-10, 1, 5, -7, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8499150081172, -11167251794124, -11560872963042, 890629568892, 28779183214716]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1745, -1541, -449, -44, 88]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-1745, -1541, -449, -44, 88]] 
 ![![17, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-1745, -1541, -449, -44, 88], ![4796, 3860, 967, -10, -176], ![-9690, -6207, -1058, 336, 156], ![-912, -2020, -846, -191, 174], ![1173, 3825, 1640, 349, -331]]]
  hmulB := by decide  
  f := ![![![-222583, -215031, -62631, -20002, 15128]], ![![-56978, -55036, -16029, -5108, 3876]], ![![-226436, -218697, -63692, -20270, 15412]], ![![55984, 54194, 15798, 5183, -3762]], ![![-296387, -285835, -83194, -25945, 20339]]]
  g := ![![![723, -1541, -449, -44, 88], ![-1740, 3860, 967, -10, -176], ![2542, -6207, -1058, 336, 156], ![1098, -2020, -846, -191, 174], ![-2119, 3825, 1640, 349, -331]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-222583, -215031, -62631, -20002, 15128]] ![![-1745, -1541, -449, -44, 88]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, -465, -297, -118, 68]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![107, -465, -297, -118, 68]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![7, 10, 1, 1, 0], ![14, 8, 1, 0, 1]] where
  M :=![![![107, -465, -297, -118, 68], ![3622, 4588, 1557, 208, -304], ![-16512, -15723, -4132, 126, 720], ![4810, 2368, -60, -495, 74], ![-8927, -3575, 580, 1089, -243]]]
  hmulB := by decide  
  f := ![![![-3649, -2569, -685, -76, 140]], ![![7624, 5356, 1427, 154, -292]], ![![-15906, -11163, -2974, -336, 600]], ![![1917, 1342, 357, 35, -74]], ![![-777, -552, -148, -25, 27]]]
  g := ![![![-1, 9, -13, -118, 68], ![338, 260, 87, 208, -304], ![-1446, -1197, -262, 126, 720], ![381, 354, 19, -495, 74], ![-692, -659, -14, 1089, -243]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [13, 1, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 5, 13], [12, 13, 6], [0, 1]]
 g := ![![[8, 2, 6], [3, 12, 7], [3, 1], []], ![[18, 8, 18, 8], [5, 17, 15, 8], [8, 17], [10, 17]], ![[5, 18, 17, 1], [0, 7, 3, 6], [17, 6], [17, 17]]]
 h' := ![![[10, 5, 13], [18, 13, 14], [18, 3, 8], [0, 0, 1], [0, 1]], ![[12, 13, 6], [13, 17, 9], [17, 12, 10], [8, 2, 13], [10, 5, 13]], ![[0, 1], [8, 8, 15], [8, 4, 1], [18, 17, 5], [12, 13, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 7], []]
 b := ![[], [2, 11, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [13, 1, 16, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![883645563, 1418163790, 481369766, 862223066, 160879564]
  a := ![6, -10, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-389696305, -446900178, -28512256, 862223066, 160879564]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3649, -2569, -685, -76, 140]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-3649, -2569, -685, -76, 140]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![14, 13, 1, 0, 0], ![14, 0, 0, 1, 0], ![10, 4, 0, 0, 1]] where
  M :=![![![-3649, -2569, -685, -76, 140], ![7624, 5356, 1427, 154, -292], ![-15906, -11163, -2974, -336, 600], ![1632, 1084, 282, -7, -66], ![-8763, -6207, -1664, -307, 289]]]
  hmulB := by decide  
  f := ![![![107, -465, -297, -118, 68]], ![![3622, 4588, 1557, 208, -304]], ![![1688, 1969, 629, 62, -120]], ![![332, -218, -222, -113, 54]], ![![349, 533, 202, 39, -41]]]
  g := ![![![295, 304, -685, -76, 140], ![-610, -633, 1427, 154, -292], ![1286, 1321, -2974, -336, 600], ![-82, -122, 282, -7, -66], ![839, 751, -1664, -307, 289]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [18, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 18], [0, 1]]
 g := ![![[5, 7], [10, 4], [6], [1]], ![[2, 12], [11, 15], [6], [1]]]
 h' := ![![[5, 18], [10, 8], [7, 2], [1, 5], [0, 1]], ![[0, 1], [12, 11], [17, 17], [7, 14], [5, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [10, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [18, 14, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1101, 11767, 4679, 21593, 6431]
  a := ![6, 13, 4, 20, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-22801, -3936, 4679, 21593, 6431]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![107, -465, -297, -118, 68]] ![![-3649, -2569, -685, -76, 140]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24403, -17228, -4598, -520, 942]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-24403, -17228, -4598, -520, 942]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 1, 21, 14, 1]] where
  M :=![![![-24403, -17228, -4598, -520, 942], ![51290, 36221, 9668, 1094, -1982], ![-107916, -76284, -20369, -2340, 4170], ![12190, 8624, 2302, 239, -484], ![-61042, -43410, -11620, -1506, 2337]]]
  hmulB := by decide  
  f := ![![![135, 192, 70, 12, -14]], ![![-758, -761, -212, -2, 38]], ![![2088, 1608, 305, -96, -42]], ![![-22, 328, 194, 73, -44]], ![![1852, 1595, 367, -50, -59]]]
  g := ![![![-1061, -790, -1060, -596, 942], ![2230, 1661, 2230, 1254, -1982], ![-4692, -3498, -4693, -2640, 4170], ![530, 396, 542, 305, -484], ![-2654, -1989, -2639, -1488, 2337]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [19, 18, 1, 20, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 19, 17, 21], [20, 9, 14, 12], [4, 17, 15, 13], [0, 1]]
 g := ![![[12, 18, 20, 3], [7, 19, 17, 18], [3, 1], []], ![[5, 19, 19, 16, 11, 5], [11, 1, 4, 5, 18, 21], [4, 21, 5, 9, 15, 22], [18, 13, 4]], ![[14, 13, 21, 8, 19, 4], [9, 3, 20, 22, 4, 3], [5, 4, 18, 18, 13, 1], [19, 9, 6]], ![[5, 20, 20, 13, 0, 8], [22, 10, 4, 20, 6, 6], [1, 6, 5, 19, 6, 18], [15, 0, 8]]]
 h' := ![![[2, 19, 17, 21], [5, 2, 14, 16], [12, 19, 2, 8], [0, 0, 1], [0, 1]], ![[20, 9, 14, 12], [0, 19, 15, 3], [22, 9, 4, 1], [7, 11, 9, 9], [2, 19, 17, 21]], ![[4, 17, 15, 13], [18, 12, 1, 10], [11, 13, 6, 12], [16, 8, 1, 5], [20, 9, 14, 12]], ![[0, 1], [8, 13, 16, 17], [16, 5, 11, 2], [7, 4, 12, 9], [4, 17, 15, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [13, 14, 3], []]
 b := ![[], [], [13, 2, 20, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [19, 18, 1, 20, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![284721438931, 444995839250, 150077883888, 261741277948, 47406306130]
  a := ![2, -5, -1, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![12379192997, 17286501440, -36758893254, -17475956864, 47406306130]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![135, 192, 70, 12, -14]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![135, 192, 70, 12, -14]] 
 ![![23, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![135, 192, 70, 12, -14], ![-758, -761, -212, -2, 38], ![2088, 1608, 305, -96, -42], ![-22, 328, 194, 73, -44], ![-186, -914, -468, -154, 103]]]
  hmulB := by decide  
  f := ![![![-24403, -17228, -4598, -520, 942]], ![![-17929, -12657, -3378, -382, 692]], ![![-12119, -8560, -2285, -260, 468]], ![![-22812, -16104, -4298, -487, 880]], ![![-17508, -12374, -3304, -382, 675]]]
  g := ![![![-177, 192, 70, 12, -14], ![639, -761, -212, -2, 38], ![-1213, 1608, 305, -96, -42], ![-374, 328, 194, 73, -44], ![974, -914, -468, -154, 103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-24403, -17228, -4598, -520, 942]] ![![135, 192, 70, 12, -14]]
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


lemma PB2695I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB2695I0 : PrimesBelowBoundCertificateInterval O 1 23 2695 where
  m := 9
  g := ![5, 5, 5, 3, 3, 2, 2, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB2695I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
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
    · exact ![343, 7, 7]
    · exact ![121, 121, 11]
    · exact ![28561, 13]
    · exact ![83521, 17]
    · exact ![6859, 361]
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
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N0, I7N1, I7N2, I11N0, I11N1, I11N2, I13N1, I17N1, I19N1, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [I11N0, I11N1, I11N2], [I13N1], [I17N1], [I19N1], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
