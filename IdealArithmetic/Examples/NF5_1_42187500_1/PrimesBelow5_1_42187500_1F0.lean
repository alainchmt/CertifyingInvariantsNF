
import IdealArithmetic.Examples.NF5_1_42187500_1.RI5_1_42187500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18012, 4578, 6909, 290, -16156]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-18012, 4578, 6909, 290, -16156]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-18012, 4578, 6909, 290, -16156], ![-32022, -27549, -45630, 47580, 84260], ![216100, -40972, -60249, -21880, 149660], ![154731, 177470, 292459, -288399, -547560], ![-72882, -81440, -134262, 133004, 251099]]]
  hmulB := by decide  
  f := ![![![7559, 6342, 917, 4386, 7376]], ![![9569, 5733, 1077, 4506, 7876]], ![![20258, 14016, 2325, 8932, 14692]], ![![18153, 14476, 2170, 9903, 16612]], ![![7419, 4286, 819, 2790, 4635]]]
  g := ![![![-9151, 4578, 6909, 290, -16156], ![-39801, -27549, -45630, 47580, 84260], ![118990, -40972, -60249, -21880, 149660], ![221565, 177470, 292459, -288399, -547560], ![-102943, -81440, -134262, 133004, 251099]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16, 226, 7, -61, -212]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![16, 226, 7, -61, -212]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![16, 226, 7, -61, -212], ![-485, -128, -44, 133, 328], ![789, -334, 58, -79, -44], ![159, 505, 26, -162, -528], ![185, -422, 5, 69, 301]]]
  hmulB := by decide  
  f := ![![![-58, -11, -19, 34, 28]], ![![16, -47, -75, 55, 148]], ![![277, 70, 123, -192, -200]], ![![-370, 232, 367, -178, -772]], ![![125, -116, -184, 108, 377]]]
  g := ![![![28, 226, 7, -61, -212], ![-387, -128, -44, 133, 328], ![594, -334, 58, -79, -44], ![159, 505, 26, -162, -528], ![116, -422, 5, 69, 301]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![130, -75, -116, 59, 229]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![130, -75, -116, 59, 229]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![130, -75, -116, 59, 229], ![517, 184, 258, -395, -437], ![-1269, 733, 1243, -585, -2555], ![-3106, -1090, -1840, 2533, 3096], ![1419, 477, 836, -1153, -1380]]]
  hmulB := by decide  
  f := ![![![-929542067, -639895785, -107171698, -445867117, -753486653]], ![![-1441191245, -992114543, -166162370, -691286396, -1168229396]], ![![-2516096010, -1732077857, -290093683, -1206878649, -2039547029]], ![![-1666566142, -1147262386, -192147004, -799390439, -1350918252]], ![![-1130437306, -778191857, -130333946, -542229169, -916332302]]]
  g := ![![![46, -75, -116, 59, 229], ![256, 184, 258, -395, -437], ![-345, 733, 1243, -585, -2555], ![-1636, -1090, -1840, 2533, 3096], ![743, 477, 836, -1153, -1380]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2

def I2N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77, 43, -4, 4, -7]] i)))

def SI2N3: IdealEqSpanCertificate' Table ![![-77, 43, -4, 4, -7]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-77, 43, -4, 4, -7], ![-10, -92, -2, 26, 83], ![192, 45, 1, -40, -103], ![-118, 111, -11, -9, -24], ![146, -47, 13, -16, -33]]]
  hmulB := by decide  
  f := ![![![594292, 409110, 68519, 285060, 481733]], ![![921409, 634297, 106234, 441966, 746894]], ![![1608637, 1107384, 185468, 771604, 1303961]], ![![1065500, 733489, 122847, 511081, 863694]], ![![425586, 292973, 49068, 204138, 344980]]]
  g := ![![![-58, 43, -4, 4, -7], ![42, -92, -2, 26, 83], ![73, 45, 1, -40, -103], ![-109, 111, -11, -9, -24], ![90, -47, 13, -16, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N3 : Nat.card (O ⧸ I2N3) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N3)

lemma isPrimeI2N3 : Ideal.IsPrime I2N3 := prime_ideal_of_norm_prime hp2.out _ NI2N3
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-18012, 4578, 6909, 290, -16156]] ![![16, 226, 7, -61, -212]]
  ![![-71, -20, -34, 51, 56]] where
 M := ![![![-71, -20, -34, 51, 56]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-71, -20, -34, 51, 56]] ![![16, 226, 7, -61, -212]]
  ![![207, -7, 17, -41, -84]] where
 M := ![![![207, -7, 17, -41, -84]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![207, -7, 17, -41, -84]] ![![130, -75, -116, 59, 229]]
  ![![9868, 270, 529, -1968, -3989]] where
 M := ![![![9868, 270, 529, -1968, -3989]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![9868, 270, 529, -1968, -3989]] ![![-77, 43, -4, 4, -7]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-1011138, 392324, -69692, 106868, 77716]]]
 hmul := by decide  
 g := ![![![![-505569, 196162, -34846, 53434, 38858]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N2, I2N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![281, 48, 86, -162, -126]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![281, 48, 86, -162, -126]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 1, 0, 1, 0], ![1, 1, 0, 0, 1]] where
  M :=![![![281, 48, 86, -162, -126], ![-414, 403, 642, -386, -1314], ![-3014, -700, -1223, 1982, 1938], ![3136, -2342, -3710, 1987, 7704], ![-1422, 1084, 1718, -930, -3563]]]
  hmulB := by decide  
  f := ![![![-117, 308, -2, -46, -210]], ![![-466, -283, -46, 186, 498]], ![![355, 36, 31, -68, -156]], ![![-190, 149, -12, 17, -18]], ![![-27, -157, -6, 58, 181]]]
  g := ![![![107, 112, 86, -162, -126], ![86, 701, 642, -386, -1314], ![-1243, -1540, -1223, 1982, 1938], ![-286, -4011, -3710, 1987, 7704], ![141, 1859, 1718, -930, -3563]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2], [0, 1]]
 g := ![![[2, 1]], ![[1, 2]]]
 h' := ![![[2, 2], [0, 1]], ![[0, 1], [2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1000, -4987, -8717, 7418, 17892]
  a := ![-5, 3, 27, -28, -60]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2725, -10099, -8717, 7418, 17892]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-652145, -449068, -75200, -313242, -529520]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-652145, -449068, -75200, -313242, -529520]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-652145, -449068, -75200, -313242, -529520], ![-1372282, -943623, -158176, -657570, -1111304], ![-2880178, -1984192, -332115, -1381594, -2334320], ![-2338976, -1610698, -269706, -1122995, -1898112], ![-935462, -644168, -107850, -448090, -756877]]]
  hmulB := by decide  
  f := ![![![77701, 154384, 252772, -230894, -481584]], ![![-346220, 129517, 200180, -49182, -441992]], ![![-85324, -489116, -796183, 675010, 1540592]], ![![2475128, -47854, -6198, -806371, 379984]], ![![-1113159, 77916, 94302, 288284, -349429]]]
  g := ![![![308637, -449068, -75200, -313242, -529520], ![647540, -943623, -158176, -657570, -1111304], ![1362252, -1984192, -332115, -1381594, -2334320], ![1106648, -1610698, -269706, -1122995, -1898112], ![441817, -644168, -107850, -448090, -756877]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![281, 48, 86, -162, -126]] ![![-652145, -449068, -75200, -313242, -529520]]
  ![![-35265, -24280, -4066, -16916, -28586]] where
 M := ![![![-35265, -24280, -4066, -16916, -28586]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-35265, -24280, -4066, -16916, -28586]] ![![-652145, -449068, -75200, -313242, -529520]]
  ![![134334938881, 92476027948, 15488167666, 64435524094, 108891877554]] where
 M := ![![![134334938881, 92476027948, 15488167666, 64435524094, 108891877554]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![134334938881, 92476027948, 15488167666, 64435524094, 108891877554]] ![![-652145, -449068, -75200, -313242, -529520]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-511695085036719321, -352250360398687068, -58995964860442902, -245441298934181556, -414779955261637818]]]
 hmul := by decide  
 g := ![![![![-170565028345573107, -117416786799562356, -19665321620147634, -81813766311393852, -138259985087212606]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, -1, -1, 6, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-15, -1, -1, 6, 0]] 
 ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-15, -1, -1, 6, 0], ![6, -22, -37, 28, 72], ![172, 13, 26, -78, -24], ![-66, 137, 223, -159, -444], ![28, -63, -103, 74, 205]]]
  hmulB := by decide  
  f := ![![![4623, 3183, 533, 2216, 3744]], ![![3790, 2610, 437, 1818, 3072]], ![![5005, 3444, 577, 2400, 4056]], ![![6089, 4192, 702, 2919, 4932]], ![![5022, 3457, 579, 2408, 4069]]]
  g := ![![![-6, -1, -1, 6, 0], ![-57, -22, -37, 28, 72], ![90, 13, 26, -78, -24], ![338, 137, 223, -159, -444], ![-157, -63, -103, 74, 205]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-15, -1, -1, 6, 0]] ![![-15, -1, -1, 6, 0]]
  ![![-349, 846, 1364, -994, -2712]] where
 M := ![![![-349, 846, 1364, -994, -2712]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-349, 846, 1364, -994, -2712]] ![![-15, -1, -1, 6, 0]]
  ![![234587, 34147, 62185, -127440, -86448]] where
 M := ![![![234587, 34147, 62185, -127440, -86448]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![234587, 34147, 62185, -127440, -86448]] ![![-15, -1, -1, 6, 0]]
  ![![13372393, -12190472, -19396192, 11379016, 39827664]] where
 M := ![![![13372393, -12190472, -19396192, 11379016, 39827664]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![13372393, -12190472, -19396192, 11379016, 39827664]] ![![-15, -1, -1, 6, 0]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-3245714215, -947550145, -1631354745, 2389787710, 2700182640]]]
 hmul := by decide  
 g := ![![![![-649142843, -189510029, -326270949, 477957542, 540036528]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, -9, 1, -10, -18]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-15, -9, 1, -10, -18]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![2, 4, 5, 6, 1]] where
  M :=![![![-15, -9, 1, -10, -18], ![-46, -22, -3, -12, -30], ![-72, -67, -40, -6, 6], ![26, -39, -5, -55, -36], ![-60, -15, -3, 2, -23]]]
  hmulB := by decide  
  f := ![![![-35, -3, -3, 8, 18]], ![![44, -28, 3, -2, 6]], ![![10, 55, 2, -16, -54]], ![![-84, 1, -7, 17, 36]], ![![-42, 26, -3, 2, -5]]]
  g := ![![![3, 9, 13, 14, -18], ![2, 14, 21, 24, -30], ![-12, -13, -10, -6, 6], ![14, 15, 25, 23, -36], ![-2, 11, 16, 20, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [4, 3, 5, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 5, 1, 3], [5, 6, 1, 4], [1, 2, 5], [0, 1]]
 g := ![![[2, 6, 5, 1], []], ![[3, 1, 3, 6], [2, 1, 6, 0, 1, 6]], ![[3, 5, 6, 4, 3, 1], [1, 5, 5, 0, 4, 1]], ![[2, 3, 1, 4, 3], [4, 5, 6]]]
 h' := ![![[6, 5, 1, 3], [0, 0, 0, 1], [0, 1]], ![[5, 6, 1, 4], [5, 5, 3], [6, 5, 1, 3]], ![[1, 2, 5], [2, 0, 1, 3], [5, 6, 1, 4]], ![[0, 1], [6, 2, 3, 3], [1, 2, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [4, 4, 6], []]
 b := ![[], [], [4, 3, 6, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [4, 3, 5, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-124489231236, -75399592560, -127384294199, 145438546963, 231069546831]
  a := ![6, -68, -31, -33, 69]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-83804046414, -142811111412, -183247432622, -177282676289, 231069546831]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, 3, 3, -8, -18]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![35, 3, 3, -8, -18]] 
 ![![7, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![35, 3, 3, -8, -18], ![-44, 28, -3, 2, -6], ![-10, -55, -2, 16, 54], ![84, -1, 7, -17, -36], ![-54, -19, -5, 16, 41]]]
  hmulB := by decide  
  f := ![![![15, 9, -1, 10, 18]], ![![13, 7, 0, 6, 12]], ![![21, 16, 5, 8, 12]], ![![7, 12, 0, 15, 18]], ![![15, 6, 0, 4, 11]]]
  g := ![![![15, 3, 3, -8, -18], ![-15, 28, -3, 2, -6], ![-11, -55, -2, 16, 54], ![35, -1, 7, -17, -36], ![-25, -19, -5, 16, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-15, -9, 1, -10, -18]] ![![35, 3, 3, -8, -18]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-315, -723, -1181, 1064, 2256]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-315, -723, -1181, 1064, 2256]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![7, 1, 6, 1, 0], ![3, 6, 3, 0, 1]] where
  M :=![![![-315, -723, -1181, 1064, 2256], ![5576, -304, -339, -1554, 1488], ![1422, 8279, 13484, -11424, -26088], ![-34588, 273, -551, 11789, -4068], ![15918, -189, 153, -5344, 2071]]]
  hmulB := by decide  
  f := ![![![6545141, 4505667, 754623, 3139462, 5305488]], ![![13750438, 9465790, 1585359, 6595580, 11146104]], ![![28887788, 19886321, 3330622, 13856410, 23416440]], ![![23305689, 16043610, 2687033, 11178881, 18891588]], ![![18015969, 12402175, 2077154, 8641598, 14603743]]]
  g := ![![![-1321, -1393, -1303, 1064, 2256], ![1090, -698, 411, -1554, 1488], ![14514, 16021, 14572, -11424, -26088], ![-9537, 1172, -5371, 11789, -4068], ![4283, -661, 2364, -5344, 2071]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [2, 0, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 8, 2], [7, 2, 9], [0, 1]]
 g := ![![[10, 6, 1], [4, 9, 1], []], ![[2, 10, 0, 2], [0, 5, 10, 8], [2, 4]], ![[3, 5], [0, 1, 8, 4], [6, 4]]]
 h' := ![![[2, 8, 2], [3, 4, 1], [0, 0, 1], [0, 1]], ![[7, 2, 9], [0, 1, 10], [0, 2, 2], [2, 8, 2]], ![[0, 1], [2, 6], [4, 9, 8], [7, 2, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 5], []]
 b := ![[], [2, 10, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [2, 0, 2, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![90601, -7814, -5788, -28703, 20999]
  a := ![-1, -2, 6, -9, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![20775, -9555, 9403, -28703, 20999]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-197, -357, -585, 540, 1112]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-197, -357, -585, 540, 1112]] 
 ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-197, -357, -585, 540, 1112], ![2764, -210, -261, -694, 920], ![1146, 4117, 6714, -5832, -12928], ![-17226, 487, 293, 5409, -3132], ![7926, -255, -185, -2448, 1539]]]
  hmulB := by decide  
  f := ![![![-1921, -1179, -221, -1150, -2104]], ![![-1011, -603, -114, -494, -872]], ![![-1126, -873, -134, -622, -1056]], ![![-811, -532, -94, -467, -836]], ![![-1684, -1107, -195, -954, -1701]]]
  g := ![![![-672, -357, -585, 540, 1112], ![-250, -210, -261, -694, 920], ![7693, 4117, 6714, -5832, -12928], ![34, 487, 293, 5409, -3132], ![-73, -255, -185, -2448, 1539]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![133, -7, 57, -68, -88]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![133, -7, 57, -68, -88]] 
 ![![11, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![133, -7, 57, -68, -88], ![-244, 170, 137, -50, -376], ![-802, -433, -658, 776, 1280], ![1790, -563, -693, 27, 1644], ![-902, 259, 317, 0, -727]]]
  hmulB := by decide  
  f := ![![![990732105, 682018943, 114226613, 475217726, 803087288]], ![![819683367, 564269171, 94505522, 393171942, 664435208]], ![![937919314, 645662673, 108137554, 449885374, 760277248]], ![![593158413, 408329630, 68388292, 284516259, 480814116]], ![![849529868, 584815471, 97946679, 407488210, 688628777]]]
  g := ![![![68, -7, 57, -68, -88], ![82, 170, 137, -50, -376], ![-581, -433, -658, 776, 1280], ![-304, -563, -693, 27, 1644], ![109, 259, 317, 0, -727]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-315, -723, -1181, 1064, 2256]] ![![-197, -357, -585, 540, 1112]]
  ![![-3737151, -4655004, -7661864, 7451742, 14392064]] where
 M := ![![![-3737151, -4655004, -7661864, 7451742, 14392064]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![-3737151, -4655004, -7661864, 7451742, 14392064]] ![![133, -7, 57, -68, -88]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![7140571273, 2084610319, 3588980439, -5257532962, -5940401808]]]
 hmul := by decide  
 g := ![![![![649142843, 189510029, 326270949, -477957542, -540036528]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [10, 8, 0, 9, 5, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 11, 6, 8, 5], [7, 8, 3, 0, 4], [9, 2, 9, 1, 11], [7, 4, 8, 4, 6], [0, 1]]
 g := ![![[8, 2, 4, 4, 9], [8, 1], []], ![[0, 10, 4, 12, 3, 11, 6, 5], [7, 3, 11, 1], [11, 8, 8, 10, 3, 7, 1, 8]], ![[11, 9, 10, 4, 9, 5, 4, 9], [1, 6, 4, 10], [1, 2, 10, 12, 11, 11, 5, 12]], ![[7, 6, 1, 7, 10, 9, 11, 7], [5, 11, 4, 10], [12, 6, 5, 2, 9, 5, 0, 5]], ![[11, 6, 5, 11, 2, 11, 8, 7], [2, 7, 0, 1], [0, 8, 7, 9, 11, 4, 2, 8]]]
 h' := ![![[11, 11, 6, 8, 5], [11, 4, 5, 6, 3], [0, 0, 0, 1], [0, 1]], ![[7, 8, 3, 0, 4], [9, 12, 2, 1, 1], [12, 3, 8, 8, 1], [11, 11, 6, 8, 5]], ![[9, 2, 9, 1, 11], [2, 9, 8, 10, 5], [8, 4, 5, 11, 6], [7, 8, 3, 0, 4]], ![[7, 4, 8, 4, 6], [6, 12, 1, 10, 9], [11, 5, 0, 2, 7], [9, 2, 9, 1, 11]], ![[0, 1], [5, 2, 10, 12, 8], [5, 1, 0, 4, 12], [7, 4, 8, 4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 3, 9, 2], [], [], []]
 b := ![[], [7, 4, 7, 1, 10], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 5
  hpos := by decide
  P := [10, 8, 0, 9, 5, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7908200033448, 863559606936, 1133348588580, 1706179771972, -3352350962259]
  a := ![8, 11, -43, 58, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-608323079496, 66427662072, 87180660660, 131244597844, -257873150943]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-226229, -155805, -26085, -108506, -183340]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-226229, -155805, -26085, -108506, -183340]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![15, 0, 2, 1, 1]] where
  M :=![![![-226229, -155805, -26085, -108506, -183340], ![-475186, -327148, -54789, -228020, -385372], ![-998764, -687327, -115144, -478934, -809380], ![-811254, -558603, -93537, -389089, -657468], ![-324108, -222955, -37363, -155438, -262725]]]
  hmulB := by decide  
  f := ![![![-887, -161, -287, 524, 428]], ![![1380, -1270, -2021, 1190, 4148]], ![![9486, 2317, 4034, -6388, -6460]], ![![-10344, 7359, 11643, -6071, -24252]], ![![1, 363, 589, -479, -1149]]]
  g := ![![![148463, -9165, 20035, 4402, -183340], ![312082, -19244, 42115, 9256, -385372], ![655408, -40431, 88448, 19438, -809380], ![532398, -32859, 71847, 15787, -657468], ![212751, -13115, 28711, 6311, -262725]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [7, 0, 14, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 7, 6, 1], [7, 14, 2, 10], [5, 12, 9, 6], [0, 1]]
 g := ![![[2, 11, 10, 1], [10, 14, 4], [1], []], ![[7, 1, 7, 10, 13, 1], [0, 15, 8], [13, 7, 9], [16, 10, 1]], ![[1, 11, 8, 5, 6, 6], [13, 7, 2], [8, 14, 1], [3, 10, 15]], ![[4, 6, 13, 10, 9, 7], [7, 7, 9], [12, 9, 4], [6, 2, 2]]]
 h' := ![![[3, 7, 6, 1], [13, 4, 11, 16], [10, 0, 3, 15], [0, 0, 1], [0, 1]], ![[7, 14, 2, 10], [8, 12, 13, 1], [12, 7, 15, 5], [16, 6, 7, 3], [3, 7, 6, 1]], ![[5, 12, 9, 6], [3, 6, 13, 2], [14, 5, 9, 11], [11, 7, 9, 16], [7, 14, 2, 10]], ![[0, 1], [3, 12, 14, 15], [1, 5, 7, 3], [0, 4, 0, 15], [5, 12, 9, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [0, 10], []]
 b := ![[], [], [5, 5, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [7, 0, 14, 2, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19439145133, -3768725019, -5562690011, -1844932535, 13749202655]
  a := ![-10, 11, 55, -47, -119]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10988170276, -221689707, -1944770313, -917302070, 13749202655]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-887, -161, -287, 524, 428]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-887, -161, -287, 524, 428]] 
 ![![17, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![-887, -161, -287, 524, 428], ![1380, -1270, -2021, 1190, 4148], ![9486, 2317, 4034, -6388, -6460], ![-10344, 7359, 11643, -6071, -24252], ![4694, -3407, -5393, 2844, 11219]]]
  hmulB := by decide  
  f := ![![![-226229, -155805, -26085, -108506, -183340]], ![![-161028, -110894, -18567, -77240, -130516]], ![![-85366, -58761, -9842, -40938, -69180]], ![![-74336, -51189, -8571, -35653, -60244]], ![![-218679, -150590, -25214, -104884, -177225]]]
  g := ![![![-363, -161, -287, 524, 428], ![-2734, -1270, -2021, 1190, 4148], ![5172, 2317, 4034, -6388, -6460], ![15806, 7359, 11643, -6071, -24252], ![-7319, -3407, -5393, 2844, 11219]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-226229, -155805, -26085, -108506, -183340]] ![![-887, -161, -287, 524, 428]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![50072073, 34469545, 5773067, 24017732, 40588424]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![50072073, 34469545, 5773067, 24017732, 40588424]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![6, 8, 17, 1, 0], ![17, 17, 13, 0, 1]] where
  M :=![![![50072073, 34469545, 5773067, 24017732, 40588424], ![105194580, 72415832, 12128425, 50457946, 85270664], ![220999274, 152135723, 25480148, 106005252, 179142032], ![179547368, 123600185, 20700941, 86122273, 145541100], ![71715482, 49368903, 8268449, 34399284, 58132559]]]
  hmulB := by decide  
  f := ![![![-183, 6047, 9807, -7910, -19160]], ![![-46230, -1626, -3973, 18384, 880]], ![![20144, -67707, -109290, 82214, 216208]], ![![13260, -58132, -93951, 72005, 185260]], ![![-34551, -42907, -70625, 68722, 132647]]]
  g := ![![![-41265133, -44614501, -48956731, 24017732, 40588424], ![-86692336, -93728896, -102851331, 50457946, 85270664], ![-182128778, -196911623, -216076608, 106005252, 179142032], ![-147967630, -159977721, -175548000, 86122273, 145541100], ![-59101775, -63898888, -70118034, 34399284, 58132559]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [16, 4, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 9, 6], [10, 9, 13], [0, 1]]
 g := ![![[2, 12, 1], [0, 18, 6], [16, 1], []], ![[4, 14, 11, 16], [18, 15, 16, 5], [16, 5], [0, 17]], ![[12, 2, 5, 14], [3, 2, 14, 10], [11, 5], [12, 17]]]
 h' := ![![[6, 9, 6], [0, 2, 18], [10, 15, 5], [0, 0, 1], [0, 1]], ![[10, 9, 13], [14, 11, 3], [14, 18, 2], [17, 7, 9], [6, 9, 6]], ![[0, 1], [17, 6, 17], [4, 5, 12], [3, 12, 9], [10, 9, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 13], []]
 b := ![[], [13, 9, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [16, 4, 3, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4668324, 8820780, 14405812, -13266804, -27393120]
  a := ![6, -16, -32, 10, 72]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![28944852, 30559908, 31371160, -13266804, -27393120]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-183, 6047, 9807, -7910, -19160]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-183, 6047, 9807, -7910, -19160]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![11, 4, 1, 0, 0], ![16, 17, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![-183, 6047, 9807, -7910, -19160], ![-46230, -1626, -3973, 18384, 880], ![20144, -67707, -109290, 82214, 216208], ![280430, 23237, 45803, -129155, -47676], ![-129320, -10199, -20283, 58878, 20349]]]
  hmulB := by decide  
  f := ![![![50072073, 34469545, 5773067, 24017732, 40588424]], ![![105194580, 72415832, 12128425, 50457946, 85270664]], ![![62766863, 43208634, 7236715, 30106952, 50878808]], ![![145737284, 100325371, 16802802, 69904793, 118134588]], ![![43305083, 29811162, 4992866, 20771856, 35103101]]]
  g := ![![![16100, 5331, 9807, -7910, -19160], ![-16309, -15698, -3973, 18384, 880], ![-175590, -54115, -109290, 82214, 216208], ![134643, 107140, 45803, -129155, -47676], ![-60710, -48947, -20283, 58878, 20349]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [13, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 18], [0, 1]]
 g := ![![[5, 16], [], [7], [1]], ![[10, 3], [], [7], [1]]]
 h' := ![![[11, 18], [0, 4], [2], [6, 11], [0, 1]], ![[0, 1], [6, 15], [2], [13, 8], [11, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [12, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [13, 8, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21859, 1416, -3213, 13310, 5941]
  a := ![6, 7, -26, 44, 59]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15189, -11158, -3213, 13310, 5941]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![50072073, 34469545, 5773067, 24017732, 40588424]] ![![-183, 6047, 9807, -7910, -19160]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 5 2 4 [17, 19, 6, 15, 19, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 7, 17, 15, 11], [19, 20, 16, 3, 10], [14, 6, 18, 7, 8], [15, 12, 18, 21, 17], [0, 1]]
 g := ![![[8, 12, 9, 4, 1], [14, 15, 12, 13, 16], [1], []], ![[17, 18, 16, 22, 2, 12, 17, 17], [18, 13, 17, 8, 11, 6, 14, 15], [22, 11, 15, 9, 7, 2, 6, 5], [5, 16, 9, 6]], ![[22, 18, 8, 15, 11, 10, 22, 5], [3, 20, 7, 18, 9, 20, 11, 11], [3, 18, 17, 21, 22, 13, 2, 15], [19, 2, 0, 8]], ![[4, 17, 17, 1, 6, 10, 20, 18], [22, 4, 10, 20, 4, 13, 13, 16], [3, 22, 6, 13, 13, 3, 8, 12], [2, 21, 0, 18]], ![[18, 11, 3, 17, 2, 6, 3, 20], [19, 20, 2, 0, 17, 0, 6, 11], [8, 7, 15, 17, 13, 4, 0, 14], [17, 12, 7, 13]]]
 h' := ![![[2, 7, 17, 15, 11], [15, 21, 4, 0, 1], [6, 4, 17, 8, 4], [0, 0, 1], [0, 1]], ![[19, 20, 16, 3, 10], [19, 11, 14, 18, 9], [6, 0, 0, 9, 19], [11, 6, 21, 15, 17], [2, 7, 17, 15, 11]], ![[14, 6, 18, 7, 8], [15, 18, 2, 20, 9], [15, 12, 9, 5, 13], [15, 20, 5, 22, 6], [19, 20, 16, 3, 10]], ![[15, 12, 18, 21, 17], [1, 19, 0, 7, 13], [9, 4, 11, 15, 5], [1, 3, 14, 19, 6], [14, 6, 18, 7, 8]], ![[0, 1], [18, 0, 3, 1, 14], [9, 3, 9, 9, 5], [5, 17, 5, 13, 17], [15, 12, 18, 21, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 16, 2, 15], [], [], []]
 b := ![[], [16, 18, 5, 2, 7], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 5
  hpos := by decide
  P := [17, 19, 6, 15, 19, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23274541271, 1331549281, 1488859345, 6420051732, -6364071434]
  a := ![2, -7, -11, 4, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1011936577, 57893447, 64733015, 279132684, -276698758]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 6436343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀



lemma PB405I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB405I0 : PrimesBelowBoundCertificateInterval O 1 23 405 where
  m := 9
  g := ![5, 4, 5, 2, 3, 1, 2, 2, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB405I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N3]
    · exact ![I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
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
    · exact ![2401, 7]
    · exact ![1331, 11, 11]
    · exact ![371293]
    · exact ![83521, 17]
    · exact ![6859, 361]
    · exact ![6436343]
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
      exact NI2N3
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
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N2
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
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
  β := ![I2N0, I2N1, I2N2, I2N3, I3N0, I3N1, I5N0, I7N1, I11N1, I11N2, I17N1, I19N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N3], [I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [I11N1, I11N2], [], [I17N1], [I19N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
