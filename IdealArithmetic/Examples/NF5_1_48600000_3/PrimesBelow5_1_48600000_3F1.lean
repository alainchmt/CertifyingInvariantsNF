
import IdealArithmetic.Examples.NF5_1_48600000_3.RI5_1_48600000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![523433, 1609749, 1570097, 111414, 454014]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![523433, 1609749, 1570097, 111414, 454014]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![22, 7, 5, 12, 1]] where
  M :=![![![523433, 1609749, 1570097, 111414, 454014], ![908028, 2793503, 2725832, 193282, 788256], ![1576512, 4849308, 4731079, 335564, 1368102], ![579846, 1783857, 1740603, 123427, 503346], ![722128, 2221430, 2167440, 153710, 626773]]]
  hmulB := by decide  
  f := ![![![-47, -99, 61, 196, -132]], ![![-264, -707, 94, 522, 456]], ![![912, 2016, -1069, -3592, 2022]], ![![1566, 4503, -3, -1747, -5388]], ![![618, 1777, -3, -696, -2117]]]
  g := ![![![-326375, -54081, -24137, -184026, 454014], ![-566676, -93941, -41912, -319510, 788256], ![-983508, -163014, -72739, -554540, 1368102], ![-361854, -59985, -26763, -204025, 503346], ![-450582, -74689, -33325, -254054, 626773]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 4 2 4 [9, 19, 24, 12, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 10, 22, 6], [20, 11, 7, 5], [1, 7, 0, 18], [0, 1]]
 g := ![![[23, 17, 20, 25], [12, 18, 7], [18, 4, 17, 1], []], ![[10, 19, 0, 8, 22, 22], [22, 19, 13], [3, 26, 4, 24, 6, 23], [4, 19, 9, 8, 16, 13]], ![[15, 1, 3, 4, 13, 25], [11, 10, 13], [15, 20, 26, 4], [6, 25, 20, 23, 11, 9]], ![[20, 26, 15, 2, 13, 27], [25, 16, 22], [22, 20, 12, 16, 2, 3], [14, 26, 27, 1, 22, 3]]]
 h' := ![![[25, 10, 22, 6], [7, 21, 3, 5], [12, 28, 6, 23], [0, 0, 0, 1], [0, 1]], ![[20, 11, 7, 5], [25, 3, 13, 9], [22, 24, 16, 10], [16, 1, 14, 17], [25, 10, 22, 6]], ![[1, 7, 0, 18], [1, 0, 2, 11], [10, 28, 17, 10], [0, 14, 13], [20, 11, 7, 5]], ![[0, 1], [8, 5, 11, 4], [28, 7, 19, 15], [20, 14, 2, 11], [1, 7, 0, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [20, 3, 11], []]
 b := ![[], [], [7, 24, 19, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 4
  hpos := by decide
  P := [9, 19, 24, 12, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2686560179, 5335030873, -4206477595, -13127840400, 11069495422]
  a := ![0, -1, -4, 5, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8304908245, -2487980589, -2053584645, -5033165016, 11069495422]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 707281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47, -99, 61, 196, -132]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-47, -99, 61, 196, -132]] 
 ![![29, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-47, -99, 61, 196, -132], ![-264, -707, 94, 522, 456], ![912, 2016, -1069, -3592, 2022], ![1566, 4503, -3, -1747, -5388], ![-2548, -5456, 3294, 10774, -7135]]]
  hmulB := by decide  
  f := ![![![523433, 1609749, 1570097, 111414, 454014]], ![![410349, 1262008, 1230961, 87344, 355950]], ![![469499, 1443915, 1408390, 99934, 407256]], ![![164390, 505581, 493151, 34991, 142602]], ![![331741, 1020247, 995141, 70612, 287759]]]
  g := ![![![45, -99, 61, 196, -132], ![17, -707, 94, 522, 456], ![-775, 2016, -1069, -3592, 2022], ![436, 4503, -3, -1747, -5388], ![2461, -5456, 3294, 10774, -7135]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![523433, 1609749, 1570097, 111414, 454014]] ![![-47, -99, 61, 196, -132]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-191868509, -590209210, -575844301, -40840144, -166519865]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-191868509, -590209210, -575844301, -40840144, -166519865]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![29, 2, 1, 0, 0], ![3, 27, 0, 1, 0], ![20, 1, 0, 0, 1]] where
  M :=![![![-191868509, -590209210, -575844301, -40840144, -166519865], ![-333039730, -1024467834, -999533646, -70889124, -289040297], ![-578080594, -1778241215, -1734961183, -123047262, -501707669], ![-212667372, -654188862, -638266773, -45267283, -184570893], ![-264825510, -814633187, -794806096, -56369396, -229838176]]]
  hmulB := by decide  
  f := ![![![-759, -1538, 1039, -178, 359]], ![![718, 1036, -858, 280, -175]], ![![-675, -1377, 928, -188, 346]], ![![579, 804, -660, 233, -177]], ![![-488, -1015, 666, 4, 173]]]
  g := ![![![643888192, 59054295, -575844301, -40840144, -166519865], ![1117642236, 102504713, -999533646, -70889124, -289040297], ![1939970609, 177924674, -1734961183, -123047262, -501707669], ![713686734, 65455878, -638266773, -45267283, -184570893], ![888723322, 81509383, -794806096, -56369396, -229838176]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [1, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 30], [0, 1]]
 g := ![![[20, 1], [11, 4], [16, 16], [11, 1]], ![[0, 30], [24, 27], [6, 15], [22, 30]]]
 h' := ![![[11, 30], [20, 1], [15, 2], [20, 27], [0, 1]], ![[0, 1], [0, 30], [6, 29], [7, 4], [11, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [25, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [1, 20, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1420, -5628, 4283, 2443, 2429]
  a := ![3, -64, 1, -3, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5856, -2664, 4283, 2443, 2429]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-74982447, -230654478, -225040654, -15960378, -65076166]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-74982447, -230654478, -225040654, -15960378, -65076166]] 
 ![![31, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![-74982447, -230654478, -225040654, -15960378, -65076166], ![-130152332, -400363277, -390618966, -27703556, -112957300], ![-225914600, -694938832, -678024943, -48087020, -196067968], ![-83110668, -255657804, -249435432, -17690509, -72130530], ![-103494132, -318359642, -310611190, -22029228, -89821039]]]
  hmulB := by decide  
  f := ![![![-259769, -225390, 195874, -38198, 74758]], ![![-87353, -76299, 66140, -12922, 25242]], ![![-27709, -23414, 20555, -3978, 7846]], ![![-107039, -93474, 81034, -15831, 30928]], ![![-191749, -166600, 144708, -28234, 55231]]]
  g := ![![![156179855, -230654478, -225040654, -15960378, -65076166], ![271092411, -400363277, -390618966, -27703556, -112957300], ![470554255, -694938832, -678024943, -48087020, -196067968], ![173110009, -255657804, -249435432, -17690509, -72130530], ![215566431, -318359642, -310611190, -22029228, -89821039]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-283, -927, -93, 204, 1410]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![-283, -927, -93, 204, 1410]] 
 ![![31, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![-283, -927, -93, 204, 1410], ![2820, 6767, -2430, -9054, 2022], ![4044, 12930, 2315, 1116, -25140], ![-27162, -67293, 19035, 76061, 1674], ![-16992, -51126, -3954, 9342, 77735]]]
  hmulB := by decide  
  f := ![![![-64385034769, -198055640745, -193235229195, -13704667350, -55878827352]], ![![-51374627561, -158034158344, -154187816583, -10935338988, -44587285758]], ![![-66488763455, -204526947849, -199549033270, -14152456218, -57704622624]], ![![-52148558490, -160414857315, -156510572499, -11100073945, -45258969060]], ![![-40251539826, -123818283858, -120804711090, -8567735742, -34933721053]]]
  g := ![![![-211, -927, -93, 204, 1410], ![3179, 6767, -2430, -9054, 2022], ![2105, 12930, 2315, 1116, -25140], ![-28614, -67293, 19035, 76061, 1674], ![-11286, -51126, -3954, 9342, 77735]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2

def I31N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-237, -259, 200, -50, 101]] i)))

def SI31N3: IdealEqSpanCertificate' Table ![![-237, -259, 200, -50, 101]] 
 ![![31, 0, 0, 0, 0], ![26, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![-237, -259, 200, -50, 101], ![202, 268, -160, -106, -49], ![-98, -43, 157, 186, -367], ![-318, -945, 162, 979, 279], ![-26, -271, -246, -450, 1258]]]
  hmulB := by decide  
  f := ![![![567263533, 1744966711, 1702496534, 120744798, 492319699]], ![![507531976, 1561225694, 1523227530, 108030646, 440479557]], ![![164925464, 507329359, 494981635, 35105186, 143136391]], ![![239868330, 737862081, 719903496, 51057139, 208178205]], ![![537623918, 1653791907, 1613540804, 114435862, 466595912]]]
  g := ![![![99, -259, 200, -50, 101], ![-102, 268, -160, -106, -49], ![262, -43, 157, 186, -367], ![120, -945, 162, 979, 279], ![-688, -271, -246, -450, 1258]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N3 : Nat.card (O ⧸ I31N3) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N3)

lemma isPrimeI31N3 : Ideal.IsPrime I31N3 := prime_ideal_of_norm_prime hp31.out _ NI31N3
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-191868509, -590209210, -575844301, -40840144, -166519865]] ![![-74982447, -230654478, -225040654, -15960378, -65076166]]
  ![![241923590817122215, 744184296307383010, 726071837831513147, 51494611257567698, 209961936240475917]] where
 M := ![![![241923590817122215, 744184296307383010, 726071837831513147, 51494611257567698, 209961936240475917]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![241923590817122215, 744184296307383010, 726071837831513147, 51494611257567698, 209961936240475917]] ![![-283, -927, -93, 204, 1410]]
  ![![-6926917, -21307981, -20789378, -1474436, -6011763]] where
 M := ![![![-6926917, -21307981, -20789378, -1474436, -6011763]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N2 : IdealMulLeCertificate' Table 
  ![![-6926917, -21307981, -20789378, -1474436, -6011763]] ![![-237, -259, 200, -50, 101]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![2697, 5642, -3720, -11966, 8680]]]
 hmul := by decide  
 g := ![![![![87, 182, -120, -386, 280]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2, I31N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
    exact isPrimeI31N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1 ⊙ MulI31N2)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -3, 2, 10, -11]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![3, -3, 2, 10, -11]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![30, 7, 20, 26, 1]] where
  M :=![![![3, -3, 2, 10, -11], ![-22, -52, 10, 50, 19], ![38, 73, -61, -194, 169], ![150, 405, -48, -277, -291], ![-94, -165, 184, 550, -568]]]
  hmulB := by decide  
  f := ![![![-1, -27, -24, -2, -7]], ![![-14, -36, -44, -2, -13]], ![![-26, -79, -67, -6, -19]], ![![-6, -21, -30, -1, -9]], ![![-22, -87, -86, -6, -25]]]
  g := ![![![9, 2, 6, 8, -11], ![-16, -5, -10, -12, 19], ![-136, -30, -93, -124, 169], ![240, 66, 156, 197, -291], ![458, 103, 312, 414, -568]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 4 2 5 [5, 1, 32, 36, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 19, 6, 31], [11, 14, 26, 22], [10, 3, 5, 21], [0, 1]]
 g := ![![[4, 27, 18, 30], [22, 6, 28], [36, 2, 11, 1], [1], []], ![[4, 19, 20, 7, 12, 23], [30, 30, 9], [11, 0, 12, 26, 26, 14], [18, 24, 28], [26, 1, 36]], ![[22, 31, 0, 9, 19, 18], [29, 16, 10], [13, 12, 12, 11, 6, 22], [1], [12, 0, 3]], ![[35, 27, 36, 5, 29, 21], [23, 34, 16], [33, 22, 18, 1, 27, 34], [18, 24, 28], [10, 22, 34]]]
 h' := ![![[17, 19, 6, 31], [26, 34, 33, 20], [5, 16, 22, 18], [32, 36, 5, 1], [0, 0, 1], [0, 1]], ![[11, 14, 26, 22], [2, 0, 14, 29], [2, 8, 15, 34], [31, 35, 34, 11], [11, 23, 33, 19], [17, 19, 6, 31]], ![[10, 3, 5, 21], [24, 33, 19, 24], [13, 14, 30, 26], [16, 36, 31, 1], [24, 0, 36], [11, 14, 26, 22]], ![[0, 1], [6, 7, 8, 1], [11, 36, 7, 33], [5, 4, 4, 24], [13, 14, 4, 18], [10, 3, 5, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2, 31, 3], []]
 b := ![[], [], [16, 24, 18, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 4
  hpos := by decide
  P := [5, 1, 32, 36, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![125431059, 247668357, -198903746, -618913822, 528772959]
  a := ![1, -3, -2, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-425344803, -93344388, -291198998, -388297588, 528772959]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1874161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -27, -24, -2, -7]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-1, -27, -24, -2, -7]] 
 ![![37, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![-1, -27, -24, -2, -7], ![-14, -36, -44, -2, -13], ![-26, -79, -67, -6, -19], ![-6, -21, -30, -1, -9], ![-10, -31, -34, -2, -10]]]
  hmulB := by decide  
  f := ![![![3, -3, 2, 10, -11]], ![![2, -4, 2, 10, -9]], ![![2, 1, -1, -2, 1]], ![![6, 9, 0, -1, -15]], ![![-1, -6, 6, 20, -21]]]
  g := ![![![36, -27, -24, -2, -7], ![53, -36, -44, -2, -13], ![103, -79, -67, -6, -19], ![33, -21, -30, -1, -9], ![44, -31, -34, -2, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![3, -3, 2, 10, -11]] ![![-1, -27, -24, -2, -7]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, 77, 77, 6, 22]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![25, 77, 77, 6, 22]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![18, 26, 17, 1, 0], ![13, 2, 38, 0, 1]] where
  M :=![![![25, 77, 77, 6, 22], ![44, 135, 132, 10, 40], ![80, 244, 227, 4, 70], ![30, 93, 87, 11, 6], ![24, 82, 116, 46, 17]]]
  hmulB := by decide  
  f := ![![![189, 113, -115, 20, -44]], ![![-88, -31, 42, -6, 16]], ![![32, -8, -5, 0, -2]], ![![40, 27, -26, 5, -10]], ![![85, 27, -39, 6, -15]]]
  g := ![![![-9, -3, -21, 6, 22], ![-16, -5, -38, 10, 40], ![-22, 0, -61, 4, 70], ![-6, -5, -8, 11, 6], ![-25, -28, -32, 46, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [21, 10, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 29, 10], [9, 11, 31], [0, 1]]
 g := ![![[27, 16, 39], [12, 21], [17, 2], [0, 16, 1], []], ![[17, 31, 33, 16], [23, 9], [14, 31], [36, 0, 17, 21], [7, 18]], ![[5, 20, 18, 31], [22, 40], [36, 9], [12, 35, 22, 36], [27, 18]]]
 h' := ![![[7, 29, 10], [15, 9, 30], [12, 34, 29], [0, 33, 24], [0, 0, 1], [0, 1]], ![[9, 11, 31], [8, 26, 10], [32, 14, 3], [11, 31, 20], [25, 40, 11], [7, 29, 10]], ![[0, 1], [30, 6, 1], [0, 34, 9], [31, 18, 38], [6, 1, 29], [9, 11, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 15], []]
 b := ![[], [34, 10, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [21, 10, 25, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4944801, 10906370, -5776614, -19540410, 11240612]
  a := ![1, 19, 3, -7, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5135225, 12109166, -2456900, -19540410, 11240612]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![189, 113, -115, 20, -44]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![189, 113, -115, 20, -44]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![27, 8, 1, 0, 0], ![22, 39, 0, 1, 0], ![19, 25, 0, 0, 1]] where
  M :=![![![189, 113, -115, 20, -44], ![-88, -31, 42, -6, 16], ![32, -8, -5, 0, -2], ![-18, 15, -3, 1, 0], ![-12, 4, 2, -2, 1]]]
  hmulB := by decide  
  f := ![![![25, 77, 77, 6, 22]], ![![44, 135, 132, 10, 40]], ![![27, 83, 82, 6, 24]], ![![56, 172, 169, 13, 50]], ![![39, 120, 119, 10, 35]]]
  g := ![![![90, 33, -115, 20, -44], ![-34, -13, 42, -6, 16], ![5, 2, -5, 0, -2], ![1, 0, -3, 1, 0], ![-1, 1, 2, -2, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [31, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 40], [0, 1]]
 g := ![![[38, 4], [8], [9], [34, 39], [1]], ![[0, 37], [8], [9], [12, 2], [1]]]
 h' := ![![[11, 40], [19, 2], [29, 7], [12, 3], [10, 11], [0, 1]], ![[0, 1], [0, 39], [24, 34], [4, 38], [8, 30], [11, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [10, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [31, 30, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2740, 4848, -5295, -15625, 15951]
  a := ![-1, 0, -2, 9, -20]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4546, 6288, -5295, -15625, 15951]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![25, 77, 77, 6, 22]] ![![189, 113, -115, 20, -44]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 5 2 5 [40, 4, 1, 39, 25, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 36, 4, 22, 15], [30, 31, 30, 2, 20], [25, 16, 8, 28, 39], [12, 2, 1, 34, 12], [0, 1]]
 g := ![![[41, 5, 13, 34, 14], [22, 4, 24, 25, 10], [19, 11, 42, 23], [1], []], ![[42, 42, 12, 12, 12, 23, 30, 1], [33, 9, 28, 24, 16, 23, 8, 11], [39, 39, 25, 35], [2, 26, 34, 33, 21, 21, 19, 15], [0, 26, 23, 10]], ![[28, 2, 9, 39, 22, 3, 37, 28], [13, 13, 26, 42, 19, 40, 22, 7], [14, 31, 23, 14], [30, 31, 38, 40, 0, 13, 15, 30], [11, 28, 13, 13]], ![[19, 30, 17, 6, 19, 7, 26, 34], [38, 22, 28, 13, 19, 13, 42, 32], [1, 34, 37, 23], [12, 4, 18, 32, 5, 12, 1, 32], [19, 1, 21, 16]], ![[18, 10, 5, 4, 3, 16, 7, 19], [11, 3, 6, 30, 25, 27, 27, 19], [24, 2, 22, 10], [7, 1, 34, 25, 42, 10, 0, 2], [14, 19, 11, 15]]]
 h' := ![![[37, 36, 4, 22, 15], [23, 23, 5, 41, 33], [23, 19, 30, 41, 28], [3, 39, 42, 4, 18], [0, 0, 1], [0, 1]], ![[30, 31, 30, 2, 20], [39, 37, 18, 26, 18], [28, 5, 28, 21, 34], [13, 5, 13, 6, 32], [36, 33, 9, 22, 42], [37, 36, 4, 22, 15]], ![[25, 16, 8, 28, 39], [26, 34, 31, 36, 28], [42, 37, 33, 23, 29], [0, 4, 6, 5, 33], [30, 8, 11, 5, 18], [30, 31, 30, 2, 20]], ![[12, 2, 1, 34, 12], [29, 33, 42, 29, 23], [17, 42, 29, 26, 11], [33, 20, 28, 17, 18], [37, 39, 8, 18, 32], [25, 16, 8, 28, 39]], ![[0, 1], [19, 2, 33, 40, 27], [7, 26, 9, 18, 27], [8, 18, 40, 11, 28], [14, 6, 14, 41, 37], [12, 2, 1, 34, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 35, 30, 3], [], [], []]
 b := ![[], [37, 15, 3, 34, 17], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 5
  hpos := by decide
  P := [40, 4, 1, 39, 25, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![426353280080, 985363258832, -423860401692, -1495761035996, 578305353788]
  a := ![0, 0, -6, -6, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9915192560, 22915424624, -9857218644, -34785140372, 13448961716]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 147008443 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![349233501, 1074281717, 1048135121, 74336048, 303094636]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![349233501, 1074281717, 1048135121, 74336048, 303094636]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![24, 19, 6, 1, 1]] where
  M :=![![![349233501, 1074281717, 1048135121, 74336048, 303094636], ![606189272, 1864706681, 1819322202, 129030330, 526102780], ![1052205560, 3236703172, 3157926103, 223967064, 913193770], ![387090990, 1190735619, 1161754701, 82394197, 335950596], ![482027724, 1482771736, 1446683042, 102601942, 418344793]]]
  hmulB := by decide  
  f := ![![![-65, -121, 71, 222, -134]], ![![-268, -735, 84, 502, 532]], ![![1064, 2392, -1183, -4028, 2038]], ![![1506, 4431, 177, -1255, -6042]], ![![-38, -100, 1, 35, 123]]]
  g := ![![![-147341229, -99670561, -16392185, -4867204, 303094636], ![-255750584, -173005237, -28453074, -8448350, 526102780], ![-443924360, -300297414, -49388011, -14664398, 913193770], ![-163313262, -110475015, -18169125, -5394817, 335950596], ![-203366964, -137569773, -22625228, -6717933, 418344793]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [37, 15, 9, 18, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 8, 13, 15], [20, 5, 44, 18], [14, 33, 37, 14], [0, 1]]
 g := ![![[23, 0, 39, 2], [45, 16, 24, 36], [21, 43, 17, 8], [29, 1], []], ![[6, 29, 40, 38, 46, 30], [26, 10, 22, 19, 20, 38], [24, 22, 18, 46, 24, 29], [20, 30, 30, 20, 4, 22], [15, 6, 37]], ![[11, 38, 32, 41, 8, 32], [43, 0, 25, 30, 46, 37], [23, 9, 25, 32, 1, 17], [11, 17, 3, 19, 7, 18], [41, 29, 42]], ![[14, 7, 10, 39, 6, 4], [33, 39, 25, 10, 13, 32], [39, 46, 36, 19, 34, 32], [8, 33, 7, 4, 19, 17], [30, 46, 8]]]
 h' := ![![[42, 8, 13, 15], [27, 16, 45, 40], [22, 38, 9, 6], [8, 45, 6, 33], [0, 0, 1], [0, 1]], ![[20, 5, 44, 18], [33, 24, 34, 7], [6, 45, 37, 32], [13, 5, 40, 36], [34, 37, 32, 25], [42, 8, 13, 15]], ![[14, 33, 37, 14], [22, 23, 6, 30], [6, 13, 36, 6], [39, 36, 24, 22], [11, 16, 38, 1], [20, 5, 44, 18]], ![[0, 1], [15, 31, 9, 17], [46, 45, 12, 3], [3, 8, 24, 3], [26, 41, 23, 21], [14, 33, 37, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [13, 20, 31], []]
 b := ![[], [], [23, 45, 22, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [37, 15, 9, 18, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3061060480, 7024370409, -3130893410, -10950436669, 4576569247]
  a := ![13, -1, -2, 7, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2271842584, -1700647772, -650857636, -330361828, 4576569247]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65, -121, 71, 222, -134]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-65, -121, 71, 222, -134]] 
 ![![47, 0, 0, 0, 0], ![43, 1, 0, 0, 0], ![31, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![46, 0, 0, 0, 1]] where
  M :=![![![-65, -121, 71, 222, -134], ![-268, -735, 84, 502, 532], ![1064, 2392, -1183, -4028, 2038], ![1506, 4431, 177, -1255, -6042], ![-3024, -6614, 3668, 12202, -7297]]]
  hmulB := by decide  
  f := ![![![349233501, 1074281717, 1048135121, 74336048, 303094636]], ![![332409145, 1022528096, 997641115, 70754902, 288493024]], ![![252732853, 777434817, 758513082, 53795416, 219343138]], ![![179137479, 551047130, 537635372, 38130283, 155470792]], ![![352058910, 1082972994, 1056614864, 74937450, 305546767]]]
  g := ![![![85, -121, 71, 222, -134], ![-155, -735, 84, 502, 532], ![-1409, 2392, -1183, -4028, 2038], ![2389, 4431, 177, -1255, -6042], ![4738, -6614, 3668, 12202, -7297]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![349233501, 1074281717, 1048135121, 74336048, 303094636]] ![![-65, -121, 71, 222, -134]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 5 2 5 [40, 50, 5, 28, 44, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 37, 6, 39, 25], [18, 41, 52, 45, 17], [16, 36, 41, 37, 14], [49, 44, 7, 38, 50], [0, 1]]
 g := ![![[31, 13, 20, 14, 36], [27, 14, 35, 47], [13, 10, 11], [9, 1], []], ![[48, 24, 11, 24, 17, 42, 23, 25], [52, 5, 23, 4], [44, 1, 18, 43, 38, 42, 44, 6], [21, 40, 46, 28], [8, 45, 28, 37, 29, 4, 1, 43]], ![[22, 44, 33, 20, 14, 10, 37, 49], [15, 37, 26, 11], [29, 13, 14, 9, 16, 20, 5, 10], [19, 24, 17, 13], [18, 47, 41, 24, 3, 22, 22, 37]], ![[17, 17, 42, 42, 50, 33, 41, 23], [39, 26, 49, 44], [26, 42, 43, 25, 17, 27, 3, 45], [45, 13, 17, 16], [29, 1, 23, 37, 12, 8, 24, 41]], ![[40, 21, 33, 15, 15, 20, 35, 23], [31, 24, 21, 16], [52, 29, 48, 37, 46, 38, 3, 45], [44, 52, 7, 42], [34, 29, 5, 5, 29, 31, 41, 26]]]
 h' := ![![[32, 37, 6, 39, 25], [27, 21, 24, 17, 47], [10, 25, 34, 30, 43], [11, 40, 11, 8], [0, 0, 0, 1], [0, 1]], ![[18, 41, 52, 45, 17], [16, 17, 10, 8, 52], [20, 32, 21, 43, 51], [46, 14, 11, 41, 7], [12, 5, 7, 35, 44], [32, 37, 6, 39, 25]], ![[16, 36, 41, 37, 14], [12, 48, 22, 47, 35], [20, 49, 12, 41, 45], [28, 32, 29, 36, 12], [24, 25, 21, 21, 38], [18, 41, 52, 45, 17]], ![[49, 44, 7, 38, 50], [20, 0, 27, 37, 38], [19, 48, 31, 14, 16], [19, 38, 32, 41, 22], [21, 29, 43, 49, 49], [16, 36, 41, 37, 14]], ![[0, 1], [17, 20, 23, 50, 40], [41, 5, 8, 31, 4], [38, 35, 23, 33, 12], [7, 47, 35, 0, 28], [49, 44, 7, 38, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 48, 29, 33], [], [], []]
 b := ![[], [18, 42, 12, 40, 22], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 5
  hpos := by decide
  P := [40, 50, 5, 28, 44, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![35443774910, 82812223128, -33660578992, -120547655816, 40459761902]
  a := ![-1, -3, 1, -3, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![668750470, 1562494776, -635105264, -2274484072, 763391734]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 418195493 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-61, -95, 137, 332, -402]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-61, -95, 137, 332, -402]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![30, 7, 20, 1, 0], ![33, 0, 31, 0, 1]] where
  M :=![![![-61, -95, 137, 332, -402], ![-804, -2071, 444, 2022, 594], ![1188, 2166, -2221, -6720, 6660], ![6066, 16161, -2247, -12121, -10080], ![-2676, -4004, 6500, 18662, -22201]]]
  hmulB := by decide  
  f := ![![![1459093, 4488307, 4379051, 310574, 1266312]], ![![2532624, 7790653, 7601046, 539082, 2198034]], ![![4396068, 13522794, 13193665, 935724, 3815280]], ![![2559996, 7874822, 7683151, 544907, 2221776]], ![![3160035, 9720605, 9484008, 672628, 2742539]]]
  g := ![![![55, -41, 101, 332, -402], ![-1374, -275, -990, 2022, 594], ![-288, 834, -1259, -6720, 6660], ![11904, 1712, 9367, -12121, -10080], ![2883, -2282, 5449, 18662, -22201]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [18, 29, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 26, 50], [10, 32, 9], [0, 1]]
 g := ![![[14, 34, 19], [6, 53, 45], [47, 9], [47, 14, 36], [1]], ![[31, 41, 36, 43], [4, 28, 7, 55], [58, 27], [27, 36, 45, 44], [11, 44, 13, 38]], ![[4, 50, 33, 28], [14, 19, 51, 48], [48, 57], [17, 41, 34, 26], [38, 30, 39, 21]]]
 h' := ![![[43, 26, 50], [10, 20, 45], [26, 24, 35], [39, 7, 3], [41, 30, 53], [0, 1]], ![[10, 32, 9], [17, 23, 21], [34, 8, 19], [55, 23, 33], [13, 36, 10], [43, 26, 50]], ![[0, 1], [14, 16, 52], [48, 27, 5], [33, 29, 23], [21, 52, 55], [10, 32, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 10], []]
 b := ![[], [1, 43, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [18, 29, 6, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2353540, 5065671, -2992021, -9838066, 6372842]
  a := ![3, 0, 3, -7, 16]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1477826, 1253087, -64217, -9838066, 6372842]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3390639, -10429989, -10176137, -721714, -2942686]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-3390639, -10429989, -10176137, -721714, -2942686]] 
 ![![59, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![38, 0, 1, 0, 0], ![58, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![-3390639, -10429989, -10176137, -721714, -2942686], ![-5885372, -18104069, -17663440, -1252730, -5107828], ![-10215656, -31424512, -30659681, -2174452, -8866018], ![-3758190, -11560617, -11279247, -799949, -3261678], ![-4679912, -14395938, -14045560, -996142, -4061627]]]
  hmulB := by decide  
  f := ![![![263, -435, 189, -20, -40]], ![![119, -198, 83, 2, -20]], ![![166, -290, 121, -32, 6]], ![![292, -345, 165, -87, -68]], ![![128, -188, 106, 34, -115]]]
  g := ![![![13375710, -10429989, -10176137, -721714, -2942686], ![23217165, -18104069, -17663440, -1252730, -5107828], ![40299674, -31424512, -30659681, -2174452, -8866018], ![14825659, -11560617, -11279247, -799949, -3261678], ![18461754, -14395938, -14045560, -996142, -4061627]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-109, -68, 68, -12, 26]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-109, -68, 68, -12, 26]] 
 ![![59, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![-109, -68, 68, -12, 26], ![52, 21, -26, 4, -10], ![-20, 2, 5, 0, 2], ![12, -6, 0, -1, 0], ![8, 0, -2, 0, -1]]]
  hmulB := by decide  
  f := ![![![9, 28, 24, 4, 2]], ![![8, 25, 22, 4, 2]], ![![2, 6, 5, 0, 2]], ![![6, 18, 12, -1, 0]], ![![5, 16, 14, 4, -3]]]
  g := ![![![39, -68, 68, -12, 26], ![-10, 21, -26, 4, -10], ![-4, 2, 5, 0, 2], ![6, -6, 0, -1, 0], ![1, 0, -2, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-61, -95, 137, 332, -402]] ![![-3390639, -10429989, -10176137, -721714, -2942686]]
  ![![-9, -28, -24, -4, -2]] where
 M := ![![![-9, -28, -24, -4, -2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-9, -28, -24, -4, -2]] ![![-109, -68, 68, -12, 26]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [13, 47, 59, 46, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 34, 22, 13, 6], [19, 35, 13, 54, 12], [1, 29, 12, 38, 2], [14, 23, 14, 17, 41], [0, 1]]
 g := ![![[45, 10, 39, 50, 46], [37, 53, 31, 1], [59, 58, 39, 50, 25], [19, 59, 1], []], ![[0, 58, 53, 41, 41, 59, 13, 35], [53, 32, 16, 48], [6, 29, 44, 43, 45, 49, 19, 44], [19, 38, 55, 22, 20, 18, 41, 38], [34, 35, 25, 17, 59, 4, 57, 33]], ![[23, 1, 11, 12, 51, 53, 26, 27], [24, 19, 18, 5], [18, 21, 46, 21, 14, 14, 37, 39], [44, 60, 40, 34, 10, 40, 16, 58], [22, 9, 45, 20, 20, 22, 47, 20]], ![[55, 49, 54, 31, 36, 54, 40, 17], [53, 40, 25, 34], [26, 34, 30, 20, 21, 57, 17, 26], [10, 19, 9, 50, 41, 3, 43, 50], [14, 15, 43, 33, 33, 57, 13, 8]], ![[48, 47, 14, 51, 3, 35, 57, 49], [59, 18, 4, 27], [20, 38, 40, 26, 33, 8, 58, 12], [23, 25, 19, 15, 2, 59, 28, 58], [29, 27, 19, 30, 21, 30, 44, 52]]]
 h' := ![![[25, 34, 22, 13, 6], [12, 15, 25, 20, 31], [26, 20, 13, 47, 1], [58, 48, 58, 51, 56], [0, 0, 0, 1], [0, 1]], ![[19, 35, 13, 54, 12], [28, 1, 24, 42, 57], [31, 41, 10, 44, 29], [43, 28, 34, 56, 32], [55, 26, 22, 54, 48], [25, 34, 22, 13, 6]], ![[1, 29, 12, 38, 2], [18, 54, 18, 2, 29], [5, 27, 49, 37, 35], [43, 24, 40, 59, 54], [46, 32, 41, 42, 36], [19, 35, 13, 54, 12]], ![[14, 23, 14, 17, 41], [27, 12, 10, 38, 10], [44, 60, 60, 13, 20], [57, 56, 37, 37, 47], [2, 27, 42, 42, 5], [1, 29, 12, 38, 2]], ![[0, 1], [60, 40, 45, 20, 56], [20, 35, 51, 42, 37], [9, 27, 14, 41, 55], [49, 37, 17, 44, 33], [14, 23, 14, 17, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 0, 9, 5], [], [], []]
 b := ![[], [2, 57, 22, 41, 50], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [13, 47, 59, 46, 2, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![403599849780, 980054139239, -318157922833, -1215642966237, 145807972735]
  a := ![1, 1, 1, -5, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6616390980, 16066461299, -5215703653, -19928573217, 2390294635]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 844596301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀



lemma PB434I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB434I1 : PrimesBelowBoundCertificateInterval O 23 61 434 where
  m := 9
  g := ![2, 4, 2, 2, 1, 2, 1, 3, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB434I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1, I31N2, I31N3]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![707281, 29]
    · exact ![961, 31, 31, 31]
    · exact ![1874161, 37]
    · exact ![68921, 1681]
    · exact ![147008443]
    · exact ![4879681, 47]
    · exact ![418195493]
    · exact ![205379, 59, 59]
    · exact ![844596301]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
      exact NI31N3
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
  β := ![I29N1, I31N1, I31N2, I31N3, I37N1, I47N1, I59N1, I59N2]
  Il := ![[I29N1], [I31N1, I31N2, I31N3], [I37N1], [], [], [I47N1], [], [I59N1, I59N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
