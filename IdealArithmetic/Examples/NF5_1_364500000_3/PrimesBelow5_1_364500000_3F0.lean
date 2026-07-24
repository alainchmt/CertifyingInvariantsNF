
import IdealArithmetic.Examples.NF5_1_364500000_3.RI5_1_364500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-242, -639, 679, -176, -62]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-242, -639, 679, -176, -62]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-242, -639, 679, -176, -62], ![372, 1367, -1722, 1358, -176], ![528, 645, -192, -1722, 679], ![-2223, -5608, 5762, -871, -773], ![5166, 15779, -18267, 9802, -192]]]
  hmulB := by decide  
  f := ![![![7481311349, -2312495272, 28447116, -159216346, 445560893]], ![![-1336682679, 413172535, -5082634, 28447116, -79608173]], ![![238824519, -73821359, 908112, -5082634, 14223558]], ![![4366326340, -1349644273, 16602623, -92923619, 260043216]], ![![15247902, -4713171, 57979, -324504, 908112]]]
  g := ![![![-33, -639, 679, -176, -62], ![-493, 1367, -1722, 1358, -176], ![1125, 645, -192, -1722, 679], ![-676, -5608, 5762, -871, -773], ![-2318, 15779, -18267, 9802, -192]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![644, 1279, -676, -851, -359]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![644, 1279, -676, -851, -359]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![644, 1279, -676, -851, -359], ![2154, 5353, -181, -1352, -851], ![2553, 7369, 1774, -181, -676], ![951, 4557, 4170, 2450, 335], ![543, 7465, 11788, 8159, 1774]]]
  hmulB := by decide  
  f := ![![![-1068522398, 330283406, -4062975, 22740162, -63637479]], ![![190912437, -59011594, 725930, -4062975, 11370081]], ![![-568371442, 175685279, -2161189, 12096011, -33850227]], ![![-623622955, 192763684, -2371279, 13271867, -37140815]], ![![-536438989, 165814864, -2039768, 11416428, -31948441]]]
  g := ![![![1265, 1279, -676, -851, -359], ![2269, 5353, -181, -1352, -851], ![818, 7369, 1774, -181, -676], ![-3002, 4557, 4170, 2450, 335], ![-10589, 7465, 11788, 8159, 1774]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-832, -2282, 2483, -845, -157]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-832, -2282, 2483, -845, -157]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-832, -2282, 2483, -845, -157], ![942, 4006, -5289, 4966, -845], ![2535, 4164, -2702, -5289, 2483], ![-7920, -20709, 21868, -5185, -2222], ![15867, 51442, -61155, 38447, -2702]]]
  hmulB := by decide  
  f := ![![![707515798, -218695207, 2690275, -15057264, 42137181]], ![![-126411543, 39074179, -480670, 2690275, -7528632]], ![![376343795, -116328970, 1431019, -8009302, 22413728]], ![![59170359, -18289732, 224991, -1259256, 3523981]], ![![355199909, -109793335, 1350621, -7559320, 21154472]]]
  g := ![![![-1579, -2282, 2483, -845, -157], ![3538, 4006, -5289, 4966, -845], ![1377, 4164, -2702, -5289, 2483], ![-13783, -20709, 21868, -5185, -2222], ![39862, 51442, -61155, 38447, -2702]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-242, -639, 679, -176, -62]] ![![644, 1279, -676, -851, -359]]
  ![![191, 8604, 19021, 9913, 2715]] where
 M := ![![![191, 8604, 19021, 9913, 2715]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![191, 8604, 19021, 9913, 2715]] ![![644, 1279, -676, -851, -359]]
  ![![78118141, 251908266, 105398444, 31200585, -12111504]] where
 M := ![![![78118141, 251908266, 105398444, 31200585, -12111504]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![78118141, 251908266, 105398444, 31200585, -12111504]] ![![-832, -2282, 2483, -845, -157]]
  ![![206481632, 585133117, -188650559, 88221982, -25112517]] where
 M := ![![![206481632, 585133117, -188650559, 88221982, -25112517]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![206481632, 585133117, -188650559, 88221982, -25112517]] ![![-832, -2282, 2483, -845, -157]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-1196004893354, -2031515869950, 1392652926372, 2306134968764, -1123449661156]]]
 hmul := by decide  
 g := ![![![![-598002446677, -1015757934975, 696326463186, 1153067484382, -561724830578]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![843531, 4793558, 5153862, 3217298, 542326]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![843531, 4793558, 5153862, 3217298, 542326]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![843531, 4793558, 5153862, 3217298, 542326], ![-3253956, -2137497, 11793078, 10307724, 3217298], ![-9651894, -19860174, 8795131, 11793078, 5153862], ![-13834608, -38013598, -5883942, 3641269, 4287890], ![-35379234, -103897074, -27994434, 25194, 8795131]]]
  hmulB := by decide  
  f := ![![![-51903, 48082, -37182, 30222, -7334]], ![![14668, 6975, -2466, -24788, 10074]], ![![-30222, -69454, 69739, -2466, -12394]], ![![29848, 109226, -128958, 82133, -6270]], ![![7398, -74514, 143358, -260382, 69739]]]
  g := ![![![281177, 4793558, 5153862, 3217298, 542326], ![-1084652, -2137497, 11793078, 10307724, 3217298], ![-3217298, -19860174, 8795131, 11793078, 5153862], ![-4611536, -38013598, -5883942, 3641269, 4287890], ![-11793078, -103897074, -27994434, 25194, 8795131]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77, 27, -4, -2, -6]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-77, 27, -4, -2, -6]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-77, 27, -4, -2, -6], ![36, 9, -4, -8, -2], ![6, 31, 3, -4, -4], ![-6, 30, 15, 7, -1], ![12, 55, 46, 26, 3]]]
  hmulB := by decide  
  f := ![![![-3, 5, -14, 34, -10]], ![![19, 46, -46, 2, 8]], ![![-35, -94, 101, -30, -8]], ![![2, 52, -87, 133, -33]], ![![122, 229, -180, -174, 99]]]
  g := ![![![-28, 27, -4, -2, -6], ![17, 9, -4, -8, -2], ![-4, 31, 3, -4, -4], ![-21, 30, 15, 7, -1], ![-49, 55, 46, 26, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![843531, 4793558, 5153862, 3217298, 542326]] ![![843531, 4793558, 5153862, 3217298, 542326]]
  ![![-128328147089583, -287206454535344, 72094632961968, 124633170840872, 61007315010360]] where
 M := ![![![-128328147089583, -287206454535344, 72094632961968, 124633170840872, 61007315010360]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-128328147089583, -287206454535344, 72094632961968, 124633170840872, 61007315010360]] ![![-77, 27, -4, -2, -6]]
  ![![-41308484523597, 3279613010380131, 6554256358475252, 4724551784769510, 1114392033950522]] where
 M := ![![![-41308484523597, 3279613010380131, 6554256358475252, 4724551784769510, 1114392033950522]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-41308484523597, 3279613010380131, 6554256358475252, 4724551784769510, 1114392033950522]] ![![-77, 27, -4, -2, -6]]
  ![![145597753531642401, 434611250534380882, 128839861305266282, 9674742828205280, -33909776230437632]] where
 M := ![![![145597753531642401, 434611250534380882, 128839861305266282, 9674742828205280, -33909776230437632]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![145597753531642401, 434611250534380882, 128839861305266282, 9674742828205280, -33909776230437632]] ![![-77, 27, -4, -2, -6]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![4743051393398361303, 10261880892799116147, -3349044996525346158, -5097375938753338458, -2369572538999199474]]]
 hmul := by decide  
 g := ![![![![1581017131132787101, 3420626964266372049, -1116348332175115386, -1699125312917779486, -789857512999733158]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45053, -89380, 47490, 59664, 25136]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-45053, -89380, 47490, 59664, 25136]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-45053, -89380, 47490, 59664, 25136], ![-150816, -374603, 12936, 94980, 59664], ![-178992, -516420, -123773, 12936, 47490], ![-67062, -320256, -291906, -171263, -23364], ![-38808, -524928, -826662, -570876, -123773]]]
  hmulB := by decide  
  f := ![![![-12989400361, 4015061732, -49391202, 276438816, -773603524]], ![![-9463196060, 2925101645, -35983080, 201394572, -563595056]], ![![-5361623434, 1657293524, -20387165, 114105408, -319319650]], ![![-10826047682, 3346363072, -41165214, 230398609, -644761760]], ![![-2608469717, 806285644, -9918516, 55513140, -155351389]]]
  g := ![![![-9261, -89380, 47490, 59664, 25136], ![176428, -374603, 12936, 94980, 59664], ![407000, -516420, -123773, 12936, 47490], ![501238, -320256, -291906, -171263, -23364], ![1224301, -524928, -826662, -570876, -123773]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-45053, -89380, 47490, 59664, 25136]] ![![-45053, -89380, 47490, 59664, 25136]]
  ![![2032711753, -19318276712, -47369022036, -35130798720, -8715068252]] where
 M := ![![![2032711753, -19318276712, -47369022036, -35130798720, -8715068252]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![2032711753, -19318276712, -47369022036, -35130798720, -8715068252]] ![![-45053, -89380, 47490, 59664, 25136]]
  ![![13994757442741051, 47342943416751492, 23168944900560510, 8665493407479648, -1451580151562124]] where
 M := ![![![13994757442741051, 47342943416751492, 23168944900560510, 8665493407479648, -1451580151562124]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![13994757442741051, 47342943416751492, 23168944900560510, 8665493407479648, -1451580151562124]] ![![-45053, -89380, 47490, 59664, 25136]]
  ![![-12442427343420309640079, -32963767769431612393072, -2920193837535311770728, 4975923318178401679584, 4253940634552362974504]] where
 M := ![![![-12442427343420309640079, -32963767769431612393072, -2920193837535311770728, 4975923318178401679584, 4253940634552362974504]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-12442427343420309640079, -32963767769431612393072, -2920193837535311770728, 4975923318178401679584, 4253940634552362974504]] ![![-45053, -89380, 47490, 59664, 25136]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![5555941316676445713603358675, 11141895107666438277774275980, -5624941967507649700835887110, -7191703444172703064809329520, -3060963565810502380210230440]]]
 hmul := by decide  
 g := ![![![![1111188263335289142720671735, 2228379021533287655554855196, -1124988393501529940167177422, -1438340688834540612961865904, -612192713162100476042046088]]]]
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


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [4, 4, 0, 6, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2, 4, 1, 2], [5, 6, 4, 0, 6], [4, 5, 5, 6], [2, 0, 1, 0, 6], [0, 1]]
 g := ![![[5, 5, 1], []], ![[6, 3, 1, 3, 2, 5, 4, 1], [0, 0, 1, 2, 6, 0, 3, 1]], ![[2, 3, 2, 0, 0, 5], [0, 5, 3, 1, 6, 0, 2, 6]], ![[3, 4, 5, 1, 5, 5, 3], [2, 5, 3, 3, 6]], ![[0, 5, 3, 0, 0, 6], [2, 6, 2, 0, 6, 5, 2, 6]]]
 h' := ![![[1, 2, 4, 1, 2], [0, 0, 0, 1], [0, 1]], ![[5, 6, 4, 0, 6], [1, 6, 6, 5, 5], [1, 2, 4, 1, 2]], ![[4, 5, 5, 6], [6, 3, 3, 3], [5, 6, 4, 0, 6]], ![[2, 0, 1, 0, 6], [0, 2, 4, 4, 2], [4, 5, 5, 6]], ![[0, 1], [0, 3, 1, 1], [2, 0, 1, 0, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 1, 4], [], [], []]
 b := ![[], [5, 2, 0, 5], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [4, 4, 0, 6, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10157812, 27066130, -13485990, 2226315, 643517]
  a := ![0, -2, -1, -3, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1451116, 3866590, -1926570, 318045, 91931]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3239864831, 1001451718, -12319339, 68950404, -192955085]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-3239864831, 1001451718, -12319339, 68950404, -192955085]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![4, 2, 8, 4, 1]] where
  M :=![![![-3239864831, 1001451718, -12319339, 68950404, -192955085], ![1157730510, -357857895, 4402182, -24638678, 68950404], ![-206851212, 63938316, -786536, 4402182, -12319339], ![-541907238, 167505116, -2060561, 11532803, -32274111], ![-13206546, 4082182, -50217, 281060, -786536]]]
  hmulB := by decide  
  f := ![![![-7, -36, 7, -38, 11]], ![![-66, -165, 76, 14, -38]], ![![114, 290, -362, 76, 7]], ![![12, -94, 249, -369, 57]], ![![52, 106, -121, -38, -10]]]
  g := ![![![-224367681, 126123808, 139211031, 76433704, -192955085], ![80175354, -45068973, -49745550, -27312754, 68950404], ![-14324896, 8052454, 8888016, 4879958, -12319339], ![-37528254, 21095758, 23284757, 12784477, -32274111], ![-914582, 514114, 567461, 311564, -786536]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 4 2 3 [8, 8, 0, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 4, 10, 6], [8, 6, 6, 7], [7, 0, 6, 9], [0, 1]]
 g := ![![[5, 6, 9, 4], [8, 1], []], ![[7, 2, 0, 6], [5, 5, 9, 1, 5, 6], [2, 1, 3]], ![[4, 9, 1, 10, 6, 8], [2, 9, 9, 1, 5, 6], [1, 3, 5]], ![[1, 8, 9, 9, 3, 9], [2, 10, 8, 4, 10, 4], [1, 8, 4]]]
 h' := ![![[4, 4, 10, 6], [2, 5, 3, 9], [0, 0, 1], [0, 1]], ![[8, 6, 6, 7], [4, 8, 1], [0, 8, 9, 10], [4, 4, 10, 6]], ![[7, 0, 6, 9], [3, 7, 1, 3], [1, 9, 2, 9], [8, 6, 6, 7]], ![[0, 1], [3, 2, 6, 10], [8, 5, 10, 3], [7, 0, 6, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1, 1, 4], []]
 b := ![[], [], [6, 8, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 4
  hpos := by decide
  P := [8, 8, 0, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4205632160, 9646180139, -8160574139, -1454700276, 1404228233]
  a := ![3, -65, 1, -66, 1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-128298252, 621611243, -1763127273, -642873928, 1404228233]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 14641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -36, 7, -38, 11]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-7, -36, 7, -38, 11]] 
 ![![11, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-7, -36, 7, -38, 11], ![-66, -165, 76, 14, -38], ![114, 290, -362, 76, 7], ![12, -94, 249, -369, 57], ![-228, -304, 389, 574, -362]]]
  hmulB := by decide  
  f := ![![![-3239864831, 1001451718, -12319339, 68950404, -192955085]], ![![-1956483937, 604754921, -7439381, 41637650, -116521381]], ![![-902404155, 278935770, -3431323, 19204854, -53744054]], ![![-2405529626, 743556260, -9146843, 51194185, -143264981]], ![![-590266928, 182453238, -2244445, 12561988, -35154246]]]
  g := ![![![46, -36, 7, -38, 11], ![75, -165, 76, 14, -38], ![-132, 290, -362, 76, 7], ![251, -94, 249, -369, 57], ![-285, -304, 389, 574, -362]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-3239864831, 1001451718, -12319339, 68950404, -192955085]] ![![-7, -36, 7, -38, 11]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -4, 75, 64, 19]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-17, -4, 75, 64, 19]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![5, 4, 1, 0, 0], ![6, 0, 0, 1, 0], ![5, 10, 0, 0, 1]] where
  M :=![![![-17, -4, 75, 64, 19], ![-114, -227, 118, 150, 64], ![-192, -478, 18, 118, 75], ![-168, -536, -221, -57, 27], ![-354, -1272, -727, -324, 18]]]
  hmulB := by decide  
  f := ![![![785557, -242818, 2987, -16718, 46785]], ![![-280710, 86769, -1068, 5974, -16718]], ![![219623, -67886, 835, -4674, 13080]], ![![372672, -115194, 1417, -7931, 22195]], ![![86453, -26722, 328, -1840, 5149]]]
  g := ![![![-67, -38, 75, 64, 19], ![-148, -103, 118, 150, 64], ![-105, -100, 18, 118, 75], ![88, 6, -221, -57, 27], ![395, 112, -727, -324, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [6, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 12], [0, 1]]
 g := ![![[9, 3], [4], [11, 1]], ![[3, 10], [4], [9, 12]]]
 h' := ![![[11, 12], [3, 9], [12, 11], [0, 1]], ![[0, 1], [11, 4], [3, 2], [11, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [4, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [6, 2, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-39, -189, -133, -51, 46]
  a := ![1, -4, 0, -5, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![54, -9, -133, -51, 46]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-161, -426, -39, 66, 55]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-161, -426, -39, 66, 55]] 
 ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-161, -426, -39, 66, 55], ![-330, -1025, -368, -78, 66], ![-198, -844, -656, -368, -39], ![282, 378, -671, -617, -217], ![1104, 2022, -1453, -1710, -656]]]
  hmulB := by decide  
  f := ![![![-799719131, 247195528, -3040871, 17019524, -47628491]], ![![-101051332, 31235263, -384240, 2150562, -6018266]], ![![-680613001, 210379474, -2587979, 14484722, -40534944]], ![![-71806307, 22195540, -273038, 1528173, -4276534]], ![![-553902465, 171212876, -2106172, 11788084, -32988505]]]
  g := ![![![43, -426, -39, 66, 55], ![404, -1025, -368, -78, 66], ![725, -844, -656, -368, -39], ![729, 378, -671, -617, -217], ![1589, 2022, -1453, -1710, -656]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13705, 4235, -52, 292, -816]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![-13705, 4235, -52, 292, -816]] 
 ![![13, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-13705, 4235, -52, 292, -816], ![4896, -1517, 18, -104, 292], ![-876, 267, -5, 18, -52], ![-2292, 708, -11, 47, -137], ![-54, 19, -6, -4, -5]]]
  hmulB := by decide  
  f := ![![![59, 183, -214, 120, -4]], ![![20, 49, -50, 4, 8]], ![![-5, 10, -27, 62, -18]], ![![53, 155, -175, 81, 3]], ![![-43, -206, 282, -292, 55]]]
  g := ![![![-2297, 4235, -52, 292, -816], ![822, -1517, 18, -104, 292], ![-145, 267, -5, 18, -52], ![-383, 708, -11, 47, -137], ![-7, 19, -6, -4, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2

def I13N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3526204301, -1089960087, 13408122, -75044244, 210008468]] i)))

def SI13N3: IdealEqSpanCertificate' Table ![![3526204301, -1089960087, 13408122, -75044244, 210008468]] 
 ![![13, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![3526204301, -1089960087, 13408122, -75044244, 210008468], ![-1260050808, 389485403, -4791250, 26816244, -75044244], ![225132732, -69589199, 856061, -4791250, 13408122], ![589801038, -182309220, 2242661, -12552061, 35126497], ![14373750, -4442955, 54652, -305928, 856061]]]
  hmulB := by decide  
  f := ![![![12953, 341981, 598928, 422224, 95456]], ![![-32100, 252601, 646418, 481888, 120592]], ![![-91458, -61001, 329677, 288434, 90128]], ![![-106222, -73030, 378671, 331965, 103969]], ![![-277695, -796268, -182486, 26912, 75277]]]
  g := ![![![1280437973, -1089960087, 13408122, -75044244, 210008468], ![-457550604, 389485403, -4791250, 26816244, -75044244], ![81750376, -69589199, 856061, -4791250, 13408122], ![214168987, -182309220, 2242661, -12552061, 35126497], ![5219415, -4442955, 54652, -305928, 856061]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N3 : Nat.card (O ⧸ I13N3) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N3)

lemma isPrimeI13N3 : Ideal.IsPrime I13N3 := prime_ideal_of_norm_prime hp13.out _ NI13N3
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-17, -4, 75, 64, 19]] ![![-161, -426, -39, 66, 55]]
  ![![28231, 10652, -117616, -100388, -30476]] where
 M := ![![![28231, 10652, -117616, -100388, -30476]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![28231, 10652, -117616, -100388, -30476]] ![![-13705, 4235, -52, 292, -816]]
  ![![12953, 341981, 598928, 422224, 95456]] where
 M := ![![![12953, 341981, 598928, 422224, 95456]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N2 : IdealMulLeCertificate' Table 
  ![![12953, 341981, 598928, 422224, 95456]] ![![3526204301, -1089960087, 13408122, -75044244, 210008468]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2, I13N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
    exact isPrimeI13N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1 ⊙ MulI13N2)
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


def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [9, 8, 2, 5, 5, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1, 11, 2, 9], [7, 9, 2, 12, 4], [1, 8, 16, 13, 15], [4, 15, 5, 7, 6], [0, 1]]
 g := ![![[0, 13, 2, 6, 4], [8, 3, 12, 1], [], []], ![[3, 3, 3, 7, 2, 1, 5, 15], [2, 5, 16, 9], [1, 15, 8, 9], [12, 10, 5, 13]], ![[12, 15, 13, 7, 14, 0, 3, 13], [6, 14, 1, 13], [16, 11, 9, 13], [8, 0, 16, 16]], ![[9, 13, 3, 13, 15, 2, 12, 4], [13, 10, 3, 15], [1, 4, 4, 8], [7, 3, 13, 4]], ![[16, 5, 8, 12, 3, 13, 15, 6], [7, 10, 4, 4], [0, 9, 12, 2], [7, 1, 6, 2]]]
 h' := ![![[0, 1, 11, 2, 9], [13, 11, 5, 2, 15], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[7, 9, 2, 12, 4], [14, 1, 9, 6, 9], [10, 15, 2, 13, 3], [11, 1, 5, 6, 3], [0, 1, 11, 2, 9]], ![[1, 8, 16, 13, 15], [16, 3, 15, 11, 4], [11, 15, 5, 2, 8], [11, 11, 0, 11, 8], [7, 9, 2, 12, 4]], ![[4, 15, 5, 7, 6], [0, 16, 5, 4, 7], [10, 2, 5, 8, 7], [6, 1, 9, 16, 12], [1, 8, 16, 13, 15]], ![[0, 1], [6, 3, 0, 11, 16], [16, 2, 5, 11, 15], [4, 4, 2, 1, 11], [4, 15, 5, 7, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 2, 13, 15], [], [], []]
 b := ![[], [3, 12, 5, 12, 4], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 5
  hpos := by decide
  P := [9, 8, 2, 5, 5, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-779092218, -367785463, 2197278951, 3038380947, -202425851]
  a := ![1, 18, 1, 17, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-45828954, -21634439, 129251703, 178728291, -11907403]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-74622689, -160293190, 145325797, 49340292, -45977037]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-74622689, -160293190, 145325797, 49340292, -45977037]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![7, 11, 1, 0, 0], ![18, 16, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![-74622689, -160293190, 145325797, 49340292, -45977037], ![275862222, 760358663, -829697042, 290651594, 49340292], ![-148020876, -646969600, 861734326, -829697042, 145325797], ![-573908502, -1113266084, 909356427, 716408529, -439518667], ![2489091126, 6281258330, -6476393041, 989015812, 861734326]]]
  hmulB := by decide  
  f := ![![![-1701806777, -3115806268, 2298175135, 2615436494, 1034007535]], ![![-6204045210, -14913744667, 1493026320, 4596350270, 2615436494]], ![![-4631760749, -10938585177, 1493462007, 3703207092, 2016106806]], ![![-7036302534, -16340757478, 2804323145, 6009818355, 3152521813]], ![![-1220997553, -3347000652, -503888338, 332418956, 381018187]]]
  g := ![![![-77593743, -134122191, 145325797, 49340292, -45977037], ![16277348, 275610559, -829697042, 290651594, 49340292], ![376621149, 165742394, 861734326, -829697042, 145325797], ![-789476404, -1188353855, 909356427, 716408529, -439518667], ![1081183169, 3247227831, -6476393041, 989015812, 861734326]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [7, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 18], [0, 1]]
 g := ![![[3, 11], [2, 1], [4], [1]], ![[0, 8], [0, 18], [4], [1]]]
 h' := ![![[17, 18], [5, 12], [2, 1], [12, 17], [0, 1]], ![[0, 1], [0, 7], [0, 18], [16, 2], [17, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [8, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [7, 2, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-768, -1714, 1440, 430, -574]
  a := ![-1, 2, 1, 4, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-646, -1286, 1440, 430, -574]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 46, -46, 2, 8]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 46, -46, 2, 8]] 
 ![![19, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![19, 46, -46, 2, 8], ![-48, -147, 170, -92, 2], ![-6, 46, -91, 170, -46], ![162, 370, -354, -45, 84], ![-510, -1406, 1534, -538, -91]]]
  hmulB := by decide  
  f := ![![![-2327, 714, -34, 30, -144]], ![![-77, 27, -4, -2, -6]], ![![-1107, 348, -17, 12, -70]], ![![-1732, 542, -22, 23, -108]], ![![-1708, 550, -14, 26, -107]]]
  g := ![![![13, 46, -46, 2, 8], ![-9, -147, 170, -92, 2], ![-51, 46, -91, 170, -46], ![128, 370, -354, -45, 84], ![-216, -1406, 1534, -538, -91]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6305113, 1962442, -34709, 130676, -372453]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![-6305113, 1962442, -34709, 130676, -372453]] 
 ![![19, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-6305113, 1962442, -34709, 130676, -372453], ![2234718, -753027, 69678, -69418, 130676], ![-392028, 172128, -64938, 69678, -34709], ![-1013232, 408348, -71095, -30229, -30499], ![-209034, -454714, 476997, -72512, -64938]]]
  hmulB := by decide  
  f := ![![![149738555, 295831912, -160224879, -200011630, -83942269]], ![![81674921, 174709005, -61543231, -90554272, -41453027]], ![![63104690, 153229898, -12215004, -44620724, -26104945]], ![![98735365, 228207286, -41463706, -85846769, -44591198]], ![![31181967, 140898120, 120210382, 68502336, 8262507]]]
  g := ![![![-1064392, 1962442, -34709, 130676, -372453], ![399935, -753027, 69678, -69418, 130676], ![-105237, 172128, -64938, 69678, -34709], ![-166488, 408348, -71095, -30229, -30499], ![108338, -454714, 476997, -72512, -64938]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2

def I19N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 3, -4, 2, 0]] i)))

def SI19N3: IdealEqSpanCertificate' Table ![![1, 3, -4, 2, 0]] 
 ![![19, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![1, 3, -4, 2, 0], ![0, -3, 4, -8, 2], ![-6, -13, 11, 4, -4], ![12, 34, -37, 15, 1], ![-12, -53, 74, -70, 11]]]
  hmulB := by decide  
  f := ![![![2407, -747, 10, -50, 144]], ![![968, -301, 4, -20, 58]], ![![768, -239, 3, -16, 46]], ![![1288, -400, 5, -27, 77]], ![![254, -79, 0, -6, 15]]]
  g := ![![![-1, 3, -4, 2, 0], ![4, -3, 4, -8, 2], ![0, -13, 11, 4, -4], ![-10, 34, -37, 15, 1], ![34, -53, 74, -70, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N3 : Nat.card (O ⧸ I19N3) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N3)

lemma isPrimeI19N3 : Ideal.IsPrime I19N3 := prime_ideal_of_norm_prime hp19.out _ NI19N3
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-74622689, -160293190, 145325797, 49340292, -45977037]] ![![19, 46, -46, 2, 8]]
  ![![36845703421, 109715063960, -125037084259, 61818446358, 725940341]] where
 M := ![![![36845703421, 109715063960, -125037084259, 61818446358, 725940341]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![36845703421, 109715063960, -125037084259, 61818446358, 725940341]] ![![-6305113, 1962442, -34709, 130676, -372453]]
  ![![-904231516890691, -6919889097846880, 10436795805190300, -13435034327693860, 3021203169984378]] where
 M := ![![![-904231516890691, -6919889097846880, 10436795805190300, -13435034327693860, 3021203169984378]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N2 : IdealMulLeCertificate' Table 
  ![![-904231516890691, -6919889097846880, 10436795805190300, -13435034327693860, 3021203169984378]] ![![1, 3, -4, 2, 0]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![-260999856320171347, -734546307875368607, 811407428236785336, -317711903844559502, -35788760874320662]]]
 hmul := by decide  
 g := ![![![![-13736834543166913, -38660331993440453, 42705654117725544, -16721679149713658, -1883618993385298]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2, I19N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
    exact isPrimeI19N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1 ⊙ MulI19N2)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-30475, -26001, -9443, 131440, -47157]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-30475, -26001, -9443, 131440, -47157]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![16, 8, 2, 1, 0], ![5, 9, 7, 0, 1]] where
  M :=![![![-30475, -26001, -9443, 131440, -47157], ![282942, 667437, -655012, -18886, 131440], ![-394320, -1171835, 1334080, -655012, -9443], ![-113142, 206984, -564038, 1343523, -393226], ![1965036, 4049375, -3527735, -1783088, 1334080]]]
  hmulB := by decide  
  f := ![![![119257, 286215, -29579, -88982, -50421]], ![![302526, 845993, 157202, -59158, -88982]], ![![266946, 897229, 430662, 157202, -29579]], ![![208682, 577804, 97296, -48797, -63246]], ![![205045, 648090, 251226, 63676, -36058]]]
  g := ![![![-82510, -28396, 2512, 131440, -47157], ![-3134, -15845, -66840, -18886, 131440], ![440569, 180576, 117835, -655012, -9443], ![-854060, -304442, -21674, 1343523, -393226], ![1035828, 274233, -404353, -1783088, 1334080]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [22, 22, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 1, 12], [13, 21, 11], [0, 1]]
 g := ![![[3, 15, 12], [12, 1, 6], [4, 16, 1], []], ![[11, 8, 8, 2], [7, 6, 8, 6], [12, 14, 2, 2], [5, 6]], ![[11, 8, 22, 20], [7, 20, 11, 21], [0, 11, 7, 11], [6, 6]]]
 h' := ![![[3, 1, 12], [12, 6, 14], [4, 20, 12], [0, 0, 1], [0, 1]], ![[13, 21, 11], [19, 14, 21], [2, 17, 9], [14, 17, 21], [3, 1, 12]], ![[0, 1], [10, 3, 11], [18, 9, 2], [14, 6, 1], [13, 21, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 19], []]
 b := ![[], [14, 20, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [22, 22, 7, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-172226, -619428, 814788, -606672, 89252]
  a := ![0, -10, 2, -20, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![395142, 149160, 61016, -606672, 89252]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6079, -15638, -522, 3080, 2230]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-6079, -15638, -522, 3080, 2230]] 
 ![![23, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-6079, -15638, -522, 3080, 2230], ![-13380, -40051, -12056, -1044, 3080], ![-9240, -35818, -24129, -12056, -522], ![8256, 7256, -26372, -23607, -7568], ![36168, 59586, -61690, -64800, -24129]]]
  hmulB := by decide  
  f := ![![![-1988033, 614594, -7634, 42304, -118386]], ![![-487734, 150769, -1860, 10372, -29044]], ![![-437699, 135320, -1691, 9328, -26068]], ![![-446627, 138102, -1738, 9497, -26590]], ![![-1815555, 561148, -6852, 38600, -108123]]]
  g := ![![![1223, -15638, -522, 3080, 2230], ![9902, -40051, -12056, -1044, 3080], ![17285, -35818, -24129, -12056, -522], ![16241, 7256, -26372, -23607, -7568], ![35557, 59586, -61690, -64800, -24129]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-330643, 102197, -1257, 7038, -19691]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![-330643, 102197, -1257, 7038, -19691]] 
 ![![23, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-330643, 102197, -1257, 7038, -19691], ![118146, -36535, 446, -2514, 7038], ![-21114, 6511, -88, 446, -1257], ![-55302, 17094, -220, 1169, -3296], ![-1338, 429, -29, 6, -88]]]
  hmulB := by decide  
  f := ![![![-1511, -4887, 5803, -3628, 249]], ![![-919, -2738, 3121, -1546, -17]], ![![-775, -2966, 3777, -3156, 458]], ![![-1250, -3876, 4510, -2531, 86]], ![![17, 1360, -2340, 3720, -941]]]
  g := ![![![-67556, 102197, -1257, 7038, -19691], ![24151, -36535, 446, -2514, 7038], ![-4298, 6511, -88, 446, -1257], ![-11288, 17094, -220, 1169, -3296], ![-252, 429, -29, 6, -88]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-30475, -26001, -9443, 131440, -47157]] ![![-6079, -15638, -522, 3080, 2230]]
  ![![-1511, -4887, 5803, -3628, 249]] where
 M := ![![![-1511, -4887, 5803, -3628, 249]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![-1511, -4887, 5803, -3628, 249]] ![![-330643, 102197, -1257, 7038, -19691]]
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


lemma PB1189I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1189I0 : PrimesBelowBoundCertificateInterval O 1 23 1189 where
  m := 9
  g := ![5, 5, 5, 1, 2, 4, 1, 4, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1189I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2, I13N3]
    · exact ![I17N0]
    · exact ![I19N0, I19N1, I19N2, I19N3]
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
    · exact ![16807]
    · exact ![14641, 11]
    · exact ![169, 13, 13, 13]
    · exact ![1419857]
    · exact ![361, 19, 19, 19]
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
      exact NI13N2
      exact NI13N3
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
      exact NI19N3
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I11N1, I13N0, I13N1, I13N2, I13N3, I19N0, I19N1, I19N2, I19N3, I23N1, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [I11N1], [I13N0, I13N1, I13N2, I13N3], [], [I19N0, I19N1, I19N2, I19N3], [I23N1, I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
