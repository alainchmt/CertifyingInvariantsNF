
import IdealArithmetic.Examples.NF5_3_15187500000_8.RI5_3_15187500000_8
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-298385, 155607, -16463, -74380, 39328]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-298385, 155607, -16463, -74380, 39328]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![1, 7, 27, 1, 0], ![5, 4, 12, 0, 1]] where
  M :=![![![-298385, 155607, -16463, -74380, 39328], ![-771630, -235575, 178472, 5486, -262468], ![6052238, -1270120, -319571, 923800, 278926], ![-555212, 605864, -140232, -236491, 253742], ![-1650918, 93513, 174813, -173554, -220473]]]
  hmulB := by decide  
  f := ![![![4034243, 599585, 105183, -512838, -451318]], ![![9718978, 1444595, 253450, -1235346, -1087196]], ![![23412770, 3481156, 610849, -2974876, -2618842]], ![![24161163, 3592328, 630350, -3070059, -2702566]], ![![11560797, 1718862, 301608, -1469002, -1293149]]]
  g := ![![![-14505, 17895, 52409, -74380, 39328], ![18456, 26755, 109654, 5486, -262468], ![128752, -305256, -986527, 923800, 278926], ![-54739, 42977, 110349, -236491, 253742], ![-12931, 75527, 258843, -173554, -220473]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [1, 7, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 20, 3], [7, 8, 26], [0, 1]]
 g := ![![[13, 4, 13], [18, 20], [21, 13, 7], [1]], ![[9, 27, 6, 8], [24, 5], [5, 10, 20, 15], [13, 9, 1, 27]], ![[4, 9, 22, 12], [14, 5], [23, 8, 17, 3], [23, 28, 1, 2]]]
 h' := ![![[16, 20, 3], [17, 7, 10], [8, 15, 22], [28, 22, 23], [0, 1]], ![[7, 8, 26], [28, 3, 14], [20, 16, 18], [23, 6, 18], [16, 20, 3]], ![[0, 1], [10, 19, 5], [13, 27, 18], [1, 1, 17], [7, 8, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 26], []]
 b := ![[], [13, 1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [1, 7, 6, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3117490957, -1318271944, -731949862, -2594429942, -1728662922]
  a := ![24, -100, -27, -63, -153]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![495008121, 819220322, 3105572884, -2594429942, -1728662922]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![612363, 91149, 16009, -77708, -68458]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![612363, 91149, 16009, -77708, -68458]] 
 ![![29, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![612363, 91149, 16009, -77708, -68458], ![1474464, 219961, 38700, -186622, -164666], ![3547476, 532046, 93995, -446196, -395200], ![-539248, -78904, -13672, 69779, 60754], ![-722746, -105263, -18171, 94010, 81597]]]
  hmulB := by decide  
  f := ![![![-17869, 895, 1931, -1914, -2408]], ![![1427, -750, 81, 368, -198]], ![![-15416, 2738, 983, -2336, -908]], ![![-18413, 1285, 1865, -2047, -2298]], ![![-11270, -291, 1513, -996, -1973]]]
  g := ![![![116718, 91149, 16009, -77708, -68458], ![280337, 219961, 38700, -186622, -164666], ![670430, 532046, 93995, -446196, -395200], ![-104727, -78904, -13672, 69779, 60754], ![-141065, -105263, -18171, 94010, 81597]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![463, -232, 14, -202, 144]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![463, -232, 14, -202, 144]] 
 ![![29, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![463, -232, 14, -202, 144], ![-2450, 1209, -74, 1060, -750], ![12746, -6334, 385, -5536, 3930], ![-4832, 2398, -146, 2097, -1488], ![9404, -4660, 284, -4078, 2891]]]
  hmulB := by decide  
  f := ![![![-57, 80, -22, -34, 36]], ![![-82, 77, -18, -36, 30]], ![![58, 38, -23, -16, 30]], ![![-1, 22, -8, -9, 12]], ![![-77, 64, -14, -32, 23]]]
  g := ![![![157, -232, 14, -202, 144], ![-820, 1209, -74, 1060, -750], ![4292, -6334, 385, -5536, 3930], ![-1625, 2398, -146, 2097, -1488], ![3159, -4660, 284, -4078, 2891]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-298385, 155607, -16463, -74380, 39328]] ![![612363, 91149, 16009, -77708, -68458]]
  ![![57, -80, 22, 34, -36]] where
 M := ![![![57, -80, 22, 34, -36]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![57, -80, 22, 34, -36]] ![![463, -232, 14, -202, 144]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![-29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-30212, 4794, 2131, -4132, -2275]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-30212, 4794, 2131, -4132, -2275]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![9, 1, 1, 0, 0], ![8, 12, 0, 1, 0], ![5, 30, 0, 0, 1]] where
  M :=![![![-30212, 4794, 2131, -4132, -2275], ![60143, -35208, 4650, 16184, -10121], ![204015, 43501, -40679, 4374, 58673], ![-124774, 32524, 4392, -21011, -2132], ![-828, -30741, 10755, 9460, -17685]]]
  hmulB := by decide  
  f := ![![![137236, -68224, 4145, -59618, 42329]], ![![-719763, 356462, -21750, 312004, -221183]], ![![137914, -68481, 4164, -59876, 42483]], ![![-289144, 143164, -8738, 125321, -88834]], ![![-585072, 289669, -17682, 253572, -179744]]]
  g := ![![![-160, 3887, 2131, -4132, -2275], ![-1954, 2244, 4650, 16184, -10121], ![7799, -55758, -40679, 4374, 58673], ![466, 11104, 4392, -21011, -2132], ![-2738, 12114, 10755, 9460, -17685]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [13, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 30], [0, 1]]
 g := ![![[1, 7], [18, 20], [15, 1], [18, 1]], ![[3, 24], [6, 11], [2, 30], [5, 30]]]
 h' := ![![[18, 30], [14, 21], [22, 19], [14, 1], [0, 1]], ![[0, 1], [20, 10], [23, 12], [1, 30], [18, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [24, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [13, 13, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-98387046, 38763345, 23218698, 71895986, 54401343]
  a := ![178, -1157, -304, -859, -1638]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-37242901, -79975725, 23218698, 71895986, 54401343]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53274, -23535, -8486, -37862, -16709]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![53274, -23535, -8486, -37862, -16709]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![9, 24, 1, 0, 0], ![22, 18, 0, 1, 0], ![18, 29, 0, 0, 1]] where
  M :=![![![53274, -23535, -8486, -37862, -16709], ![304417, -135758, -48730, -219058, -96877], ![1767341, -788283, -281365, -1263482, -560297], ![450532, -200148, -71806, -321135, -142024], ![779204, -347120, -124578, -558744, -247071]]]
  hmulB := by decide  
  f := ![![![281912417810, -139783272985, 8516000808, -122289433998, 86727517261]], ![![-1474437389113, 731084092226, -44539754916, 639589114878, -453595819255]], ![![-810896537321, 402074420558, -24495535247, 351754915056, -249464156222]], ![![-750271009184, 372013897452, -22664161338, 325456458325, -230813322822]], ![![-1032487307365, 511947846286, -31189341754, 447877711130, -317634325820]]]
  g := ![![![40754, 43426, -8486, -37862, -16709], ![235679, 251169, -48730, -219058, -96877], ![1360696, 1450186, -281365, -1263482, -560297], ![345748, 368462, -71806, -321135, -142024], ![601292, 640813, -124578, -558744, -247071]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [26, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 30], [0, 1]]
 g := ![![[2, 5], [24, 8], [5, 20], [10, 1]], ![[21, 26], [11, 23], [19, 11], [20, 30]]]
 h' := ![![[10, 30], [27, 6], [25, 15], [19, 12], [0, 1]], ![[0, 1], [25, 25], [20, 16], [15, 19], [10, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [13, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [26, 21, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-539868, 203685, 135401, 397574, 319866]
  a := ![17, -87, -23, -60, -128]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-524603, -628335, 135401, 397574, 319866]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23509512, -6595834, -665457, 4103860, 134687]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![23509512, -6595834, -665457, 4103860, 134687]] 
 ![![31, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![23509512, -6595834, -665457, 4103860, 134687], ![-10655655, 24428752, -7126604, -8508276, 12176893], ![-265612315, 11137803, 29479041, -26711098, -37701721], ![79171944, -32842486, 1442032, 17116703, -5614238], ![44123726, 13410275, -10184515, -294948, 14974047]]]
  hmulB := by decide  
  f := ![![![1961072, -676176, 59265, -706630, 416507]], ![![158549, 1678, 5006, -29388, -1205]], ![![3053169, -1210453, 93973, -1174078, 753285]], ![![-77894, 96974, -1765, 63109, -58941]], ![![2540692, -1032383, 77760, -989924, 641312]]]
  g := ![![![1557813, -6595834, -665457, 4103860, 134687], ![-6993576, 24428752, -7126604, -8508276, 12176893], ![987952, 11137803, 29479041, -26711098, -37701721], ![8363647, -32842486, 1442032, 17116703, -5614238], ![-4639583, 13410275, -10184515, -294948, 14974047]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-30212, 4794, 2131, -4132, -2275]] ![![53274, -23535, -8486, -37862, -16709]]
  ![![-18222643, -2905969, 3295939, -685030, -4679244]] where
 M := ![![![-18222643, -2905969, 3295939, -685030, -4679244]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-18222643, -2905969, 3295939, -685030, -4679244]] ![![23509512, -6595834, -665457, 4103860, 134687]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-1533583266005770, 45661990883071, 176665192082326, -148441860430336, -228323897426405]]]
 hmul := by decide  
 g := ![![![![-49470427935670, 1472967447841, 5698877163946, -4788447110656, -7365287013755]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 5 2 5 [4, 13, 30, 16, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 33, 31, 5, 19], [8, 2, 9, 16, 20], [8, 28, 0, 16, 26], [32, 10, 34, 0, 9], [0, 1]]
 g := ![![[31, 1, 30, 9, 34], [19, 11, 36, 1], [2, 26, 25, 35, 1], [], []], ![[33, 1, 27, 29, 7, 19, 30, 32], [35, 8, 2, 16], [19, 20, 14, 2, 30, 32, 16, 18], [4, 27, 4, 25], [11, 6, 23, 28]], ![[11, 0, 12, 34, 32, 33, 10, 32], [12, 1, 22, 4], [24, 9, 17, 14, 28, 32, 31, 13], [25, 36, 13, 7], [6, 12, 25, 30]], ![[7, 22, 33, 33, 18, 17, 15, 26], [24, 20, 9, 10], [6, 28, 24, 9, 1, 5, 17, 12], [28, 10, 8, 9], [26, 26, 35, 10]], ![[22, 0, 5, 11, 1, 16, 0, 27], [23, 23, 27, 33], [0, 30, 1, 15, 28, 35, 22, 26], [8, 33, 21, 1], [26, 10, 23, 7]]]
 h' := ![![[24, 33, 31, 5, 19], [25, 13, 35, 29, 16], [29, 18, 20, 18, 36], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[8, 2, 9, 16, 20], [7, 13, 28, 18, 8], [6, 17, 35, 32, 4], [32, 0, 33, 28, 6], [14, 11, 5, 2, 32], [24, 33, 31, 5, 19]], ![[8, 28, 0, 16, 26], [5, 14, 32, 16, 34], [33, 6, 3, 11, 35], [20, 3, 29, 10, 24], [3, 17, 8, 20, 9], [8, 2, 9, 16, 20]], ![[32, 10, 34, 0, 9], [27, 11, 24, 33, 1], [7, 5, 17, 3, 11], [8, 4, 28, 36, 34], [34, 6, 7, 8, 34], [8, 28, 0, 16, 26]], ![[0, 1], [30, 23, 29, 15, 15], [14, 28, 36, 10, 25], [30, 30, 21, 0, 9], [32, 3, 16, 7, 36], [32, 10, 34, 0, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 2, 11, 31], [], [], []]
 b := ![[], [2, 13, 25, 30, 12], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 5
  hpos := by decide
  P := [4, 13, 30, 16, 2, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-122500995805681094688, 54091324854813725950, 21385352587903478456, 90396582543382754546, 44869643147464174804]
  a := ![-85, 448, 119, 311, 655]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3310837724477867424, 1461927698778749350, 577982502375769688, 2443150879550885258, 1212693058039572292]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 69343957 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37390, 1316, 4237, -3682, -5451]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-37390, 1316, 4237, -3682, -5451]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![22, 34, 31, 1, 0], ![36, 30, 6, 0, 1]] where
  M :=![![![-37390, 1316, 4237, -3682, -5451], ![132673, -48356, 102, 26612, -5595], ![80305, 126327, -53849, -32142, 85431], ![-183296, 28112, 13266, -24767, -14358], ![69034, -54981, 10385, 23094, -19933]]]
  hmulB := by decide  
  f := ![![![-5406, -890, -159, 616, 603]], ![![-13027, -2126, -446, 1392, 1245]], ![![-27723, -6841, -1327, 1226, 2931]], ![![-34537, -7399, -1459, 2387, 3549]], ![![-18120, -3341, -661, 1684, 1847]]]
  g := ![![![5850, 7074, 3685, -3682, -5451], ![-6131, -19154, -19300, 26612, -5595], ![-55807, -32775, 10487, -32142, 85431], ![21426, 31730, 21151, -24767, -14358], ![6794, -5907, -14291, 23094, -19933]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [15, 21, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 31, 26], [34, 9, 15], [0, 1]]
 g := ![![[13, 1, 8], [16, 4], [33, 40], [29, 3, 1], []], ![[25, 2, 37, 15], [7, 9], [8, 18], [22, 13, 16, 15], [32, 20]], ![[25, 12, 14, 19], [38, 25], [22, 33], [25, 11, 4, 24], [2, 20]]]
 h' := ![![[10, 31, 26], [14, 28, 34], [7, 1, 2], [16, 2, 9], [0, 0, 1], [0, 1]], ![[34, 9, 15], [2, 11, 9], [36, 24, 3], [19, 10, 10], [30, 17, 9], [10, 31, 26]], ![[0, 1], [13, 2, 39], [38, 16, 36], [9, 29, 22], [19, 24, 31], [34, 9, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 8], []]
 b := ![[], [35, 36, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [15, 21, 38, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2292448503, -928388773, -710469859, -2196124838, -1823856782]
  a := ![35, -97, -26, -45, -163]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2835757051, 3133062419, 1910061971, -2196124838, -1823856782]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5406, 890, 159, -616, -603]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![5406, 890, 159, -616, -603]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![34, 18, 1, 0, 0], ![7, 37, 0, 1, 0], ![4, 13, 0, 0, 1]] where
  M :=![![![5406, 890, 159, -616, -603], ![13027, 2126, 446, -1392, -1245], ![27723, 6841, 1327, -1226, -2931], ![-5246, -576, 20, 1019, 948], ![-8844, 115, 35, 2248, 917]]]
  hmulB := by decide  
  f := ![![![37390, -1316, -4237, 3682, 5451]], ![![-132673, 48356, -102, -26612, 5595]], ![![-29199, 17057, -2245, -7846, 4893]], ![![-108875, 42728, -1139, -22783, 6330]], ![![-40103, 16545, -699, -8642, 2792]]]
  g := ![![![164, 699, 159, -616, -603], ![307, 1507, 446, -1392, -1245], ![71, 1620, 1327, -1226, -2931], ![-411, -1243, 20, 1019, 948], ![-718, -2332, 35, 2248, 917]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [33, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 40], [0, 1]]
 g := ![![[28, 5], [36], [37], [29, 33], [1]], ![[0, 36], [36], [37], [0, 8], [1]]]
 h' := ![![[19, 40], [1, 28], [0, 35], [27, 18], [8, 19], [0, 1]], ![[0, 1], [0, 13], [9, 6], [0, 23], [0, 22], [19, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [23, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [33, 22, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-536363, 246372, 88856, 379288, 192444]
  a := ![-14, -82, -18, -98, -84]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-170299, -436304, 88856, 379288, 192444]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-37390, 1316, 4237, -3682, -5451]] ![![5406, 890, 159, -616, -603]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![-41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-264049586, 130926178, -7976401, 114540802, -81232197]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-264049586, 130926178, -7976401, 114540802, -81232197]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![42, 21, 6, 1, 0], ![11, 26, 13, 0, 1]] where
  M :=![![![-264049586, 130926178, -7976401, 114540802, -81232197], ![1381012535, -684760372, 41717580, -599062796, 424854603], ![-7222869181, 3581382837, -218188189, 3133173738, -2222042991], ![2735543246, -1356390014, 82635198, -1186638169, 841562340], ![-5317432408, 2636592285, -160628819, 2306623470, -1635854549]]]
  hmulB := by decide  
  f := ![![![-222, 688, -195, -248, 327]], ![![-7135, 322, 820, -768, -1071]], ![![26037, -9409, 71, 5054, -1233]], ![![-7, -438, 196, 79, -339]], ![![3277, -2428, 479, 966, -947]]]
  g := ![![![-97237421, -3776594, 8390636, 114540802, -81232197], ![508563938, 19752062, -43884081, -599062796, 424854603], ![-2659853332, -103305765, 229519262, 3133173738, -2222042991], ![1007375828, 39125365, -86926656, -1186638169, 841562340], ![-1958167863, -76053077, 168970686, 2306623470, -1635854549]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [15, 34, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 35, 22], [32, 7, 21], [0, 1]]
 g := ![![[4, 3, 13], [23, 9, 14], [35, 23], [19, 15, 1], []], ![[27, 26], [7, 38, 31, 32], [18, 40], [13, 24, 16, 3], [28, 11]], ![[42, 15, 8, 15], [6, 10, 4, 10], [24, 15], [23, 19, 20, 11], [29, 11]]]
 h' := ![![[26, 35, 22], [42, 21, 20], [32, 5, 10], [16, 32, 18], [0, 0, 1], [0, 1]], ![[32, 7, 21], [32, 3], [13, 24, 8], [38, 14, 13], [41, 15, 7], [26, 35, 22]], ![[0, 1], [24, 19, 23], [19, 14, 25], [32, 40, 12], [30, 28, 35], [32, 7, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 38], []]
 b := ![[], [2, 11, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [15, 34, 28, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-734872910, 328046208, 117350912, 524393259, 234249921]
  a := ![17, 62, 14, 81, 55]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-589212533, -390109539, -141261805, 524393259, 234249921]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-260, 89, 4, 36, -47]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-260, 89, 4, 36, -47]] 
 ![![43, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-260, 89, 4, 36, -47], ![881, -482, 46, -226, 155], ![-2443, 1861, -281, 1574, -833], ![806, -504, 52, -669, 410], ![-2650, 1160, -28, 1150, -873]]]
  hmulB := by decide  
  f := ![![![-13527120, 6026363, 2158454, 9680952, 4285291]], ![![-7794559, 3472493, 1243738, 5578330, 2469258]], ![![-18679263, 8321647, 2980553, 13368178, 5917449]], ![![-13679740, 6094353, 2182806, 9790175, 4333639]], ![![-4954092, 2207055, 790498, 3545490, 1569418]]]
  g := ![![![-76, 89, 4, 36, -47], ![386, -482, 46, -226, 155], ![-1971, 1861, -281, 1574, -833], ![745, -504, 52, -669, 410], ![-1473, 1160, -28, 1150, -873]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5763680, -865132, -150197, 728672, 650403]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-5763680, -865132, -150197, 728672, 650403]] 
 ![![43, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-5763680, -865132, -150197, 728672, 650403], ![-13987511, -2033772, -364926, 1799660, 1535613], ![-33165863, -5163729, -863085, 4104714, 3863367], ![4927558, 821264, 127884, -584121, -609192], ![7049968, 874743, 184895, -978588, -676127]]]
  hmulB := by decide  
  f := ![![![128609760, -57295782, -20521643, -92042298, -40742613]], ![![98034549, -43674516, -15642893, -70160482, -31056624]], ![![105812077, -47139397, -16883853, -75726298, -33520395]], ![![127069884, -56609764, -20275924, -90940209, -40254780]], ![![44110330, -19651231, -7038453, -31568434, -13973831]]]
  g := ![![![-159990, -865132, -150197, 728672, 650403], ![-454285, -2033772, -364926, 1799660, 1535613], ![-734402, -5163729, -863085, 4104714, 3863367], ![54832, 821264, 127884, -584121, -609192], ![379863, 874743, 184895, -978588, -676127]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-264049586, 130926178, -7976401, 114540802, -81232197]] ![![-260, 89, 4, 36, -47]]
  ![![511070411283, -253408825939, 15438397745, -221694779586, 157225666966]] where
 M := ![![![511070411283, -253408825939, 15438397745, -221694779586, 157225666966]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![511070411283, -253408825939, 15438397745, -221694779586, 157225666966]] ![![-5763680, -865132, -150197, 728672, 650403]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![102906683846793554, -51025184318940519, 3108601634501984, -44639396235874736, 31658205300772687]]]
 hmul := by decide  
 g := ![![![![2393178694111478, -1186632193463733, 72293061267488, -1038125493857552, 736237332576109]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1427, 192, -246, 50, 356]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![1427, 192, -246, 50, 356]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![38, 30, 1, 0, 0], ![17, 24, 0, 1, 0], ![9, 1, 0, 0, 1]] where
  M :=![![![1427, 192, -246, 50, 356], ![-8290, 2137, 302, -1308, -206], ![7034, -9022, 2233, 2992, -3718], ![8228, -274, -934, 965, 1108], ![-5968, 2764, -216, -1690, 783]]]
  hmulB := by decide  
  f := ![![![-10373775, -1541672, -270438, 1318838, 1160560]], ![![-24992106, -3714205, -651550, 3177228, 2795954]], ![![-25620772, -3807620, -667935, 3257164, 2866290]], ![![-16320597, -2425482, -425480, 2074831, 1825844]], ![![-2259103, -335739, -58896, 287196, 252733]]]
  g := ![![![143, 128, -246, 50, 356], ![92, 525, 302, -1308, -206], ![-2026, -3066, 2233, 2992, -3718], ![369, 74, -934, 965, 1108], ![509, 1043, -216, -1690, 783]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [21, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 46], [0, 1]]
 g := ![![[21, 9], [16, 27], [43, 42], [0, 42], [1]], ![[0, 38], [0, 20], [39, 5], [43, 5], [1]]]
 h' := ![![[29, 46], [40, 44], [37, 36], [0, 29], [26, 29], [0, 1]], ![[0, 1], [0, 3], [0, 11], [42, 18], [21, 18], [29, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [34, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [21, 18, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-167312, 72282, 31179, 117377, 69007]
  a := ![-1, -46, -11, -45, -55]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-84438, -79769, 31179, 117377, 69007]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26728, 11907, 4266, 19130, 8471]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-26728, 11907, 4266, 19130, 8471]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![26, 37, 1, 0, 0], ![44, 16, 0, 1, 0], ![2, 37, 0, 0, 1]] where
  M :=![![![-26728, 11907, 4266, 19130, 8471], ![-154483, 68824, 24644, 110550, 48919], ![-892147, 397445, 142387, 638530, 282731], ![-226906, 101090, 36194, 162371, 71842], ![-394150, 175588, 62916, 282116, 124941]]]
  hmulB := by decide  
  f := ![![![85956, 12793, 2244, -10942, -9623]], ![![207243, 30740, 5414, -26322, -23203]], ![![221330, 32855, 5779, -28124, -24776]], ![![149412, 22204, 3902, -19001, -16728]], ![![164657, 24424, 4302, -20914, -18436]]]
  g := ![![![-21198, -16286, 4266, 19130, 8471], ![-122495, -94081, 24644, 110550, 48919], ![-707553, -543583, 142387, 638530, 282731], ![-179914, -138174, 36194, 162371, 71842], ![-312616, -240191, 62916, 282116, 124941]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [46, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 46], [0, 1]]
 g := ![![[3, 21], [4, 27], [20, 37], [33, 9], [1]], ![[19, 26], [38, 20], [37, 10], [13, 38], [1]]]
 h' := ![![[3, 46], [4, 16], [20, 11], [33, 15], [1, 3], [0, 1]], ![[0, 1], [5, 31], [6, 36], [31, 32], [10, 44], [3, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [40, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [46, 44, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-194333, 49466, 92806, 188999, 242133]
  a := ![-27, 63, 21, 23, 111]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-242713, -326963, 92806, 188999, 242133]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3223, -1688, 96, -1444, 1044]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![3223, -1688, 96, -1444, 1044]] 
 ![![47, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![3223, -1688, 96, -1444, 1044], ![-17816, 8619, -548, 7608, -5376], ![91248, -45752, 2695, -39928, 28200], ![-34528, 17204, -1060, 14991, -10728], ![67840, -33524, 2020, -29420, 20707]]]
  hmulB := by decide  
  f := ![![![115177, -41816, 32, 23052, -4764]], ![![67605, -21685, -972, 12644, -1164]], ![![21137, -16128, 2935, 6852, -5700]], ![![31494, -12852, 500, 6743, -2112]], ![![71382, -22476, -1172, 13220, -989]]]
  g := ![![![721, -1688, 96, -1444, 1044], ![-3707, 8619, -548, 7608, -5376], ![19801, -45752, 2695, -39928, 28200], ![-7354, 17204, -1060, 14991, -10728], ![14518, -33524, 2020, -29420, 20707]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![1427, 192, -246, 50, 356]] ![![-26728, 11907, 4266, 19130, 8471]]
  ![![3870, -2145, -176, -2424, -165]] where
 M := ![![![3870, -2145, -176, -2424, -165]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![3870, -2145, -176, -2424, -165]] ![![3223, -1688, 96, -1444, 1044]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![107130954, -53138999, 3308800, -46363996, 33196617]]]
 hmul := by decide  
 g := ![![![![2279382, -1130617, 70400, -986468, 706311]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![403014, -200260, 12177, -175026, 124263]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![403014, -200260, 12177, -175026, 124263]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![24, 6, 3, 25, 1]] where
  M :=![![![403014, -200260, 12177, -175026, 124263], ![-2112909, 1046628, -63820, 916056, -649341], ![11038503, -5475819, 333467, -4789526, 3397509], ![-4181534, 2073746, -126318, 1814067, -1286652], ![8130112, -4030725, 245591, -3526482, 2500819]]]
  hmulB := by decide  
  f := ![![![430, -6, -51, 44, 69]], ![![-1661, 582, 12, -300, 63]], ![![-825, -1511, 657, 546, -963]], ![![2136, -290, -160, 315, 198]], ![![949, -146, -62, 161, 82]]]
  g := ![![![-48666, -17846, -6804, -61917, 124263], ![254175, 93258, 35551, 323577, -649341], ![-1330221, -487941, -186020, -1692967, 3397509], ![503738, 184786, 70446, 641139, -1286652], ![-979048, -359163, -136922, -1246169, 2500819]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [37, 31, 5, 15, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 4, 24, 36], [51, 42, 15, 27], [23, 6, 14, 43], [0, 1]]
 g := ![![[11, 1], [25, 16, 47], [13, 9, 28, 52], [8, 38, 1], []], ![[37, 33, 34, 9, 8, 17], [27, 28, 16], [27, 8, 51, 39, 34, 37], [7, 24, 46], [7, 1, 27, 28, 4, 16]], ![[13, 36, 28, 52, 23, 22], [20, 44, 29], [19, 51, 8, 36, 29, 27], [46, 13, 9], [22, 7, 21, 29, 16, 20]], ![[14, 23, 9, 18, 0, 40], [36, 44, 40], [0, 23, 37, 4, 35, 52], [34, 3, 7], [23, 51, 27, 21, 14, 7]]]
 h' := ![![[17, 4, 24, 36], [45, 13, 1], [49, 13, 44, 10], [22, 42, 17, 30], [0, 0, 0, 1], [0, 1]], ![[51, 42, 15, 27], [19, 33, 18, 23], [8, 33, 46, 49], [0, 17, 47, 20], [43, 34, 48, 24], [17, 4, 24, 36]], ![[23, 6, 14, 43], [38, 42, 49, 37], [6, 23, 8, 20], [34, 14, 5, 52], [26, 40, 46, 50], [51, 42, 15, 27]], ![[0, 1], [45, 18, 38, 46], [23, 37, 8, 27], [1, 33, 37, 4], [27, 32, 12, 31], [23, 6, 14, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [6, 9, 13], []]
 b := ![[], [], [31, 47, 1, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [37, 31, 5, 15, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5910949558891, 2559056117030, 1253798024760, 4706444851650, 2900115175690]
  a := ![-23, 80, 21, 45, 127]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1424787052367, -280030847870, -140500896270, -1279178010200, 2900115175690]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-430, 6, 51, -44, -69]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-430, 6, 51, -44, -69]] 
 ![![53, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![-430, 6, 51, -44, -69], ![1661, -582, -12, 300, -63], ![825, 1511, -657, -546, 963], ![-2136, 290, 160, -315, -198], ![982, -697, 105, 236, -251]]]
  hmulB := by decide  
  f := ![![![-403014, 200260, -12177, 175026, -124263]], ![![-203463, 101164, -6148, 88392, -62775]], ![![-482019, 239343, -14563, 209254, -148509]], ![![-95996, 47778, -2901, 41727, -29649]], ![![-487976, 242305, -14743, 211842, -150347]]]
  g := ![![![30, 6, 51, -44, -69], ![313, -582, -12, 300, -63], ![-1013, 1511, -657, -546, 963], ![-23, 290, 160, -315, -198], ![474, -697, 105, 236, -251]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![403014, -200260, 12177, -175026, 124263]] ![![-430, 6, 51, -44, -69]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26364330, -11952925, 789224, -10903734, 7381939]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![26364330, -11952925, 789224, -10903734, 7381939]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![1, 37, 33, 1, 0], ![10, 13, 35, 0, 1]] where
  M :=![![![26364330, -11952925, 789224, -10903734, 7381939], ![-124617763, 64487574, -3781762, 55340770, -40093141], ![683738337, -332526411, 20612671, -293503514, 206115451], ![-256659412, 126280148, -7746838, 110867957, -78319588], ![493901760, -246210170, 14928236, -214872588, 152799513]]]
  hmulB := by decide  
  f := ![![![-12323950, -2866355, 2539958, -190254, -3680455]], ![![85358647, -19357186, -4006852, 13476682, 3109693]], ![![-96601961, 93452375, -20254345, -37437770, 37320353]], ![![-2084314, 40092120, -13629447, -12614905, 22539671]], ![![-39352806, 50174551, -12445077, -19004696, 22112885]]]
  g := ![![![-619514, 5008814, 1732959, -10903734, 7381939], ![3745303, -24778137, -7233343, 55340770, -40093141], ![-18371401, 133010216, 42240472, -293503514, 206115451], ![7045229, -50130163, -15681421, 110867957, -78319588], ![-13885098, 96909863, 29792215, -214872588, 152799513]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [23, 29, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 4, 40], [53, 54, 19], [0, 1]]
 g := ![![[20, 13, 41], [1, 0, 3], [18, 26], [27, 45, 36], [1]], ![[40, 32, 55, 32], [46, 16, 34, 39], [34, 25], [27, 15, 9, 47], [35, 34, 53, 44]], ![[52, 58, 12, 16], [2, 37, 36, 46], [29, 53], [41, 46, 2, 9], [5, 7, 44, 15]]]
 h' := ![![[12, 4, 40], [36, 50, 49], [16, 33, 48], [28, 9, 12], [36, 30, 6], [0, 1]], ![[53, 54, 19], [33, 43, 44], [26, 36, 18], [10, 12, 5], [38, 49, 49], [12, 4, 40]], ![[0, 1], [28, 25, 25], [33, 49, 52], [13, 38, 42], [23, 39, 4], [53, 54, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 47], []]
 b := ![[], [51, 24, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [23, 29, 53, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-449730524, 196414797, 80336442, 331809291, 168730722]
  a := ![-1, 51, 12, 47, 64]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-41844865, -241932684, -284321109, 331809291, 168730722]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![872, -315, -34, 202, 25]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![872, -315, -34, 202, 25]] 
 ![![59, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![872, -315, -34, 202, 25], ![-881, 1020, -324, -326, 581], ![-12657, 335, 1277, -1050, -1559], ![3646, -1426, 66, 737, -262], ![2130, 624, -444, -40, 639]]]
  hmulB := by decide  
  f := ![![![20339140, -9061117, -3245404, -14556086, -6443269]], ![![8886247, -3958836, -1417930, -6359610, -2815091]], ![![15987799, -7122588, -2551085, -11441968, -5064802]], ![![18093256, -8060572, -2887042, -12948779, -5731796]], ![![16804972, -7486640, -2681476, -12026792, -5323673]]]
  g := ![![![-36, -315, -34, 202, 25], ![-381, 1020, -324, -326, 581], ![1072, 335, 1277, -1050, -1559], ![132, -1426, 66, 737, -262], ![-416, 624, -444, -40, 639]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-346827519, 171428630, -10473472, 150190692, -106345102]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-346827519, 171428630, -10473472, 150190692, -106345102]] 
 ![![59, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![37, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![-346827519, 171428630, -10473472, 150190692, -106345102], ![1807525414, -897548271, 54610056, -784699220, 556917178], ![-9469066826, 4691989598, -286021037, 4106043852, -2911014838], ![3585142236, -1777179284, 108296804, -1554955445, 1102623484], ![-6966487620, 3454895140, -210447508, 3022262024, -2143584033]]]
  hmulB := by decide  
  f := ![![![606930255, 110918062, -114608936, 18748260, 163991098]], ![![449564068, 109624993, -94409264, 5370076, 137149298]], ![![442135243, -398636, -55356021, 38837472, 73113244]], ![![239330361, 30120038, -40475244, 11615935, 56892938]], ![![296742630, 87269880, -67482476, -1078912, 99038723]]]
  g := ![![![-126580489, 171428630, -10473472, 150190692, -106345102], ![662187620, -897548271, 54610056, -784699220, 556917178], ![-3462949311, 4691989598, -286021037, 4106043852, -2911014838], ![1311562183, -1777179284, 108296804, -1554955445, 1102623484], ![-2549513290, 3454895140, -210447508, 3022262024, -2143584033]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![26364330, -11952925, 789224, -10903734, 7381939]] ![![872, -315, -34, 202, 25]]
  ![![-500469577, -77302790, -13027832, 62233492, 57895938]] where
 M := ![![![-500469577, -77302790, -13027832, 62233492, 57895938]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-500469577, -77302790, -13027832, 62233492, 57895938]] ![![-346827519, 171428630, -10473472, 150190692, -106345102]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-23004138628633813, 11886041406256636, -697989160856048, 10207104948252224, -7389249687225376]]]
 hmul := by decide  
 g := ![![![![-389900654722607, 201458328919604, -11830324760272, 173001778783936, -125241520122464]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-140913356, 62777101, 22484792, 100847320, 44640261]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-140913356, 62777101, 22484792, 100847320, 44640261]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![12, 42, 53, 1, 0], ![25, 11, 38, 0, 1]] where
  M :=![![![-140913356, 62777101, 22484792, 100847320, 44640261], ![-814103527, 362684282, 129902154, 582628654, 257901699], ![-4703348011, 2095348245, 750488135, 3366040350, 1489984263], ![-1195668802, 532672156, 190786488, 855703091, 378778626], ![-2078195962, 925839264, 331606636, 1487300418, 658356403]]]
  hmulB := by decide  
  f := ![![![1368, 265, 54, -236, -183]], ![![4037, 358, 136, -342, -525]], ![![11133, 1361, -31, -1246, -501]], ![![12683, 1483, 77, -1363, -831]], ![![8197, 1011, 28, -932, -479]]]
  g := ![![![-40444061, -76456610, -115061526, 100847320, 44640261], ![-233658850, -441715375, -664748870, 582628654, 257901699], ![-1349925226, -2551937268, -3840476269, 3366040350, 1489984263], ![-343173304, -648744632, -976312543, 855703091, 378778626], ![-596470673, -1127585225, -1696932112, 1487300418, 658356403]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [5, 51, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 35, 45], [2, 25, 16], [0, 1]]
 g := ![![[49, 42, 39], [32, 34], [23, 26, 19], [60, 21, 1], [1]], ![[5, 57, 42, 22], [50, 15], [30, 46, 14, 36], [3, 15, 0, 41], [17, 31, 31, 52]], ![[23, 3, 38, 46], [40, 12], [8, 50, 14, 12], [17, 32, 26, 47], [29, 22, 55, 9]]]
 h' := ![![[60, 35, 45], [11, 9, 51], [7, 3, 20], [5, 32, 43], [56, 10, 1], [0, 1]], ![[2, 25, 16], [41, 53, 33], [48, 19, 25], [31, 14, 14], [36, 59, 48], [60, 35, 45]], ![[0, 1], [24, 60, 38], [23, 39, 16], [60, 15, 4], [46, 53, 12], [2, 25, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 44], []]
 b := ![[], [27, 45, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [5, 51, 60, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13252437153, -5121692555, -5504846169, -14969794400, -15243047264]
  a := ![79, -177, -62, -63, -317]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9409281173, 12971855609, 22411968083, -14969794400, -15243047264]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1368, -265, -54, 236, 183]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-1368, -265, -54, 236, 183]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![23, 52, 1, 0, 0], ![31, 10, 0, 1, 0], ![45, 0, 0, 0, 1]] where
  M :=![![![-1368, -265, -54, 236, 183], ![-4037, -358, -136, 342, 525], ![-11133, -1361, 31, 1246, 501], ![2356, -114, 20, -91, -108], ![1644, 610, -40, -158, -169]]]
  hmulB := by decide  
  f := ![![![140913356, -62777101, -22484792, -100847320, -44640261]], ![![814103527, -362684282, -129902154, -582628654, -257901699]], ![![824225223, -367193512, -131517219, -589872438, -261108174]], ![![224672428, -100091887, -35849780, -160791091, -71174487]], ![![138021262, -61488669, -22023316, -98777538, -43724068]]]
  g := ![![![-257, 3, -54, 236, 183], ![-576, 54, -136, 342, 525], ![-1197, -253, 31, 1246, 501], ![157, -4, 20, -91, -108], ![247, 70, -40, -158, -169]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [2, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 60], [0, 1]]
 g := ![![[59, 1], [58], [47, 14], [11, 13], [4, 1]], ![[2, 60], [58], [42, 47], [2, 48], [8, 60]]]
 h' := ![![[4, 60], [58, 1], [28, 34], [39, 21], [53, 14], [0, 1]], ![[0, 1], [1, 60], [42, 27], [1, 40], [48, 47], [4, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [31, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [2, 57, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-122862, 24897, 60923, 121712, 155610]
  a := ![23, -51, -17, -18, -92]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-201633, -71479, 60923, 121712, 155610]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-140913356, 62777101, 22484792, 100847320, 44640261]] ![![-1368, -265, -54, 236, 183]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![-61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)


lemma PB6026I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB6026I1 : PrimesBelowBoundCertificateInterval O 23 61 6026 where
  m := 9
  g := ![3, 3, 1, 2, 3, 3, 2, 3, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB6026I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
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
    · exact ![24389, 29, 29]
    · exact ![961, 961, 31]
    · exact ![69343957]
    · exact ![68921, 1681]
    · exact ![79507, 43, 43]
    · exact ![2209, 2209, 47]
    · exact ![7890481, 53]
    · exact ![205379, 59, 59]
    · exact ![226981, 3721]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I29N1, I29N2, I31N0, I31N1, I31N2, I41N1, I43N1, I43N2, I47N0, I47N1, I47N2, I53N1, I59N1, I59N2, I61N1]
  Il := ![[I29N1, I29N2], [I31N0, I31N1, I31N2], [], [I41N1], [I43N1, I43N2], [I47N0, I47N1, I47N2], [I53N1], [I59N1, I59N2], [I61N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
