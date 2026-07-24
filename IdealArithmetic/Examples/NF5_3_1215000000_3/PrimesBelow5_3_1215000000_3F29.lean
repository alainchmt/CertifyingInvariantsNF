
import IdealArithmetic.Examples.NF5_3_1215000000_3.RI5_3_1215000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp1667 : Fact (Nat.Prime 1667) := {out := by norm_num}

def I1667N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![140816, -85870, -12349, -10341, 22085]] i)))

def SI1667N0: IdealEqSpanCertificate' Table ![![140816, -85870, -12349, -10341, 22085]] 
 ![![1667, 0, 0, 0, 0], ![0, 1667, 0, 0, 0], ![0, 0, 1667, 0, 0], ![549, 441, 888, 1, 0], ![1293, 1261, 500, 0, 1]] where
  M :=![![![140816, -85870, -12349, -10341, 22085], ![-265020, 160893, 23152, 19472, -41364], ![496368, -302704, -43507, -36424, 77888], ![-334818, 203140, 29272, 24645, -52166], ![338427, -206718, -29669, -24791, 53248]]]
  hmulB := by decide  
  f := ![![![-638, 66, 309, -5, -141]], ![![1692, -465, -488, 336, -20]], ![![240, 848, -1217, -1016, 1344]], ![![360, 351, -673, -454, 663]], ![![861, -47, -496, -54, 279]]]
  g := ![![![-13640, -14022, -1123, -10341, 22085], ![25512, 26235, 2048, 19472, -41364], ![-48120, -49464, -3985, -36424, 77888], ![32145, 33063, 2536, 24645, -52166], ![-32934, -33845, -2783, -24791, 53248]]]
  hle1 := by decide   
  hle2 := by decide  


def P1667P0 : CertificateIrreducibleZModOfList' 1667 3 2 10 [332, 110, 908, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1290, 1044, 1309], [1136, 622, 358], [0, 1]]
 g := ![![[207, 1438, 569], [346, 1034, 932], [1438, 1552], [1211, 395], [1584, 1188], [955, 1466], [307, 462], [735, 120, 1017], [1101, 966], [1]], ![[1334, 47, 72, 1623], [594, 1507, 1267, 273], [1565, 1255], [762, 1303], [1150, 699], [823, 536], [726, 616], [1280, 1485, 1387, 1624], [1563, 1331], [572, 1418, 1244, 1463]], ![[70, 965, 466, 671], [125, 640, 456, 229], [524, 1626], [549, 1590], [1181, 359], [1189, 1652], [896, 1269], [1297, 1538, 1530, 549], [961, 647], [1501, 53, 1008, 204]]]
 h' := ![![[1290, 1044, 1309], [151, 247, 1150], [227, 951, 1371], [1571, 1011, 1499], [1033, 147, 1139], [1484, 1247, 1143], [59, 858, 1568], [1029, 370, 1358], [1410, 1292, 809], [1335, 1557, 759], [0, 1]], ![[1136, 622, 358], [1524, 863, 82], [58, 1624, 535], [203, 1405, 326], [406, 804, 701], [1128, 1646, 1134], [1096, 1121, 1332], [217, 1499, 407], [109, 549, 654], [1549, 427, 1376], [1290, 1044, 1309]], ![[0, 1], [609, 557, 435], [1289, 759, 1428], [1498, 918, 1509], [1068, 716, 1494], [631, 441, 1057], [1275, 1355, 434], [480, 1465, 1569], [1536, 1493, 204], [415, 1350, 1199], [1136, 622, 358]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1378, 94], []]
 b := ![[], [621, 1208, 1332], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI1667N0 : CertifiedPrimeIdeal' SI1667N0 1667 where
  n := 3
  hpos := by decide
  P := [332, 110, 908, 1]
  hirr := P1667P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20640622, -228268, 5639609, 1262404, 1636453]
  a := ![0, 4, 9, -4, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1697441, -1571995, -1159929, 1262404, 1636453]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI1667N0 : Ideal.IsPrime I1667N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI1667N0 B_one_repr
lemma NI1667N0 : Nat.card (O ⧸ I1667N0) = 4632407963 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI1667N0

def I1667N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![773, 192, -92, -180, -214]] i)))

def SI1667N1: IdealEqSpanCertificate' Table ![![773, 192, -92, -180, -214]] 
 ![![1667, 0, 0, 0, 0], ![599, 1, 0, 0, 0], ![1271, 0, 1, 0, 0], ![779, 0, 0, 1, 0], ![820, 0, 0, 0, 1]] where
  M :=![![![773, 192, -92, -180, -214], ![2568, 647, -304, -612, -720], ![8640, 2156, -1009, -2048, -2448], ![13404, 3292, -1618, -3151, -3736], ![16170, 4040, -1918, -3854, -4555]]]
  hmulB := by decide  
  f := ![![![34899475, -21234000, -3054256, -2563192, 5460570]], ![![12501055, -7606057, -1094040, -918140, 1955986]], ![![26682823, -16234716, -2335169, -1959720, 4174946]], ![![16259119, -9892588, -1422930, -1194151, 2543994]], ![![17217482, -10475688, -1506802, -1264538, 2693945]]]
  g := ![![![191, 192, -92, -180, -214], ![641, 647, -304, -612, -720], ![2161, 2156, -1009, -2048, -2448], ![3369, 3292, -1618, -3151, -3736], ![4062, 4040, -1918, -3854, -4555]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI1667N1 : Nat.card (O ⧸ I1667N1) = 1667 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI1667N1)

lemma isPrimeI1667N1 : Ideal.IsPrime I1667N1 := prime_ideal_of_norm_prime hp1667.out _ NI1667N1

def I1667N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![80, -58, -1, -11, 15]] i)))

def SI1667N2: IdealEqSpanCertificate' Table ![![80, -58, -1, -11, 15]] 
 ![![1667, 0, 0, 0, 0], ![959, 1, 0, 0, 0], ![503, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![892, 0, 0, 0, 1]] where
  M :=![![![80, -58, -1, -11, 15], ![-180, 105, 24, 28, -44], ![528, -228, -127, -40, 112], ![-582, 224, 138, -29, -58], ![393, -206, -45, 27, 16]]]
  hmulB := by decide  
  f := ![![![144934, 35166, -17743, -34787, -41071]], ![![83674, 20303, -10243, -20083, -23711]], ![![44734, 10858, -5474, -10735, -12675]], ![![5632, 1374, -685, -1348, -1593]], ![![79433, 19282, -9719, -19061, -22506]]]
  g := ![![![26, -58, -1, -11, 15], ![-45, 105, 24, 28, -44], ![111, -228, -127, -40, 112], ![-139, 224, 138, -29, -58], ![123, -206, -45, 27, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI1667N2 : Nat.card (O ⧸ I1667N2) = 1667 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI1667N2)

lemma isPrimeI1667N2 : Ideal.IsPrime I1667N2 := prime_ideal_of_norm_prime hp1667.out _ NI1667N2
def MulI1667N0 : IdealMulLeCertificate' Table 
  ![![140816, -85870, -12349, -10341, 22085]] ![![773, 192, -92, -180, -214]]
  ![![144934, 35166, -17743, -34787, -41071]] where
 M := ![![![144934, 35166, -17743, -34787, -41071]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI1667N1 : IdealMulLeCertificate' Table 
  ![![144934, 35166, -17743, -34787, -41071]] ![![80, -58, -1, -11, 15]]
  ![![1667, 0, 0, 0, 0]] where
 M := ![![![1667, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC1667 : ContainsPrimesAboveP 1667 ![I1667N0, I1667N1, I1667N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI1667N0
    exact isPrimeI1667N1
    exact isPrimeI1667N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 1667 (by decide) (𝕀 ⊙ MulI1667N0 ⊙ MulI1667N1)
instance hp1669 : Fact (Nat.Prime 1669) := {out := by norm_num}

def I1669N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![367, -179, -7, 164, -120]] i)))

def SI1669N0: IdealEqSpanCertificate' Table ![![367, -179, -7, 164, -120]] 
 ![![1669, 0, 0, 0, 0], ![0, 1669, 0, 0, 0], ![655, 1033, 1, 0, 0], ![1334, 29, 0, 1, 0], ![1003, 871, 0, 0, 1]] where
  M :=![![![367, -179, -7, 164, -120], ![1440, 76, -987, -254, 656], ![-7872, 1363, 3208, -662, -1016], ![5376, -2547, -195, 2319, -1652], ![1380, 1003, -2091, -1318, 1975]]]
  hmulB := by decide  
  f := ![![![7147, 3245, 475, -460, -784]], ![![9408, 7298, 1029, -618, -1840]], ![![8641, 5796, 824, -564, -1448]], ![![5882, 2725, 398, -379, -660]], ![![9217, 5764, 823, -600, -1433]]]
  g := ![![![-56, 64, -7, 164, -120], ![197, 273, -987, -254, 656], ![-124, -1443, 3208, -662, -1016], ![-781, 941, -195, 2319, -1652], ![688, 287, -2091, -1318, 1975]]]
  hle1 := by decide   
  hle2 := by decide  


def P1669P0 : CertificateIrreducibleZModOfList' 1669 2 2 10 [961, 1240, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [429, 1668], [0, 1]]
 g := ![![[432, 851], [1609], [718, 76], [1149], [1554], [1633], [240], [262, 1035], [1405], [429, 1]], ![[0, 818], [1609], [1611, 1593], [1149], [1554], [1633], [240], [323, 634], [1405], [858, 1668]]]
 h' := ![![[429, 1668], [1629, 323], [968, 1004], [630, 788], [245, 416], [1121, 81], [774, 1320], [237, 525], [692, 52], [1643, 1159], [0, 1]], ![[0, 1], [0, 1346], [1082, 665], [1544, 881], [126, 1253], [821, 1588], [1263, 349], [147, 1144], [1303, 1617], [1492, 510], [429, 1668]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1487]]
 b := ![[], [326, 1578]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI1669N0 : CertifiedPrimeIdeal' SI1669N0 1669 where
  n := 2
  hpos := by decide
  P := [961, 1240, 1]
  hirr := P1669P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2232002, -319352, 442287, 290029, 289170]
  a := ![3, -4, 59, -65, -178]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-580507, -429886, 442287, 290029, 289170]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI1669N0 : Ideal.IsPrime I1669N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI1669N0 B_one_repr
lemma NI1669N0 : Nat.card (O ⧸ I1669N0) = 2785561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI1669N0

def I1669N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22729, 13583, 2055, -1352, -3190]] i)))

def SI1669N1: IdealEqSpanCertificate' Table ![![22729, 13583, 2055, -1352, -3190]] 
 ![![1669, 0, 0, 0, 0], ![0, 1669, 0, 0, 0], ![1219, 802, 1, 0, 0], ![198, 1125, 0, 1, 0], ![328, 620, 0, 0, 1]] where
  M :=![![![22729, 13583, 2055, -1352, -3190], ![38280, 22946, 3527, -2270, -5408], ![64896, 38669, 5854, -3762, -9080], ![35340, 21243, 3173, -2091, -4820], ![56478, 34017, 5345, -3272, -7983]]]
  hmulB := by decide  
  f := ![![![38168977, -23223353, -3340403, -2803324, 5972158]], ![![-71665896, 43604056, 6271927, 5263510, -11213296]], ![![-6479033, 3942070, 567021, 475854, -1013750]], ![![-43832934, 26669501, 3836092, 3219315, -6858376]], ![![-19066262, 11600585, 1668607, 1400324, -2983227]]]
  g := ![![![-700, 1117, 2055, -1352, -3190], ![-1221, 1858, 3527, -2270, -5408], ![-2006, 3119, 5854, -3762, -9080], ![-1101, 1688, 3173, -2091, -4820], ![-1913, 2623, 5345, -3272, -7983]]]
  hle1 := by decide   
  hle2 := by decide  


def P1669P1 : CertificateIrreducibleZModOfList' 1669 2 2 10 [507, 1338, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [331, 1668], [0, 1]]
 g := ![![[1484, 530], [1492], [768, 110], [1271], [144], [345], [1211], [1637, 1364], [1644], [331, 1]], ![[0, 1139], [1492], [460, 1559], [1271], [144], [345], [1211], [822, 305], [1644], [662, 1668]]]
 h' := ![![[331, 1668], [1602, 1049], [1170, 850], [677, 945], [260, 1003], [907, 12], [401, 201], [1203, 172], [705, 1318], [752, 569], [0, 1]], ![[0, 1], [0, 620], [459, 819], [1369, 724], [122, 666], [1541, 1657], [172, 1468], [1389, 1497], [1354, 351], [494, 1100], [331, 1668]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [554]]
 b := ![[], [54, 277]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI1669N1 : CertifiedPrimeIdeal' SI1669N1 1669 where
  n := 2
  hpos := by decide
  P := [507, 1338, 1]
  hirr := P1669P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16745, -1082, 11406, -3804, -18982]
  a := ![1, 1, 6, -5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4159, 4134, 11406, -3804, -18982]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI1669N1 : Ideal.IsPrime I1669N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI1669N1 B_one_repr
lemma NI1669N1 : Nat.card (O ⧸ I1669N1) = 2785561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI1669N1

def I1669N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4222, -2604, -347, -333, 673]] i)))

def SI1669N2: IdealEqSpanCertificate' Table ![![4222, -2604, -347, -333, 673]] 
 ![![1669, 0, 0, 0, 0], ![1503, 1, 0, 0, 0], ![817, 0, 1, 0, 0], ![1134, 0, 0, 1, 0], ![696, 0, 0, 0, 1]] where
  M :=![![![4222, -2604, -347, -333, 673], ![-8076, 4881, 754, 652, -1332], ![15984, -9306, -1751, -1156, 2608], ![-11610, 6558, 1342, 531, -1646], ![10911, -6544, -959, -567, 1502]]]
  hmulB := by decide  
  f := ![![![-271708160, -162286404, -24604575, 16161593, 38258865]], ![![-244958940, -146309575, -22182295, 14570511, 34492343]], ![![-133469936, -79719194, -12086390, 7938985, 18793725]], ![![-184866930, -110417694, -16740652, 10996153, 26030868]], ![![-113715657, -67920316, -10297537, 6763973, 16012152]]]
  g := ![![![2463, -2604, -347, -333, 673], ![-4657, 4881, 754, 652, -1332], ![8945, -9306, -1751, -1156, 2608], ![-6244, 6558, 1342, 531, -1646], ![6128, -6544, -959, -567, 1502]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI1669N2 : Nat.card (O ⧸ I1669N2) = 1669 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI1669N2)

lemma isPrimeI1669N2 : Ideal.IsPrime I1669N2 := prime_ideal_of_norm_prime hp1669.out _ NI1669N2
def MulI1669N0 : IdealMulLeCertificate' Table 
  ![![367, -179, -7, 164, -120]] ![![22729, 13583, 2055, -1352, -3190]]
  ![![53551, 8756, -39154, -13804, 28342]] where
 M := ![![![53551, 8756, -39154, -13804, 28342]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI1669N1 : IdealMulLeCertificate' Table 
  ![![53551, 8756, -39154, -13804, 28342]] ![![4222, -2604, -347, -333, 673]]
  ![![1669, 0, 0, 0, 0]] where
 M := ![![![-954668, -8338324, 10873535, 9738615, -12445733]]]
 hmul := by decide  
 g := ![![![![-572, -4996, 6515, 5835, -7457]]]]
 hle2 := by decide  


def PBC1669 : ContainsPrimesAboveP 1669 ![I1669N0, I1669N1, I1669N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI1669N0
    exact isPrimeI1669N1
    exact isPrimeI1669N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 1669 (by decide) (𝕀 ⊙ MulI1669N0 ⊙ MulI1669N1)
instance hp1693 : Fact (Nat.Prime 1693) := {out := by norm_num}

def I1693N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![757, 180, -98, -174, -202]] i)))

def SI1693N0: IdealEqSpanCertificate' Table ![![757, 180, -98, -174, -202]] 
 ![![1693, 0, 0, 0, 0], ![0, 1693, 0, 0, 0], ![374, 1108, 1, 0, 0], ![1043, 68, 0, 1, 0], ![601, 1448, 0, 0, 1]] where
  M :=![![![757, 180, -98, -174, -202], ![2424, 631, -280, -600, -696], ![8352, 2048, -953, -1952, -2400], ![13188, 3160, -1684, -3053, -3556], ![15450, 3932, -1786, -3746, -4427]]]
  hmulB := by decide  
  f := ![![![26317, -15092, -2166, -1922, 3890]], ![![-46680, 29963, 4312, 3448, -7688]], ![![-24682, 16244, 2339, 1828, -4164]], ![![14303, -8072, -1158, -1043, 2082]], ![![-30545, 20248, 2916, 2264, -5189]]]
  g := ![![![201, 244, -98, -174, -202], ![680, 803, -280, -600, -696], ![2270, 2756, -953, -1952, -2400], ![3523, 4268, -1684, -3053, -3556], ![4283, 5108, -1786, -3746, -4427]]]
  hle1 := by decide   
  hle2 := by decide  


def P1693P0 : CertificateIrreducibleZModOfList' 1693 2 2 10 [664, 740, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [953, 1692], [0, 1]]
 g := ![![[970, 1140], [1259], [664, 121], [1360, 795], [1301, 508], [1361], [1582], [372, 139], [944], [953, 1]], ![[484, 553], [1259], [853, 1572], [531, 898], [1227, 1185], [1361], [1582], [785, 1554], [944], [213, 1692]]]
 h' := ![![[953, 1692], [43, 765], [977, 433], [1022, 11], [1259, 725], [967, 371], [1024, 754], [170, 1364], [1017, 124], [390, 97], [0, 1]], ![[0, 1], [1098, 928], [534, 1260], [1347, 1682], [1440, 968], [693, 1322], [61, 939], [1531, 329], [679, 1569], [1409, 1596], [953, 1692]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [989]]
 b := ![[], [121, 1341]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI1693N0 : CertifiedPrimeIdeal' SI1693N0 1693 where
  n := 2
  hpos := by decide
  P := [664, 740, 1]
  hirr := P1693P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-447614, -61244, 70453, 81237, 141450]
  a := ![1, -8, -30, 18, 87]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-116089, -170388, 70453, 81237, 141450]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI1693N0 : Ideal.IsPrime I1693N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI1693N0 B_one_repr
lemma NI1693N0 : Nat.card (O ⧸ I1693N0) = 2866249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI1693N0

def I1693N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-301, -102, 250, -38, -72]] i)))

def SI1693N1: IdealEqSpanCertificate' Table ![![-301, -102, 250, -38, -72]] 
 ![![1693, 0, 0, 0, 0], ![152, 1, 0, 0, 0], ![598, 0, 1, 0, 0], ![187, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-301, -102, 250, -38, -72], ![864, -85, -314, 356, -152], ![1824, 42, -1405, -932, 1424], ![-8976, 1430, 3958, -159, -1788], ![6492, -1662, -2132, 708, 515]]]
  hmulB := by decide  
  f := ![![![-5046097, -3051210, -479330, 281178, 695552]], ![![-457976, -276961, -43526, 25500, 63112]], ![![-1790350, -1082758, -170181, 99664, 246704]], ![![-561031, -339596, -53508, 31079, 77188]], ![![-15243, -9640, -1702, 634, 1931]]]
  g := ![![![-75, -102, 250, -38, -72], ![80, -85, -314, 356, -152], ![594, 42, -1405, -932, 1424], ![-1511, 1430, 3958, -159, -1788], ![827, -1662, -2132, 708, 515]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI1693N1 : Nat.card (O ⧸ I1693N1) = 1693 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI1693N1)

lemma isPrimeI1693N1 : Ideal.IsPrime I1693N1 := prime_ideal_of_norm_prime hp1693.out _ NI1693N1

def I1693N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6706, -3993, -600, 405, 949]] i)))

def SI1693N2: IdealEqSpanCertificate' Table ![![-6706, -3993, -600, 405, 949]] 
 ![![1693, 0, 0, 0, 0], ![586, 1, 0, 0, 0], ![283, 0, 1, 0, 0], ![1438, 0, 0, 1, 0], ![1246, 0, 0, 0, 1]] where
  M :=![![![-6706, -3993, -600, 405, 949], ![-11388, -6762, -1007, 698, 1620], ![-19440, -11473, -1678, 1226, 2792], ![-11058, -6395, -875, 765, 1642], ![-17493, -10191, -1430, 1171, 2566]]]
  hmulB := by decide  
  f := ![![![-1816, -1477, 3158, 2555, -3467]], ![![-604, -514, 1081, 884, -1194]], ![![-376, -228, 550, 415, -581]], ![![-1546, -1273, 2707, 2191, -2972]], ![![-1285, -1085, 2290, 1873, -2530]]]
  g := ![![![436, -3993, -600, 405, 949], ![717, -6762, -1007, 698, 1620], ![1144, -11473, -1678, 1226, 2792], ![495, -6395, -875, 765, 1642], ![873, -10191, -1430, 1171, 2566]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI1693N2 : Nat.card (O ⧸ I1693N2) = 1693 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI1693N2)

lemma isPrimeI1693N2 : Ideal.IsPrime I1693N2 := prime_ideal_of_norm_prime hp1693.out _ NI1693N2

def I1693N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-298, -239, -36, 17, 57]] i)))

def SI1693N3: IdealEqSpanCertificate' Table ![![-298, -239, -36, 17, 57]] 
 ![![1693, 0, 0, 0, 0], ![1540, 1, 0, 0, 0], ![293, 0, 1, 0, 0], ![482, 0, 0, 1, 0], ![345, 0, 0, 0, 1]] where
  M :=![![![-298, -239, -36, 17, 57], ![-684, -294, -45, 42, 68], ![-816, -703, -106, 46, 168], ![-666, -253, -39, 41, 58], ![-753, -597, -90, 43, 142]]]
  hmulB := by decide  
  f := ![![![-664, 453, 174, -385, 1]], ![![-604, 412, 159, -350, 0]], ![![-104, 78, 26, -67, 1]], ![![-194, 133, 51, -113, 0]], ![![-129, 92, 36, -78, -3]]]
  g := ![![![207, -239, -36, 17, 57], ![249, -294, -45, 42, 68], ![610, -703, -106, 46, 168], ![213, -253, -39, 41, 58], ![517, -597, -90, 43, 142]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI1693N3 : Nat.card (O ⧸ I1693N3) = 1693 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI1693N3)

lemma isPrimeI1693N3 : Ideal.IsPrime I1693N3 := prime_ideal_of_norm_prime hp1693.out _ NI1693N3
def MulI1693N0 : IdealMulLeCertificate' Table 
  ![![757, 180, -98, -174, -202]] ![![-301, -102, 250, -38, -72]]
  ![![-649, -9726, 12392, 11300, -14334]] where
 M := ![![![-649, -9726, 12392, 11300, -14334]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI1693N1 : IdealMulLeCertificate' Table 
  ![![-649, -9726, 12392, 11300, -14334]] ![![-6706, -3993, -600, 405, 949]]
  ![![664, -453, -174, 385, -1]] where
 M := ![![![664, -453, -174, 385, -1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI1693N2 : IdealMulLeCertificate' Table 
  ![![664, -453, -174, 385, -1]] ![![-298, -239, -36, 17, 57]]
  ![![1693, 0, 0, 0, 0]] where
 M := ![![![-1693, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC1693 : ContainsPrimesAboveP 1693 ![I1693N0, I1693N1, I1693N2, I1693N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI1693N0
    exact isPrimeI1693N1
    exact isPrimeI1693N2
    exact isPrimeI1693N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 1693 (by decide) (𝕀 ⊙ MulI1693N0 ⊙ MulI1693N1 ⊙ MulI1693N2)
instance hp1697 : Fact (Nat.Prime 1697) := {out := by norm_num}

def I1697N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20, 6, 9, -1, -1]] i)))

def SI1697N0: IdealEqSpanCertificate' Table ![![-20, 6, 9, -1, -1]] 
 ![![1697, 0, 0, 0, 0], ![0, 1697, 0, 0, 0], ![1504, 491, 1, 0, 0], ![714, 699, 0, 1, 0], ![963, 320, 0, 0, 1]] where
  M :=![![![-20, 6, 9, -1, -1], ![12, -11, 4, 16, -4], ![48, -4, -59, 0, 64], ![-390, 32, 124, -3, 2], ![21, -70, -17, 67, 28]]]
  hmulB := by decide  
  f := ![![![1742, -966, -139, -127, 251]], ![![-3012, 1981, 292, 224, -508]], ![![676, -285, -39, -48, 76]], ![![-510, 411, 62, 39, -104]], ![![423, -176, -24, -30, 47]]]
  g := ![![![-7, -2, 9, -1, -1], ![-8, -7, 4, 16, -4], ![16, 5, -59, 0, 64], ![-110, -35, 124, -3, 2], ![-29, -28, -17, 67, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P1697P0 : CertificateIrreducibleZModOfList' 1697 2 2 10 [360, 1288, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [409, 1696], [0, 1]]
 g := ![![[79, 314], [1533], [1367], [647], [1674], [1653, 370], [757], [827, 1625], [1491], [409, 1]], ![[1230, 1383], [1533], [1367], [647], [1674], [253, 1327], [757], [228, 72], [1491], [818, 1696]]]
 h' := ![![[409, 1696], [1497, 953], [380, 1168], [1104, 1628], [551, 770], [567, 1483], [803, 1104], [952, 1133], [872, 933], [399, 615], [0, 1]], ![[0, 1], [964, 744], [1235, 529], [35, 69], [1536, 927], [1285, 214], [937, 593], [1068, 564], [644, 764], [778, 1082], [409, 1696]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1416]]
 b := ![[], [1156, 708]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI1697N0 : CertifiedPrimeIdeal' SI1697N0 1697 where
  n := 2
  hpos := by decide
  P := [360, 1288, 1]
  hirr := P1697P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-42867, 8694, 32360, 12997, -45046]
  a := ![-1, 11, 13, 5, -34]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8611, -6217, 32360, 12997, -45046]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI1697N0 : Ideal.IsPrime I1697N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI1697N0 B_one_repr
lemma NI1697N0 : Nat.card (O ⧸ I1697N0) = 2879809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI1697N0

def I1697N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1628, -4873, -2490, -1889, -1339]] i)))

def SI1697N1: IdealEqSpanCertificate' Table ![![-1628, -4873, -2490, -1889, -1339]] 
 ![![1697, 0, 0, 0, 0], ![0, 1697, 0, 0, 0], ![628, 631, 1, 0, 0], ![415, 1480, 0, 1, 0], ![443, 1135, 0, 0, 1]] where
  M :=![![![-1628, -4873, -2490, -1889, -1339], ![16068, -3568, -6451, -7658, -7556], ![90672, 9719, -18476, -28014, -30632], ![175758, 36573, -25165, -45279, -52250], ![206103, 39873, -31318, -54629, -62484]]]
  hmulB := by decide  
  f := ![![![1305866, -794617, -114232, -95963, 204353]], ![![-2452236, 1491950, 214721, 180242, -383852]], ![![-425852, 259045, 37329, 31308, -66680]], ![![-1821140, 1107958, 159489, 133860, -285079]], ![![-1297375, 789296, 113629, 95364, -203095]]]
  g := ![![![1732, 3466, -2490, -1889, -1339], ![6242, 14129, -6451, -7658, -7556], ![21738, 51795, -18476, -28014, -30632], ![34129, 83814, -25165, -45279, -52250], ![41382, 101103, -31318, -54629, -62484]]]
  hle1 := by decide   
  hle2 := by decide  


def P1697P1 : CertificateIrreducibleZModOfList' 1697 2 2 10 [241, 863, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [834, 1696], [0, 1]]
 g := ![![[1602, 169], [204], [1387], [1578], [1309], [963, 676], [822], [494, 1129], [1688], [834, 1]], ![[0, 1528], [204], [1387], [1578], [1309], [1343, 1021], [822], [245, 568], [1688], [1668, 1696]]]
 h' := ![![[834, 1696], [660, 1684], [657, 1357], [312, 305], [400, 1009], [406, 80], [566, 26], [1433, 212], [1663, 1162], [949, 1242], [0, 1]], ![[0, 1], [0, 13], [496, 340], [132, 1392], [194, 688], [943, 1617], [189, 1671], [56, 1485], [87, 535], [1607, 455], [834, 1696]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [291]]
 b := ![[], [1267, 994]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI1697N1 : CertifiedPrimeIdeal' SI1697N1 1697 where
  n := 2
  hpos := by decide
  P := [241, 863, 1]
  hirr := P1697P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3935, -22064, 2206, -8706, 14876]
  a := ![0, -16, -10, -18, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2573, -3190, 2206, -8706, 14876]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI1697N1 : Ideal.IsPrime I1697N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI1697N1 B_one_repr
lemma NI1697N1 : Nat.card (O ⧸ I1697N1) = 2879809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI1697N1

def I1697N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12976, 7775, 1186, -779, -1831]] i)))

def SI1697N2: IdealEqSpanCertificate' Table ![![12976, 7775, 1186, -779, -1831]] 
 ![![1697, 0, 0, 0, 0], ![575, 1, 0, 0, 0], ![290, 0, 1, 0, 0], ![339, 0, 0, 1, 0], ![1619, 0, 0, 0, 1]] where
  M :=![![![12976, 7775, 1186, -779, -1831], ![21972, 13110, 2009, -1290, -3116], ![37392, 22155, 3226, -2214, -5160], ![19974, 12281, 1967, -1289, -2870], ![32799, 19445, 2960, -1881, -4648]]]
  hmulB := by decide  
  f := ![![![143445326, -87276929, -12553800, -10535405, 22444221]], ![![48445334, -29475759, -4239755, -3558089, 7580015]], ![![24811340, -15096047, -2171396, -1822280, 3882114]], ![![28454856, -17312882, -2490263, -2089880, 4452197]], ![![137055473, -83389126, -11994584, -10066100, 21444429]]]
  g := ![![![-927, 7775, 1186, -779, -1831], ![-1542, 13110, 2009, -1290, -3116], ![-2671, 22155, 3226, -2214, -5160], ![-1490, 12281, 1967, -1289, -2870], ![-2265, 19445, 2960, -1881, -4648]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI1697N2 : Nat.card (O ⧸ I1697N2) = 1697 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI1697N2)

lemma isPrimeI1697N2 : Ideal.IsPrime I1697N2 := prime_ideal_of_norm_prime hp1697.out _ NI1697N2
def MulI1697N0 : IdealMulLeCertificate' Table 
  ![![-20, 6, 9, -1, -1]] ![![-1628, -4873, -2490, -1889, -1339]]
  ![![563155, 87077, -98707, -160386, -179510]] where
 M := ![![![563155, 87077, -98707, -160386, -179510]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI1697N1 : IdealMulLeCertificate' Table 
  ![![563155, 87077, -98707, -160386, -179510]] ![![12976, 7775, 1186, -779, -1831]]
  ![![1697, 0, 0, 0, 0]] where
 M := ![![![-3561395474, -2127016406, -322418121, 211906087, 501529683]]]
 hmul := by decide  
 g := ![![![![-2098642, -1253398, -189993, 124871, 295539]]]]
 hle2 := by decide  


def PBC1697 : ContainsPrimesAboveP 1697 ![I1697N0, I1697N1, I1697N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI1697N0
    exact isPrimeI1697N1
    exact isPrimeI1697N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 1697 (by decide) (𝕀 ⊙ MulI1697N0 ⊙ MulI1697N1)
instance hp1699 : Fact (Nat.Prime 1699) := {out := by norm_num}

def I1699N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11843, 2121, 481, -608, -246]] i)))

def SI1699N0: IdealEqSpanCertificate' Table ![![11843, 2121, 481, -608, -246]] 
 ![![1699, 0, 0, 0, 0], ![0, 1699, 0, 0, 0], ![0, 0, 1699, 0, 0], ![1580, 1120, 731, 1, 0], ![170, 1526, 1541, 0, 1]] where
  M :=![![![11843, 2121, 481, -608, -246], ![2952, 12686, 2353, 470, -2432], ![29184, 2403, 2018, -158, 1880], ![-12756, 10277, 3943, 3663, 900], ![12630, 1479, 3235, 2460, 3995]]]
  hmulB := by decide  
  f := ![![![2309, 423, -1955, -756, 1490]], ![![-17880, 2600, 7895, -930, -3024]], ![![36288, -12079, -7636, 9742, -3720]], ![![5992, -3086, 85, 2869, -2196]], ![![17056, -8576, -15, 7926, -5949]]]
  g := ![![![597, 623, 485, -608, -246], ![-192, 1882, 2005, 470, -2432], ![-24, -1583, -1636, -158, 1880], ![-3504, -3217, -2390, 3663, 900], ![-2680, -5209, -4680, 2460, 3995]]]
  hle1 := by decide   
  hle2 := by decide  


def P1699P0 : CertificateIrreducibleZModOfList' 1699 3 2 10 [1506, 587, 425, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1487, 1418, 1422], [1486, 280, 277], [0, 1]]
 g := ![![[844, 257, 80], [156, 1062, 579], [357, 857], [983, 1672], [1217, 1391], [924, 411, 681], [486, 1298], [430, 1398, 270], [1435, 531], [1]], ![[732, 672, 775, 802], [1523, 922, 45, 917], [80, 1523], [1237, 1324], [1333, 1242], [19, 1280, 1173, 1445], [771, 1487], [997, 845, 1435, 4], [518, 1019], [765, 1440, 1217, 557]], ![[847, 584, 562, 1631], [226, 349, 938, 1508], [744, 829], [1664, 763], [1174, 287], [49, 1447, 721, 1291], [216, 1403], [1629, 163, 845, 1497], [1605, 988], [184, 1293, 1359, 1142]]]
 h' := ![![[1487, 1418, 1422], [1225, 92, 1562], [1274, 1399, 616], [907, 1386, 1464], [990, 1563, 1013], [1636, 1613, 428], [514, 1428, 437], [1438, 842, 1022], [1588, 287, 1410], [193, 1112, 1274], [0, 1]], ![[1486, 280, 277], [743, 550, 718], [1233, 1626, 730], [1536, 1550, 513], [647, 1238, 201], [1168, 814, 946], [812, 417, 343], [1660, 246, 257], [403, 1128, 986], [1395, 372, 1124], [1487, 1418, 1422]], ![[0, 1], [1427, 1057, 1118], [1169, 373, 353], [675, 462, 1421], [725, 597, 485], [1310, 971, 325], [902, 1553, 919], [523, 611, 420], [364, 284, 1002], [148, 215, 1000], [1486, 280, 277]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1442, 1349], []]
 b := ![[], [1388, 1311, 1618], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI1699N0 : CertifiedPrimeIdeal' SI1699N0 1699 where
  n := 3
  hpos := by decide
  P := [1506, 587, 425, 1]
  hirr := P1699P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13806103, 1554820, 6571187, -336784, -2787597]
  a := ![13, 8, 11, 2, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![583993, 2726678, 2677132, -336784, -2787597]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI1699N0 : Ideal.IsPrime I1699N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI1699N0 B_one_repr
lemma NI1699N0 : Nat.card (O ⧸ I1699N0) = 4904335099 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI1699N0

def I1699N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1801, -1078, -164, 108, 254]] i)))

def SI1699N1: IdealEqSpanCertificate' Table ![![-1801, -1078, -164, 108, 254]] 
 ![![1699, 0, 0, 0, 0], ![371, 1, 0, 0, 0], ![1677, 0, 1, 0, 0], ![1347, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![-1801, -1078, -164, 108, 254], ![-3048, -1819, -278, 180, 432], ![-5184, -3074, -451, 308, 720], ![-2796, -1702, -266, 179, 400], ![-4554, -2702, -410, 266, 647]]]
  hmulB := by decide  
  f := ![![![-2268775, 1380378, 198556, 166640, -354978]], ![![-492911, 299899, 43138, 36204, -77122]], ![![-2244105, 1365368, 196397, 164828, -351118]], ![![-1795563, 1092464, 157142, 131883, -280938]], ![![-35262, 21454, 3086, 2590, -5517]]]
  g := ![![![307, -1078, -164, 108, 254], ![521, -1819, -278, 180, 432], ![859, -3074, -451, 308, 720], ![485, -1702, -266, 179, 400], ![772, -2702, -410, 266, 647]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI1699N1 : Nat.card (O ⧸ I1699N1) = 1699 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI1699N1)

lemma isPrimeI1699N1 : Ideal.IsPrime I1699N1 := prime_ideal_of_norm_prime hp1699.out _ NI1699N1

def I1699N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -139, 121, 16, -56]] i)))

def SI1699N2: IdealEqSpanCertificate' Table ![![5, -139, 121, 16, -56]] 
 ![![1699, 0, 0, 0, 0], ![1565, 1, 0, 0, 0], ![733, 0, 1, 0, 0], ![1606, 0, 0, 1, 0], ![1465, 0, 0, 0, 1]] where
  M :=![![![5, -139, 121, 16, -56], ![672, 54, -395, 130, 64], ![-768, 211, 50, -662, 520], ![-3456, 205, 2005, 505, -1356], ![3852, -709, -1631, 26, 781]]]
  hmulB := by decide  
  f := ![![![27467303, 16403939, 2486233, -1634704, -3868352]], ![![25328281, 15126477, 2292616, -1507402, -3567104]], ![![11896409, 7104728, 1076811, -708014, -1675432]], ![![25989182, 15521163, 2352429, -1546743, -3660188]], ![![23724953, 14168924, 2147478, -1411990, -3341307]]]
  g := ![![![109, -139, 121, 16, -56], ![-57, 54, -395, 130, 64], ![-39, 211, 50, -662, 520], ![-364, 205, 2005, 505, -1356], ![661, -709, -1631, 26, 781]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI1699N2 : Nat.card (O ⧸ I1699N2) = 1699 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI1699N2)

lemma isPrimeI1699N2 : Ideal.IsPrime I1699N2 := prime_ideal_of_norm_prime hp1699.out _ NI1699N2
def MulI1699N0 : IdealMulLeCertificate' Table 
  ![![11843, 2121, 481, -608, -246]] ![![-1801, -1078, -164, 108, 254]]
  ![![-27467303, -16403939, -2486233, 1634704, 3868352]] where
 M := ![![![-27467303, -16403939, -2486233, 1634704, 3868352]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI1699N1 : IdealMulLeCertificate' Table 
  ![![-27467303, -16403939, -2486233, 1634704, 3868352]] ![![5, -139, 121, 16, -56]]
  ![![1699, 0, 0, 0, 0]] where
 M := ![![![-1699, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC1699 : ContainsPrimesAboveP 1699 ![I1699N0, I1699N1, I1699N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI1699N0
    exact isPrimeI1699N1
    exact isPrimeI1699N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 1699 (by decide) (𝕀 ⊙ MulI1699N0 ⊙ MulI1699N1)


lemma PB1705I29_primes (p : ℕ) :
  p ∈ Set.range ![1667, 1669, 1693, 1697, 1699] ↔ Nat.Prime p ∧ 1663 < p ∧ p ≤ 1704 := by
  rw [← List.mem_ofFn']
  convert primes_range 1663 1704 (by omega)

def PB1705I29 : PrimesBelowBoundCertificateInterval O 1663 1704 1705 where
  m := 5
  g := ![3, 3, 4, 3, 3]
  P := ![1667, 1669, 1693, 1697, 1699]
  hP := PB1705I29_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I1667N0, I1667N1, I1667N2]
    · exact ![I1669N0, I1669N1, I1669N2]
    · exact ![I1693N0, I1693N1, I1693N2, I1693N3]
    · exact ![I1697N0, I1697N1, I1697N2]
    · exact ![I1699N0, I1699N1, I1699N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC1667
    · exact PBC1669
    · exact PBC1693
    · exact PBC1697
    · exact PBC1699
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![4632407963, 1667, 1667]
    · exact ![2785561, 2785561, 1669]
    · exact ![2866249, 1693, 1693, 1693]
    · exact ![2879809, 2879809, 1697]
    · exact ![4904335099, 1699, 1699]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI1667N0
      exact NI1667N1
      exact NI1667N2
    · dsimp ; intro j
      fin_cases j
      exact NI1669N0
      exact NI1669N1
      exact NI1669N2
    · dsimp ; intro j
      fin_cases j
      exact NI1693N0
      exact NI1693N1
      exact NI1693N2
      exact NI1693N3
    · dsimp ; intro j
      fin_cases j
      exact NI1697N0
      exact NI1697N1
      exact NI1697N2
    · dsimp ; intro j
      fin_cases j
      exact NI1699N0
      exact NI1699N1
      exact NI1699N2
  β := ![I1667N1, I1667N2, I1669N2, I1693N1, I1693N2, I1693N3, I1697N2, I1699N1, I1699N2]
  Il := ![[I1667N1, I1667N2], [I1669N2], [I1693N1, I1693N2, I1693N3], [I1697N2], [I1699N1, I1699N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
