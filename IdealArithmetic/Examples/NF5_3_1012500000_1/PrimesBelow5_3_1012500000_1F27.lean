
import IdealArithmetic.Examples.NF5_3_1012500000_1.RI5_3_1012500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp1549 : Fact (Nat.Prime 1549) := {out := by norm_num}

def I1549N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1132117, 603960, -267311, 48893, -95893]] i)))

def SI1549N0: IdealEqSpanCertificate' Table ![![1132117, 603960, -267311, 48893, -95893]] 
 ![![1549, 0, 0, 0, 0], ![0, 1549, 0, 0, 0], ![0, 0, 1549, 0, 0], ![559, 1197, 1341, 1, 0], ![710, 123, 596, 0, 1]] where
  M :=![![![1132117, 603960, -267311, 48893, -95893], ![-575358, -306278, 136706, -24471, 48893], ![293358, 158037, -67261, 13575, -24471], ![-171150, -91303, 40391, -7423, 14498], ![-133104, -69552, 33213, -5043, 11600]]]
  hmulB := by decide  
  f := ![![![339745, 567830, -180351, 82463, -68333]], ![![-409998, -685250, 217646, -99501, 82463]], ![![494778, 826947, -262663, 120045, -99501]], ![![233893, 390916, -124171, 56740, -47031]], ![![313460, 523900, -166403, 76066, -63041]]]
  g := ![![![27040, -29778, -5604, 48893, -95893], ![-13951, 14830, 2461, -24471, 48893], ![6507, -8445, -2380, 13575, -24471], ![-4077, 4526, 874, -7423, 14498], ![-3583, 2931, -76, -5043, 11600]]]
  hle1 := by decide   
  hle2 := by decide  


def P1549P0 : CertificateIrreducibleZModOfList' 1549 3 2 10 [1516, 1187, 964, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [379, 1237, 1063], [206, 311, 486], [0, 1]]
 g := ![![[387, 636, 461], [1063, 818], [1319, 987, 903], [960, 230, 1071], [608, 1020], [611, 1203], [1364, 1051], [1317, 356], [234, 1445], [1]], ![[1284, 541, 688, 1381], [206, 746], [1301, 1150, 1436, 359], [752, 920, 1224, 1392], [1353, 518], [72, 1369], [1205, 623], [1185, 1052], [186, 73], [1108, 682, 1448, 487]], ![[912, 1314, 1126, 1459], [1313, 207], [617, 244, 660, 1308], [1241, 1266, 746, 1217], [867, 1424], [1039, 1118], [62, 202], [92, 610], [641, 313], [1200, 247, 955, 1062]]]
 h' := ![![[379, 1237, 1063], [242, 1194, 944], [155, 944, 698], [700, 1264, 1137], [214, 983, 842], [1309, 859, 1074], [457, 268, 399], [1028, 993, 1283], [1066, 1385, 919], [33, 362, 585], [0, 1]], ![[206, 311, 486], [983, 234, 1414], [1329, 70, 1487], [552, 1358, 1084], [575, 1392, 984], [288, 26, 186], [1314, 168, 37], [988, 1441, 61], [1325, 1056, 1498], [1271, 1302, 1356], [379, 1237, 1063]], ![[0, 1], [699, 121, 740], [366, 535, 913], [11, 476, 877], [256, 723, 1272], [1230, 664, 289], [1020, 1113, 1113], [372, 664, 205], [653, 657, 681], [135, 1434, 1157], [206, 311, 486]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [487, 1533], []]
 b := ![[], [1056, 1389, 1141], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI1549N0 : CertifiedPrimeIdeal' SI1549N0 1549 where
  n := 3
  hpos := by decide
  P := [1516, 1187, 964, 1]
  hirr := P1549P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![162196, 96570, -553046, -1219102, 1290046]
  a := ![0, -1, -4, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-151254, 839694, 558680, -1219102, 1290046]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI1549N0 : Ideal.IsPrime I1549N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI1549N0 B_one_repr
lemma NI1549N0 : Nat.card (O ⧸ I1549N0) = 3716672149 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI1549N0

def I1549N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![339745, 567830, -180351, 82463, -68333]] i)))

def SI1549N1: IdealEqSpanCertificate' Table ![![339745, 567830, -180351, 82463, -68333]] 
 ![![1549, 0, 0, 0, 0], ![0, 1549, 0, 0, 0], ![1089, 1251, 1, 0, 0], ![102, 1278, 0, 1, 0], ![655, 330, 0, 0, 1]] where
  M :=![![![339745, 567830, -180351, 82463, -68333], ![-409998, -685250, 217646, -99501, 82463], ![494778, 826947, -262663, 120045, -99501], ![-346890, -579763, 184151, -84205, 69758], ![-127344, -212862, 67653, -30693, 25568]]]
  hmulB := by decide  
  f := ![![![1132117, 603960, -267311, 48893, -95893]], ![![-575358, -306278, 136706, -24471, 48893]], ![![331437, 177351, -77566, 14619, -27945]], ![![-400260, -212983, 95213, -16975, 34034]], ![![356059, 190092, -83888, 15458, -30125]]]
  g := ![![![150477, 92543, -180351, 82463, -68333], ![-181595, -111692, 217646, -99501, 82463], ![219150, 134820, -262663, 120045, -99501], ![-153641, -94486, 184151, -84205, 69758], ![-56435, -34899, 67653, -30693, 25568]]]
  hle1 := by decide   
  hle2 := by decide  


def P1549P1 : CertificateIrreducibleZModOfList' 1549 2 2 10 [1541, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1468, 1548], [0, 1]]
 g := ![![[958, 1167], [1490], [906, 613], [1411, 1008], [89], [650], [1009], [1213], [1268], [1468, 1]], ![[920, 382], [1490], [821, 936], [311, 541], [89], [650], [1009], [1213], [1268], [1387, 1548]]]
 h' := ![![[1468, 1548], [246, 1211], [1052, 976], [445, 1343], [1196, 455], [22, 315], [1379, 1416], [1498, 1235], [975, 955], [901, 373], [0, 1]], ![[0, 1], [1291, 338], [995, 573], [92, 206], [1517, 1094], [840, 1234], [1309, 133], [599, 314], [1070, 594], [119, 1176], [1468, 1548]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1350]]
 b := ![[], [230, 675]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI1549N1 : CertifiedPrimeIdeal' SI1549N1 1549 where
  n := 2
  hpos := by decide
  P := [1541, 81, 1]
  hirr := P1549P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![431, -9020, 4445, 2663, 461]
  a := ![3, -64, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3495, -5891, 4445, 2663, 461]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI1549N1 : Ideal.IsPrime I1549N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI1549N1 B_one_repr
lemma NI1549N1 : Nat.card (O ⧸ I1549N1) = 2399401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI1549N1
def MulI1549N0 : IdealMulLeCertificate' Table 
  ![![1132117, 603960, -267311, 48893, -95893]] ![![339745, 567830, -180351, 82463, -68333]]
  ![![1549, 0, 0, 0, 0]] where
 M := ![![![1549, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC1549 : ContainsPrimesAboveP 1549 ![I1549N0, I1549N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI1549N0
    exact isPrimeI1549N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 1549 (by decide) (𝕀 ⊙ MulI1549N0)
instance hp1553 : Fact (Nat.Prime 1553) := {out := by norm_num}

def I1553N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3335, -5573, 1767, -810, 670]] i)))

def SI1553N0: IdealEqSpanCertificate' Table ![![-3335, -5573, 1767, -810, 670]] 
 ![![1553, 0, 0, 0, 0], ![0, 1553, 0, 0, 0], ![463, 144, 1, 0, 0], ![304, 1467, 0, 1, 0], ![815, 150, 0, 0, 1]] where
  M :=![![![-3335, -5573, 1767, -810, 670], ![4020, 6715, -2142, 972, -810], ![-4860, -8130, 2557, -1188, 972], ![3402, 5685, -1805, 829, -684], ![1242, 2067, -681, 294, -251]]]
  hmulB := by decide  
  f := ![![![-1987, -1073, 465, -78, 172]], ![![1032, 593, -288, -72, -78]], ![![-497, -265, 112, -30, 44]], ![![586, 350, -181, -83, -40]], ![![-943, -506, 216, -48, 83]]]
  g := ![![![-722, 533, 1767, -810, 670], ![876, -637, -2142, 972, -810], ![-1043, 786, 2557, -1188, 972], ![737, -546, -1805, 829, -684], ![278, -189, -681, 294, -251]]]
  hle1 := by decide   
  hle2 := by decide  


def P1553P0 : CertificateIrreducibleZModOfList' 1553 2 2 10 [1050, 689, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [864, 1552], [0, 1]]
 g := ![![[647, 1306], [929], [4], [736], [1054, 1186], [766], [872], [769], [36], [864, 1]], ![[0, 247], [929], [4], [736], [778, 367], [766], [872], [769], [36], [175, 1552]]]
 h' := ![![[864, 1552], [419, 1069], [562, 225], [1196, 1551], [589, 238], [977, 1231], [1296, 551], [1220, 741], [409, 174], [1305, 6], [0, 1]], ![[0, 1], [0, 484], [837, 1328], [1021, 2], [1225, 1315], [756, 322], [589, 1002], [55, 812], [104, 1379], [277, 1547], [864, 1552]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [654]]
 b := ![[], [59, 327]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI1553N0 : CertifiedPrimeIdeal' SI1553N0 1553 where
  n := 2
  hpos := by decide
  P := [1050, 689, 1]
  hirr := P1553P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2028, -1487, -1832, -1937, -1567]
  a := ![1, -3, -2, -1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1749, 2150, -1832, -1937, -1567]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI1553N0 : Ideal.IsPrime I1553N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI1553N0 B_one_repr
lemma NI1553N0 : Nat.card (O ⧸ I1553N0) = 2411809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI1553N0

def I1553N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-499, -1389, -1328, -657, -229]] i)))

def SI1553N1: IdealEqSpanCertificate' Table ![![-499, -1389, -1328, -657, -229]] 
 ![![1553, 0, 0, 0, 0], ![0, 1553, 0, 0, 0], ![1095, 1442, 1, 0, 0], ![1074, 514, 0, 1, 0], ![567, 545, 0, 0, 1]] where
  M :=![![![-499, -1389, -1328, -657, -229], ![-1374, -3934, -3800, -1875, -657], ![-3942, -11229, -10831, -5349, -1875], ![96, 270, 270, 143, 46], ![-3378, -9633, -9268, -4557, -1594]]]
  hmulB := by decide  
  f := ![![![6169, 10581, -3346, 1545, -1267]], ![![-7602, -12836, 4066, -1905, 1545]], ![![-2703, -4448, 1413, -678, 540]], ![![1746, 3062, -966, 437, -364]], ![![-417, -644, 206, -105, 80]]]
  g := ![![![1474, 1530, -1328, -657, -229], ![4215, 4377, -3800, -1875, -657], ![12018, 12478, -10831, -5349, -1875], ![-306, -314, 270, 143, 46], ![10266, 10667, -9268, -4557, -1594]]]
  hle1 := by decide   
  hle2 := by decide  


def P1553P1 : CertificateIrreducibleZModOfList' 1553 2 2 10 [862, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1472, 1552], [0, 1]]
 g := ![![[1227, 443], [1089], [1511], [380], [604, 801], [209], [1186], [118], [712], [1472, 1]], ![[1063, 1110], [1089], [1511], [380], [949, 752], [209], [1186], [118], [712], [1391, 1552]]]
 h' := ![![[1472, 1552], [762, 434], [896, 33], [825, 1102], [1160, 1303], [1167, 1438], [780, 849], [204, 1231], [554, 754], [1490, 1040], [0, 1]], ![[0, 1], [1327, 1119], [1329, 1520], [84, 451], [1221, 250], [1164, 115], [343, 704], [1438, 322], [47, 799], [1112, 513], [1472, 1552]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [665]]
 b := ![[], [654, 1109]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI1553N1 : CertifiedPrimeIdeal' SI1553N1 1553 where
  n := 2
  hpos := by decide
  P := [862, 81, 1]
  hirr := P1553P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3566, 7629, -2084, -9003, 2199]
  a := ![1, 19, 3, -1, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6895, 4148, -2084, -9003, 2199]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI1553N1 : Ideal.IsPrime I1553N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI1553N1 B_one_repr
lemma NI1553N1 : Nat.card (O ⧸ I1553N1) = 2411809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI1553N1

def I1553N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-205, -110, 49, -9, 17]] i)))

def SI1553N2: IdealEqSpanCertificate' Table ![![-205, -110, 49, -9, 17]] 
 ![![1553, 0, 0, 0, 0], ![1520, 1, 0, 0, 0], ![464, 0, 1, 0, 0], ![767, 0, 0, 1, 0], ![122, 0, 0, 0, 1]] where
  M :=![![![-205, -110, 49, -9, 17], ![102, 50, -22, 15, -9], ![-54, -33, 5, -15, 15], ![42, 45, -13, -25, -10], ![12, -6, 37, 87, -40]]]
  hmulB := by decide  
  f := ![![![-14933, -42044, -39643, -19767, -6811]], ![![-14642, -41226, -38874, -19383, -6679]], ![![-4538, -12779, -12053, -6009, -2071]], ![![-7373, -20759, -19574, -9760, -3363]], ![![-1238, -3488, -3293, -1641, -566]]]
  g := ![![![96, -110, 49, -9, 17], ![-49, 50, -22, 15, -9], ![37, -33, 5, -15, 15], ![-27, 45, -13, -25, -10], ![-45, -6, 37, 87, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI1553N2 : Nat.card (O ⧸ I1553N2) = 1553 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI1553N2)

lemma isPrimeI1553N2 : Ideal.IsPrime I1553N2 := prime_ideal_of_norm_prime hp1553.out _ NI1553N2
def MulI1553N0 : IdealMulLeCertificate' Table 
  ![![-3335, -5573, 1767, -810, 670]] ![![-499, -1389, -1328, -657, -229]]
  ![![14933, 42044, 39643, 19767, 6811]] where
 M := ![![![14933, 42044, 39643, 19767, 6811]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI1553N1 : IdealMulLeCertificate' Table 
  ![![14933, 42044, 39643, 19767, 6811]] ![![-205, -110, 49, -9, 17]]
  ![![1553, 0, 0, 0, 0]] where
 M := ![![![-1553, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC1553 : ContainsPrimesAboveP 1553 ![I1553N0, I1553N1, I1553N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI1553N0
    exact isPrimeI1553N1
    exact isPrimeI1553N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 1553 (by decide) (𝕀 ⊙ MulI1553N0 ⊙ MulI1553N1)


lemma PB1556I27_primes (p : ℕ) :
  p ∈ Set.range ![1549, 1553] ↔ Nat.Prime p ∧ 1543 < p ∧ p ≤ 1555 := by
  rw [← List.mem_ofFn']
  convert primes_range 1543 1555 (by omega)

def PB1556I27 : PrimesBelowBoundCertificateInterval O 1543 1555 1556 where
  m := 2
  g := ![2, 3]
  P := ![1549, 1553]
  hP := PB1556I27_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I1549N0, I1549N1]
    · exact ![I1553N0, I1553N1, I1553N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC1549
    · exact PBC1553
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![3716672149, 2399401]
    · exact ![2411809, 2411809, 1553]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI1549N0
      exact NI1549N1
    · dsimp ; intro j
      fin_cases j
      exact NI1553N0
      exact NI1553N1
      exact NI1553N2
  β := ![I1553N2]
  Il := ![[], [I1553N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
