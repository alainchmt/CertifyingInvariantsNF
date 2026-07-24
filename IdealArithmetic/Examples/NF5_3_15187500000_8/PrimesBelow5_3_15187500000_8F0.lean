
import IdealArithmetic.Examples.NF5_3_15187500000_8.RI5_3_15187500000_8
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11461, -11298, 2476, 4507, -4548]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![11461, -11298, 2476, 4507, -4548]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![11461, -11298, 2476, 4507, -4548], ![96761, 3536, -13370, 7376, 18069], ![-430907, 132331, 8235, -78766, 4059], ![-11955, -37262, 14411, 10508, -23253], ![144155, -23111, -10086, 19789, 10720]]]
  hmulB := by decide  
  f := ![![![1973, -926, 115, -741, 747]], ![![-6381, 3202, -32, 3046, -1485]], ![![24977, -12437, 1685, -9358, 10623]], ![![-11512, 5642, -83, 5389, -2673]], ![![20536, -10305, 1060, -8258, 7768]]]
  g := ![![![5751, -11298, 2476, 4507, -4548], ![35658, 3536, -13370, 7376, 18069], ![-178100, 132331, 8235, -78766, 4059], ![395, -37262, 14411, 10508, -23253], ![56823, -23111, -10086, 19789, 10720]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-201212387, 99769021, -6078217, 87282955, -61900965]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-201212387, 99769021, -6078217, 87282955, -61900965]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-201212387, 99769021, -6078217, 87282955, -61900965], ![1052366078, -521804524, 31789839, -456500828, 323749830], ![-5504006908, 2729103264, -166264855, 2387556726, -1693252314], ![2084552348, -1033603103, 62970087, -904247953, 641291544], ![-4052016442, 2009149242, -122403176, 1757704755, -1246562066]]]
  hmulB := by decide  
  f := ![![![484008, -215629, -77229, -346384, -153330]], ![![1398140, -622865, -223094, -1000593, -442911]], ![![8077338, -3598483, -1288870, -5780782, -2558868]], ![![2053418, -914808, -327650, -1469564, -650511]], ![![3811083, -1697835, -608111, -2727447, -1207310]]]
  g := ![![![-69655711, 99769021, -6078217, 87282955, -61900965], ![364308124, -521804524, 31789839, -456500828, 323749830], ![-1905377297, 2729103264, -166264855, 2387556726, -1693252314], ![721630402, -1033603103, 62970087, -904247953, 641291544], ![-1402727188, 2009149242, -122403176, 1757704755, -1246562066]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4600524, -295770, -474952, 494544, 594297]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![4600524, -295770, -474952, 494544, 594297]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![4600524, -295770, -474952, 494544, 594297], ![-14635899, 5811138, -176425, -3083546, 889335], ![-14872369, -13441985, 6524048, 2866060, -10139973], ![21715881, -3810863, -1405264, 3083199, 1426881], ![-6463033, 6273958, -1362591, -2511440, 2509226]]]
  hmulB := by decide  
  f := ![![![-272143679723, -40443412087, -7094456468, 34598669030, 30446095257]], ![![-463892448722, -68939295023, -12093114883, 58976425010, 51898003545]], ![![-925848412664, -137590808804, -24135747946, 117706656928, 103579363197]], ![![119315916332, 17731599832, 3110421579, -15169089645, -13348477512]], ![![159733820282, 23738124675, 4164067438, -20307572982, -17870233237]]]
  g := ![![![2685623, -295770, -474952, 494544, 594297], ![-10135306, 5811138, -176425, -3083546, 889335], ![-3977216, -13441985, 6524048, 2866060, -10139973], ![13466004, -3810863, -1405264, 3083199, 1426881], ![-5687200, 6273958, -1362591, -2511440, 2509226]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![11461, -11298, 2476, 4507, -4548]] ![![-201212387, 99769021, -6078217, 87282955, -61900965]]
  ![![-10207, 5660, -482, 5664, -3693]] where
 M := ![![![-10207, 5660, -482, 5664, -3693]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-10207, 5660, -482, 5664, -3693]] ![![-201212387, 99769021, -6078217, 87282955, -61900965]]
  ![![37434099384623, -18561299902533, 1130808011505, -16238358216104, 11516223817857]] where
 M := ![![![37434099384623, -18561299902533, 1130808011505, -16238358216104, 11516223817857]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![37434099384623, -18561299902533, 1130808011505, -16238358216104, 11516223817857]] ![![4600524, -295770, -474952, 494544, 594297]]
  ![![77785041369, -38194588931, 2219677638, -33873381546, 24153077169]] where
 M := ![![![77785041369, -38194588931, 2219677638, -33873381546, 24153077169]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![77785041369, -38194588931, 2219677638, -33873381546, 24153077169]] ![![4600524, -295770, -474952, 494544, 594297]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-7840226808998700, 5824825815745062, -1034119089225724, -2492753524772672, 2024405344221102]]]
 hmul := by decide  
 g := ![![![![-3920113404499350, 2912412907872531, -517059544612862, -1246376762386336, 1012202672110551]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13523, 5576, 2018, 9236, 4130]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-13523, 5576, 2018, 9236, 4130]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-13523, 5576, 2018, 9236, 4130], ![-75598, 32601, 11724, 53032, 23578], ![-430670, 189246, 67903, 305604, 135518], ![-107688, 48368, 17308, 77467, 34252], ![-187444, 84038, 30074, 134676, 59567]]]
  hmulB := by decide  
  f := ![![![-1203274317, 596630768, -36348470, 521962588, -370175230]], ![![1696667215, -841274387, 51252866, -735989124, 521962588]], ![![-11773724384, 5837875970, -355660269, 5107267364, -3622067778]], ![![3754199969, -1861480112, 113406746, -1628516377, 1154941826]], ![![-8478273635, 4203861778, -256111404, 3677749608, -2608255531]]]
  g := ![![![-12167, 5576, 2018, 9236, 4130], ![-69419, 32601, 11724, 53032, 23578], ![-398948, 189246, 67903, 305604, 135518], ![-100797, 48368, 17308, 77467, 34252], ![-175291, 84038, 30074, 134676, 59567]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, -1, 0, -2, 1]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![8, -1, 0, -2, 1]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![8, -1, 0, -2, 1], ![-17, 12, 0, 6, -7], ![127, -53, 5, -42, 25], ![-34, 18, -2, 17, -10], ![62, -34, 2, -32, 23]]]
  hmulB := by decide  
  f := ![![![-388, 173, 62, 278, 123]], ![![-877, 391, 140, 628, 278]], ![![-4581, 2041, 731, 3278, 1451]], ![![-1228, 547, 196, 879, 389]], ![![-2168, 966, 346, 1552, 687]]]
  g := ![![![3, -1, 0, -2, 1], ![-7, 12, 0, 6, -7], ![54, -53, 5, -42, 25], ![-15, 18, -2, 17, -10], ![26, -34, 2, -32, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1305, -194, -34, 166, 146]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![-1305, -194, -34, 166, 146]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-1305, -194, -34, 166, 146], ![-3144, -467, -82, 400, 352], ![-7580, -1124, -197, 964, 848], ![1144, 170, 30, -145, -128], ![1532, 228, 40, -194, -171]]]
  hmulB := by decide  
  f := ![![![-59, 30, -2, 26, -18]], ![![62, -31, 2, -28, 20]], ![![-582, 288, -17, 256, -180]], ![![208, -102, 6, -89, 64]], ![![-404, 200, -12, 174, -123]]]
  g := ![![![-283, -194, -34, 166, 146], ![-682, -467, -82, 400, 352], ![-1646, -1124, -197, 964, 848], ![248, 170, 30, -145, -128], ![332, 228, 40, -194, -171]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-13523, 5576, 2018, 9236, 4130]] ![![8, -1, 0, -2, 1]]
  ![![-4654, -691, -122, 598, 525]] where
 M := ![![![-4654, -691, -122, 598, 525]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-4654, -691, -122, 598, 525]] ![![8, -1, 0, -2, 1]]
  ![![-28761, -4258, -756, 3652, 3228]] where
 M := ![![![-28761, -4258, -756, 3652, 3228]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-28761, -4258, -756, 3652, 3228]] ![![8, -1, 0, -2, 1]]
  ![![-177746, -26283, -4628, 22514, 19869]] where
 M := ![![![-177746, -26283, -4628, 22514, 19869]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![-177746, -26283, -4628, 22514, 19869]] ![![-1305, -194, -34, 166, 146]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![405867846, 60316269, 10580466, -51599544, -45406467]]]
 hmul := by decide  
 g := ![![![![135289282, 20105423, 3526822, -17199848, -15135489]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1, I3N1, I3N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, 6, 2, 8, 4]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-21, 6, 2, 8, 4]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-21, 6, 2, 8, 4], ![-72, 23, 12, 52, 20], ![-360, 172, 55, 288, 136], ![-116, 52, 16, 67, 32], ![-176, 74, 30, 124, 51]]]
  hmulB := by decide  
  f := ![![![15823, -7846, 478, -6864, 4868]], ![![-16552, 8207, -500, 7180, -5092]], ![![86568, -42924, 2615, -37552, 26632]], ![![-20128, 9980, -608, 8731, -6192]], ![![73225, -36308, 2212, -31764, 22527]]]
  g := ![![![-13, 6, 2, 8, 4], ![-68, 23, 12, 52, 20], ![-384, 172, 55, 288, 136], ![-96, 52, 16, 67, 32], ![-165, 74, 30, 124, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-21, 6, 2, 8, 4]] ![![-21, 6, 2, 8, 4]]
  ![![-2343, 1068, 388, 1752, 768]] where
 M := ![![![-2343, 1068, 388, 1752, 768]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-2343, 1068, 388, 1752, 768]] ![![-21, 6, 2, 8, 4]]
  ![![-505773, 225178, 80542, 361152, 159988]] where
 M := ![![![-505773, 225178, 80542, 361152, 159988]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-505773, 225178, 80542, 361152, 159988]] ![![-21, 6, 2, 8, 4]]
  ![![-104638223, 46616696, 16698472, 74894864, 33150432]] where
 M := ![![![-104638223, 46616696, 16698472, 74894864, 33150432]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-104638223, 46616696, 16698472, 74894864, 33150432]] ![![-21, 6, 2, 8, 4]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-21692729605, 9664156750, 3461370650, 15524731800, 6872080900]]]
 hmul := by decide  
 g := ![![![![-4338545921, 1932831350, 692274130, 3104946360, 1374416180]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4412, 2020, -87, 1470, -1141]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-4412, 2020, -87, 1470, -1141]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![3, 1, 1, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]] where
  M :=![![![-4412, 2020, -87, 1470, -1141], ![19687, -10310, 792, -8064, 5551], ![-92653, 49681, -3967, 44394, -29743], ![35566, -17890, 1122, -17059, 11872], ![-75292, 36267, -1925, 32158, -23247]]]
  hmulB := by decide  
  f := ![![![715572, 106242, 18623, -91072, -80089]], ![![1724501, 255704, 44776, -219812, -193127]], ![![1147014, 169859, 29714, -146418, -128529]], ![![-625888, -93858, -16580, 78735, 69730]], ![![-837338, -125905, -22287, 105000, 93171]]]
  g := ![![![-593, 301, -87, 210, -163], ![2473, -1586, 792, -1152, 793], ![-11536, 7664, -3967, 6342, -4249], ![4600, -2716, 1122, -2437, 1696], ![-9931, 5456, -1925, 4594, -3321]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [5, 5, 4, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 5, 5, 3], [0, 2, 3, 5], [2, 6, 6, 6], [0, 1]]
 g := ![![[2, 4, 6, 1], []], ![[0, 1, 4, 4, 0, 3], [3, 3, 0, 4, 3, 6]], ![[1, 0, 4, 6], [5, 3, 1, 0, 2, 6]], ![[0, 4, 6, 2, 5, 3], [3, 2, 5, 0, 5, 6]]]
 h' := ![![[4, 5, 5, 3], [0, 0, 0, 1], [0, 1]], ![[0, 2, 3, 5], [0, 0, 2, 1], [4, 5, 5, 3]], ![[2, 6, 6, 6], [3, 2, 2], [0, 2, 3, 5]], ![[0, 1], [0, 5, 3, 5], [2, 6, 6, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 6], []]
 b := ![[], [], [4, 2, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [5, 5, 4, 1, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15260104542003, 6655467527742, 3028970229493, 11831521173423, 6797556894345]
  a := ![24, -100, -27, -63, -153]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3478145032926, 518071042607, 3028970229493, 1690217310489, 971079556335]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![715572, 106242, 18623, -91072, -80089]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![715572, 106242, 18623, -91072, -80089]] 
 ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![715572, 106242, 18623, -91072, -80089], ![1724501, 255704, 44776, -219812, -193127], ![4157881, 614583, 107353, -531898, -466309], ![-625888, -93858, -16580, 78735, 69730], ![-837338, -125905, -22287, 105000, 93171]]]
  hmulB := by decide  
  f := ![![![-4412, 2020, -87, 1470, -1141]], ![![-339, -30, 51, -102, -22]], ![![-15127, 7963, -604, 6972, -4738]], ![![3190, -1690, 123, -1807, 1207]], ![![-10756, 5181, -275, 4594, -3321]]]
  g := ![![![57387, 106242, 18623, -91072, -80089], ![138727, 255704, 44776, -219812, -193127], ![336943, 614583, 107353, -531898, -466309], ![-49009, -93858, -16580, 78735, 69730], ![-65136, -125905, -22287, 105000, 93171]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-4412, 2020, -87, 1470, -1141]] ![![715572, 106242, 18623, -91072, -80089]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3020, -447, -78, 386, 339]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-3020, -447, -78, 386, 339]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![4, 5, 1, 1, 0], ![5, 6, 1, 0, 1]] where
  M :=![![![-3020, -447, -78, 386, 339], ![-7295, -1068, -186, 942, 819], ![-17619, -2555, -435, 2310, 2007], ![2604, 412, 74, -309, -288], ![3500, 544, 102, -416, -373]]]
  hmulB := by decide  
  f := ![![![264, -61, -12, 42, 9]], ![![-285, 288, -64, -114, 117]], ![![-2493, -81, 341, -194, -459]], ![![-172, 71, -3, -37, 12]], ![![-235, 140, -19, -64, 41]]]
  g := ![![![-569, -401, -73, 386, 339], ![-1378, -972, -177, 942, 819], ![-3354, -2377, -432, 2310, 2007], ![480, 335, 61, -309, -288], ![639, 442, 81, -416, -373]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [1, 5, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 7, 10], [6, 3, 1], [0, 1]]
 g := ![![[9, 8, 4], [4, 8, 1], []], ![[4, 9, 9, 10], [9, 3, 1, 2], [5, 1]], ![[8, 7, 0, 9], [7, 9, 5, 5], [3, 1]]]
 h' := ![![[2, 7, 10], [7, 5, 2], [0, 0, 1], [0, 1]], ![[6, 3, 1], [4, 6, 1], [10, 2, 3], [2, 7, 10]], ![[0, 1], [4, 0, 8], [0, 9, 7], [6, 3, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 1], []]
 b := ![[], [6, 9, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [1, 5, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5111291495246, -2199142064332, -1049246247132, -4005684876643, -2350689651009]
  a := ![178, -1157, -304, -859, -1638]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2989770841533, 2903038202267, 482466207320, -4005684876643, -2350689651009]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25181, 11215, 4017, 18018, 7976]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-25181, 11215, 4017, 18018, 7976]] 
 ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-25181, 11215, 4017, 18018, 7976], ![-145460, 64795, 23208, 104094, 46078], ![-840328, 374350, 134081, 601380, 266204], ![-213614, 95168, 34086, 152879, 67672], ![-371284, 165411, 59245, 265720, 117621]]]
  hmulB := by decide  
  f := ![![![53229, -26397, 1609, -23096, 16378]], ![![-15634, 7751, -472, 6782, -4810]], ![![166273, -82443, 5022, -72128, 51154]], ![![-40468, 20064, -1222, 17551, -12448]], ![![121663, -60328, 3676, -52778, 37429]]]
  g := ![![![-13786, 11215, 4017, 18018, 7976], ![-79644, 64795, 23208, 104094, 46078], ![-460125, 374350, 134081, 601380, 266204], ![-116970, 95168, 34086, 152879, 67672], ![-203306, 165411, 59245, 265720, 117621]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![30313, 4967, 1087, -3150, -2756]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![30313, 4967, 1087, -3150, -2756]] 
 ![![11, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![30313, 4967, 1087, -3150, -2756], ![62036, 17149, 3298, -1318, -6694], ![148292, 40342, 13753, 6008, 2740], ![-48424, 5730, 1198, 16413, 4946], ![-44974, -2443, 3221, 14872, 16077]]]
  hmulB := by decide  
  f := ![![![1306647, -1698857, 424615, 641220, -752998]], ![![2305451, -1083130, 85915, 537742, -235848]], ![![-5146062, 1031220, 288607, -770372, -264980]], ![![236453, -1256595, 405705, 410369, -678068]], ![![2535894, -994287, 26209, 530370, -146909]]]
  g := ![![![1436, 4967, 1087, -3150, -2756], ![-4039, 17149, 3298, -1318, -6694], ![-23420, 40342, 13753, 6008, 2740], ![-17961, 5730, 1198, 16413, 4946], ![-16897, -2443, 3221, 14872, 16077]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-3020, -447, -78, 386, 339]] ![![-25181, 11215, 4017, 18018, 7976]]
  ![![-1707456, 777212, 277617, 1238356, 546613]] where
 M := ![![![-1707456, 777212, 277617, 1238356, 546613]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![-1707456, 777212, 277617, 1238356, 546613]] ![![30313, 4967, 1087, -3150, -2756]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![-46924133938, 21807503971, 7769498066, 34476409484, 15176568165]]]
 hmul := by decide  
 g := ![![![![-4265830358, 1982500361, 706318006, 3134219044, 1379688015]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1937269, 323126, 50276, -229530, -239664]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![1937269, 323126, 50276, -229530, -239664]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![5, 0, 1, 0, 0], ![1, 11, 0, 1, 0], ![3, 5, 0, 0, 1]] where
  M :=![![![1937269, 323126, 50276, -229530, -239664], ![5084802, 571411, 133738, -734120, -448926], ![10066142, 2459554, 256223, -821224, -1753434], ![-1180340, -540366, -28426, -23597, 369624], ![-3439116, 198322, -94210, 774790, -77051]]]
  hmulB := by decide  
  f := ![![![-228491, 101442, 36340, 162430, 71892]], ![![-1310338, 583331, 209674, 940112, 415398]], ![![-670545, 299032, 106931, 479998, 212646]], ![![-1275025, 567569, 203888, 914041, 403998]], ![![-814491, 362507, 130196, 583568, 257959]]]
  g := ![![![202647, 311252, 50276, -229530, -239664], ![499770, 837797, 133738, -734120, -448926], ![1143581, 1558476, 256223, -821224, -1753434], ![-163345, -163763, -28426, -23597, 369624], ![-270131, -610701, -94210, 774790, -77051]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [5, 5, 1] where
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
 g := ![![[1, 1], [10], [8, 1]], ![[9, 12], [10], [3, 12]]]
 h' := ![![[8, 12], [3, 1], [12, 7], [0, 1]], ![[0, 1], [11, 12], [3, 6], [8, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [12, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [5, 5, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-540161, 205077, 135769, 398534, 321914]
  a := ![17, -87, -23, -60, -128]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-198714, -445259, 135769, 398534, 321914]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![638, 96, 17, -80, -71]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![638, 96, 17, -80, -71]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![5, 10, 1, 0, 0], ![3, 5, 0, 1, 0], ![0, 2, 0, 0, 1]] where
  M :=![![![638, 96, 17, -80, -71], ![1531, 234, 42, -188, -169], ![3651, 581, 107, -426, -395], ![-578, -76, -12, 83, 68], ![-780, -99, -15, 116, 93]]]
  hmulB := by decide  
  f := ![![![-34, 10, 1, 2, -5]], ![![99, -56, 6, -16, 11]], ![![51, -25, 2, 0, 2]], ![![33, -22, 3, -11, 6]], ![![-4, -1, 1, 6, -5]]]
  g := ![![![61, 36, 17, -80, -71], ![145, 84, 42, -188, -169], ![338, 187, 107, -426, -395], ![-59, -39, -12, 83, 68], ![-81, -55, -15, 116, 93]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [4, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 12], [0, 1]]
 g := ![![[5, 10], [10], [6, 1]], ![[0, 3], [10], [12, 12]]]
 h' := ![![[6, 12], [3, 6], [2, 6], [0, 1]], ![[0, 1], [0, 7], [12, 7], [6, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [12, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [4, 7, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14347658, 5487054, 3589146, 10603152, 8507994]
  a := ![-85, 448, 119, 311, 655]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4930988, -7725858, 3589146, 10603152, 8507994]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1496, 2082, 721, 5492, 2461]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![-1496, 2082, 721, 5492, 2461]] 
 ![![13, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-1496, 2082, 721, 5492, 2461], ![-47925, 23088, 5264, 24860, 14015], ![-259561, 92609, 42367, 157786, 60565], ![-35588, 19442, 8376, 44045, 18098], ![-97074, 48765, 13791, 68828, 34161]]]
  hmulB := by decide  
  f := ![![![2233847464, 331970680, 58233717, -283998798, -249910205]], ![![929479799, 138130906, 24230411, -118168122, -103985908]], ![![1684690907, 250356657, 43917893, -214184126, -188470939]], ![![1739501066, 258508022, 45346689, -221149497, -194606735]], ![![657463288, 97701047, 17139304, -83588164, -73550560]]]
  g := ![![![-6411, 2082, 721, 5492, 2461], ![-37060, 23088, 5264, 24860, 14015], ![-211179, 92609, 42367, 157786, 60565], ![-54031, 19442, 8376, 44045, 18098], ![-94342, 48765, 13791, 68828, 34161]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![1937269, 323126, 50276, -229530, -239664]] ![![638, 96, 17, -80, -71]]
  ![![2233847464, 331970680, 58233717, -283998798, -249910205]] where
 M := ![![![2233847464, 331970680, 58233717, -283998798, -249910205]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![2233847464, 331970680, 58233717, -283998798, -249910205]] ![![-1496, 2082, 721, 5492, 2461]]
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


def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [7, 2, 16, 7, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 1, 7, 16, 1], [2, 15, 5, 3], [15, 11, 12, 13, 4], [8, 6, 10, 2, 12], [0, 1]]
 g := ![![[6, 10, 5, 15, 16], [1, 10, 0, 1], [], []], ![[14, 7, 9, 3, 12, 15, 8, 8], [13, 4, 15, 9], [13, 9, 4, 8], [3, 8, 15, 1]], ![[13, 16, 14, 9, 0, 9, 10], [16, 6, 16, 8], [10, 5, 7, 1], [13, 9]], ![[0, 15, 9, 1, 14, 12, 1, 4], [0, 3, 3, 13], [4, 7, 6, 15], [11, 0, 2, 16]], ![[5, 4, 9, 8, 8, 14, 0, 12], [4, 0, 4, 1], [10, 1, 12, 1], [9, 1, 14, 8]]]
 h' := ![![[9, 1, 7, 16, 1], [10, 13, 15, 13, 13], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[2, 15, 5, 3], [9, 5, 4, 5, 5], [7, 3, 8, 11, 3], [9, 7, 9, 14, 5], [9, 1, 7, 16, 1]], ![[15, 11, 12, 13, 4], [11, 0, 0, 2, 14], [2, 10, 2, 5, 5], [15, 5, 2, 12, 1], [2, 15, 5, 3]], ![[8, 6, 10, 2, 12], [9, 16, 3, 7, 1], [14, 8, 0, 3, 9], [12, 2, 2, 2, 10], [15, 11, 12, 13, 4]], ![[0, 1], [7, 0, 12, 7, 1], [16, 13, 7, 15, 16], [1, 3, 3, 6, 1], [8, 6, 10, 2, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 13, 3, 11], [], [], []]
 b := ![[], [14, 6, 7, 3, 6], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 5
  hpos := by decide
  P := [7, 2, 16, 7, 0, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![56581021809090257, -24414733161599716, -11999894706299598, -44882775242187106, -27712177609746354]
  a := ![35, -97, -26, -45, -163]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3328295400534721, -1436160774211748, -705876159194094, -2640163249540418, -1630128094690962]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![330, -1, -18, 10, 13]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![330, -1, -18, 10, 13]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![2, 16, 3, 11, 1]] where
  M :=![![![330, -1, -18, 10, 13], ![-365, 310, -6, -174, 17], ![-185, -473, 321, 18, -539], ![896, -204, -62, 159, 68], ![-376, 260, -70, -92, 135]]]
  hmulB := by decide  
  f := ![![![-550, 245, 88, 394, 175]], ![![-3191, 1422, 508, 2282, 1007]], ![![-18367, 8181, 2937, 13154, 5839]], ![![-4690, 2090, 746, 3353, 1478]], ![![-8787, 3915, 1401, 6287, 2780]]]
  g := ![![![16, -11, -3, -7, 13], ![-21, 2, -3, -19, 17], ![47, 429, 102, 313, -539], ![40, -68, -14, -31, 68], ![-34, -100, -25, -83, 135]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [10, 8, 18, 17, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 14, 0, 5], [6, 5, 16, 9], [9, 18, 3, 5], [0, 1]]
 g := ![![[7, 11, 17, 11], [13, 16, 12, 4], [1], []], ![[7, 11, 14, 0, 14, 1], [0, 14, 17, 10, 1, 17], [14, 5, 9], [18, 12, 6]], ![[4, 17, 0, 10, 2, 4], [15, 2, 14, 7, 5, 4], [17, 7, 11], [16, 13, 5]], ![[8, 1, 9, 13, 11, 7], [0, 16, 3, 5, 18, 1], [13, 15, 5], [13, 4, 6]]]
 h' := ![![[6, 14, 0, 5], [3, 7, 1, 7], [9, 11, 1, 2], [0, 0, 1], [0, 1]], ![[6, 5, 16, 9], [0, 12, 12, 2], [0, 12, 15, 7], [8, 18, 1, 3], [6, 14, 0, 5]], ![[9, 18, 3, 5], [9, 15, 7, 7], [6, 11, 7, 12], [9, 11, 3, 7], [6, 5, 16, 9]], ![[0, 1], [7, 4, 18, 3], [10, 4, 15, 17], [8, 9, 14, 9], [9, 18, 3, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 14, 8], []]
 b := ![[], [], [11, 16, 14, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [10, 8, 18, 17, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5594773837966, 2490049763592, 896723473712, 4007914105888, 1784006987784]
  a := ![-14, -82, -18, -98, -84]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-482251990186, -1371266423208, -234489341560, -821903303144, 1784006987784]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![550, -245, -88, -394, -175]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![550, -245, -88, -394, -175]] 
 ![![19, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![550, -245, -88, -394, -175], ![3191, -1422, -508, -2282, -1007], ![18367, -8181, -2937, -13154, -5839], ![4690, -2090, -746, -3353, -1478], ![8106, -3610, -1298, -5808, -2583]]]
  hmulB := by decide  
  f := ![![![-330, 1, 18, -10, -13]], ![![-85, -16, 6, 6, -5]], ![![-25, 25, -15, -2, 27]], ![![-134, 11, 8, -11, -7]], ![![-206, -13, 16, -2, -16]]]
  g := ![![![339, -245, -88, -394, -175], ![1960, -1422, -508, -2282, -1007], ![11316, -8181, -2937, -13154, -5839], ![2879, -2090, -746, -3353, -1478], ![4999, -3610, -1298, -5808, -2583]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![330, -1, -18, 10, 13]] ![![550, -245, -88, -394, -175]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![-19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1893, -293, -57, 254, 226]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-1893, -293, -57, 254, 226]] 
 ![![23, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![-1893, -293, -57, 254, 226], ![-4890, -625, -124, 558, 536], ![-11486, -1860, -213, 1480, 1138], ![1986, 208, 26, -179, -172], ![2200, 421, 43, -324, -225]]]
  hmulB := by decide  
  f := ![![![-18547, 8283, 2883, 13160, 5624]], ![![-4466, 1985, 730, 3222, 1472]], ![![-26810, 11968, 4187, 19052, 8194]], ![![-12157, 5413, 1951, 8717, 3888]], ![![-24083, 10760, 3726, 17062, 7245]]]
  g := ![![![-307, -293, -57, 254, 226], ![-732, -625, -124, 558, 536], ![-1692, -1860, -213, 1480, 1138], ![253, 208, 26, -179, -172], ![341, 421, 43, -324, -225]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39065, 9879, 993, -3028, -7024]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![39065, 9879, 993, -3028, -7024]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![6, 12, 1, 0, 0], ![8, 16, 0, 1, 0], ![6, 8, 0, 0, 1]] where
  M :=![![![39065, 9879, 993, -3028, -7024], ![142442, -149, 3848, -28242, -2060], ![90470, 124928, 1639, 41512, -82666], ![25676, -38392, 944, -23353, 24598], ![-180574, 55201, -5235, 62006, -33207]]]
  hmulB := by decide  
  f := ![![![5176499943, -2306138105, -825986463, -3704660518, -1639875134]], ![![29906369286, -13323330157, -4771999702, -21403061286, -9474106420]], ![![24465848528, -10899570402, -3903884847, -17509449256, -7750591534]], ![![24514661184, -10921316510, -3911673622, -17544382961, -7766055006]], ![![15071877728, -6714543017, -2404939073, -10786475604, -4774654261]]]
  g := ![![![4325, 4461, 993, -3028, -7024], ![15550, 18349, 3848, -28242, -2060], ![10632, 4452, 1639, 41512, -82666], ![2576, 5528, 944, -23353, 24598], ![-19390, -26453, -5235, 62006, -33207]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [22, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 22], [0, 1]]
 g := ![![[4, 13], [19, 13], [3, 16], [1]], ![[10, 10], [2, 10], [21, 7], [1]]]
 h' := ![![[4, 22], [19, 6], [3, 6], [1, 4], [0, 1]], ![[0, 1], [20, 17], [4, 17], [17, 19], [4, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [14, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [22, 19, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-295354, 141914, 48462, 217876, 103988]
  a := ![17, 62, 14, 81, 55]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-128394, -206850, 48462, 217876, 103988]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10502153, 241544868, -85008270, -73982484, 139620906]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![10502153, 241544868, -85008270, -73982484, 139620906]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![21, 11, 1, 0, 0], ![12, 4, 0, 1, 0], ![10, 5, 0, 0, 1]] where
  M :=![![![10502153, 241544868, -85008270, -73982484, 139620906], ![-3088864350, 264195485, 296157504, -352390344, -361568358], ![8999134170, -3833719818, 198784631, 1976794908, -695602674], ![1564528764, 628164180, -414015564, -57799225, 618091056], ![-3690219240, 902843958, 150357966, -603087900, -96766489]]]
  hmulB := by decide  
  f := ![![![19523731, 92395068, -65838, 40102020, -60441534]], ![![1107892098, -303418481, 31887696, -363570936, 180747594]], ![![422500185, 27079393, 11243429, -70705416, -24022134]], ![![259375440, -36474880, 7243452, -68672857, 19818360]], ![![119662280, 33298087, 3019806, -7830540, -23486959]]]
  g := ![![![55967677, 33672228, -85008270, -73982484, 139620906], ![-63643662, 9733309, 296157504, -352390344, -361568358], ![-519167619, -454326827, 198784631, 1976794908, -695602674], ![207458076, 101003348, -414015564, -57799225, 618091056], ![58999268, 93264799, 150357966, -603087900, -96766489]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P2 : CertificateIrreducibleZModOfList' 23 2 2 4 [3, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 22], [0, 1]]
 g := ![![[13, 8], [8, 12], [2, 3], [1]], ![[0, 15], [0, 11], [0, 20], [1]]]
 h' := ![![[7, 22], [22, 10], [17, 14], [20, 7], [0, 1]], ![[0, 1], [0, 13], [0, 9], [0, 16], [7, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [12, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N2 : CertifiedPrimeIdeal' SI23N2 23 where
  n := 2
  hpos := by decide
  P := [3, 16, 1]
  hirr := P23P2
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-167328, 72374, 31201, 117467, 69117]
  a := ![-1, -46, -11, -45, -55]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-127101, -47230, 31201, 117467, 69117]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N2 B_one_repr
lemma NI23N2 : Nat.card (O ⧸ I23N2) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-1893, -293, -57, 254, 226]] ![![39065, 9879, 993, -3028, -7024]]
  ![![-155130361, -23054328, -4043970, 19722420, 17355084]] where
 M := ![![![-155130361, -23054328, -4043970, 19722420, 17355084]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![-155130361, -23054328, -4043970, 19722420, 17355084]] ![![10502153, 241544868, -85008270, -73982484, 139620906]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![2488973857387, -493488550896, -141417762648, 370966092696, 131174097582]]]
 hmul := by decide  
 g := ![![![![108216254669, -21456023952, -6148598376, 16128960552, 5703221634]]]]
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


lemma PB6026I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB6026I0 : PrimesBelowBoundCertificateInterval O 1 23 6026 where
  m := 9
  g := ![5, 5, 5, 2, 3, 3, 1, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB6026I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1, I3N2]
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
    · exact ![2401, 7]
    · exact ![1331, 11, 11]
    · exact ![169, 169, 13]
    · exact ![1419857]
    · exact ![130321, 19]
    · exact ![23, 529, 529]
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
      exact NI3N1
      exact NI3N1
      exact NI3N1
      exact NI3N2
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
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I3N2, I5N0, I7N0, I7N1, I11N0, I11N1, I11N2, I13N0, I13N1, I13N2, I19N1, I23N0, I23N1, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1, I3N1, I3N2], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1], [I11N0, I11N1, I11N2], [I13N0, I13N1, I13N2], [], [I19N1], [I23N0, I23N1, I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
