
import IdealArithmetic.Examples.NF5_3_15187500000_3.RI5_3_15187500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1979387, 3370674, 2853966, 252130, 2642016]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![1979387, 3370674, 2853966, 252130, 2642016]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![10, 20, 1, 0, 0], ![11, 27, 0, 1, 0], ![14, 8, 0, 0, 1]] where
  M :=![![![1979387, 3370674, 2853966, 252130, 2642016], ![12201560, 20725629, 17549094, 1553136, 16235640], ![74965656, 127404176, 107876691, 9543732, 99815832], ![192969288, 327908018, 277649350, 24565713, 256894056], ![176236848, 299482170, 253580294, 22435736, 234625675]]]
  hmulB := by decide  
  f := ![![![-2910633, -3328538, -725238, -214806, 806832]], ![![4893384, 2522385, -1470866, -968472, 1456488]], ![![2755782, 1078712, -1127505, -693272, 1133064]], ![![2788033, 535431, -1627254, -941865, 1655088]], ![![-547526, -1409466, -822030, -379268, 868675]]]
  g := ![![![-2286963, -2815596, 2853966, 252130, 2642016], ![-14057684, -17312967, 17549094, 1553136, 16235640], ![-86420826, -106425416, 107876691, 9543732, 99815832], ![-222422891, -273913989, 277649350, 24565713, 256894056], ![-203142022, -250168758, 253580294, 22435736, 234625675]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [15, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 28], [0, 1]]
 g := ![![[], [5], [0, 22], [0, 1]], ![[], [5], [0, 7], [0, 28]]]
 h' := ![![[0, 28], [12], [0, 18], [0, 14], [0, 1]], ![[0, 1], [12], [0, 11], [0, 15], [0, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [0, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [15, 0, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![41357, 172642, 180007, -21977, 221454]
  a := ![27, -7, -25, 32, -81]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-159218, -158819, 180007, -21977, 221454]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-214996436, -364152734, -308382723, -27321357, -285127085]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-214996436, -364152734, -308382723, -27321357, -285127085]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![5, 18, 1, 0, 0], ![25, 20, 0, 1, 0], ![5, 26, 0, 0, 1]] where
  M :=![![![-214996436, -364152734, -308382723, -27321357, -285127085], ![-1316349997, -2238207388, -1895007868, -167710219, -1753491709], ![-8096617669, -13758502179, -11650312749, -1030262713, -10779981173], ![-20841118672, -35414123207, -29984607505, -2654402667, -27741538624], ![-19032548102, -32342827330, -27385276918, -2423205288, -25338069165]]]
  hmulB := by decide  
  f := ![![![-93884673200, -76243352340, 3845575569, 6534014497, -2457081397]], ![![-38421464973, -104550228482, -62624058868, -29055854447, 66122766979]], ![![-24626637339, -64404787067, -37857102226, -17495553986, 39995447592]], ![![-115518423652, -139416417937, -35183353014, -11688418860, 38713824811]], ![![-62390754690, -114887199658, -53652674747, -23438821967, 57141167514]]]
  g := ![![![118468501, 453326470, -308382723, -27321357, -285127085], ![728238047, 2786790450, -1895007868, -167710219, -1753491709], ![4476255854, 17132134209, -11650312749, -1030262713, -10779981173], ![11522402712, 44092305843, -29984607505, -2654402667, -27741538624], ![10522907397, 40270553836, -27385276918, -2423205288, -25338069165]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [5, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 28], [0, 1]]
 g := ![![[14, 6], [5], [8, 7], [17, 1]], ![[0, 23], [5], [11, 22], [5, 28]]]
 h' := ![![[17, 28], [9, 8], [18, 18], [2, 23], [0, 1]], ![[0, 1], [0, 21], [5, 11], [16, 6], [17, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [13, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [5, 12, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4636238, 10451838, 9719601, -99555, 10415340]
  a := ![175, -59, -176, 169, -522]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3225848, -14941680, 9719601, -99555, 10415340]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-76433, -10494, -10286, -7266, 13746]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![-76433, -10494, -10286, -7266, 13746]] 
 ![![29, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![-76433, -10494, -10286, -7266, 13746], ![97794, 12523, 12406, 9278, -18462], ![-129422, -22162, -21085, -12394, 19026], ![137064, 6764, 8380, 12781, -36312], ![47870, -4314, -2648, 4326, -19141]]]
  hmulB := by decide  
  f := ![![![-937, 590, 258, -1054, 1014]], ![![-326, 583, 238, -526, 438]], ![![-2304, -1186, -153, -1042, 1314]], ![![4688, 3540, 532, 1253, -1896]], ![![986, 1126, 216, 22, -205]]]
  g := ![![![7055, -10494, -10286, -7266, 13746], ![-7870, 12523, 12406, 9278, -18462], ![17568, -22162, -21085, -12394, 19026], ![2776, 6764, 8380, 12781, -36312], ![9514, -4314, -2648, 4326, -19141]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![1979387, 3370674, 2853966, 252130, 2642016]] ![![-214996436, -364152734, -308382723, -27321357, -285127085]]
  ![![-83508987259602956, -141910594242103674, -120159817850428705, -10631112454166841, -111178583782826639]] where
 M := ![![![-83508987259602956, -141910594242103674, -120159817850428705, -10631112454166841, -111178583782826639]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-83508987259602956, -141910594242103674, -120159817850428705, -10631112454166841, -111178583782826639]] ![![-76433, -10494, -10286, -7266, 13746]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![1276900112637294795548, 2169894389608739679094, 1837312537652033883189, 162555788767036125559, 1699984385227750282373]]]
 hmul := by decide  
 g := ![![![![44031038366803268812, 74823944469266885486, 63355604746621858041, 5605372026449521571, 58620151214750009737]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 5 2 4 [24, 5, 9, 24, 6, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 20, 18, 0, 13], [5, 17, 29, 13, 9], [18, 30, 4, 28, 23], [1, 25, 11, 21, 17], [0, 1]]
 g := ![![[9, 18, 1, 0, 20], [22, 0, 29, 12, 1], [12, 25, 1], []], ![[26, 1, 7, 21, 21, 3, 22, 23], [7, 4, 3, 16, 9, 21, 10, 3], [17, 19, 21, 8, 16, 14, 8, 17], [10, 25, 4, 20, 20, 26, 24, 27]], ![[5, 14, 19, 23, 22, 20, 30, 9], [21, 3, 15, 22, 8, 16, 19, 1], [8, 21, 14, 6, 3, 22, 21, 9], [6, 28, 13, 17, 3, 9, 25, 16]], ![[7, 7, 26, 7, 17, 15, 5, 21], [1, 25, 12, 11, 17, 10, 27, 12], [24, 15, 27, 27, 17, 1, 20, 6], [4, 11, 8, 12, 6, 3, 16, 15]], ![[27, 30, 21, 11, 22, 1, 11, 23], [7, 4, 12, 27, 28, 9, 3, 3], [16, 7, 25, 11, 15, 8, 9, 24], [6, 16, 25, 19, 12, 1, 13, 15]]]
 h' := ![![[1, 20, 18, 0, 13], [30, 2, 12, 26, 19], [22, 22, 22, 9, 1], [0, 0, 0, 1], [0, 1]], ![[5, 17, 29, 13, 9], [28, 17, 19, 17, 20], [14, 7, 23, 3, 25], [9, 30, 13, 19, 7], [1, 20, 18, 0, 13]], ![[18, 30, 4, 28, 23], [28, 21, 3, 16, 1], [1, 15, 5, 11, 10], [12, 15, 21, 0, 30], [5, 17, 29, 13, 9]], ![[1, 25, 11, 21, 17], [7, 15, 19, 2, 28], [0, 28, 21, 5, 18], [1, 15, 1, 3, 21], [18, 30, 4, 28, 23]], ![[0, 1], [20, 7, 9, 1, 25], [8, 21, 22, 3, 8], [12, 2, 27, 8, 4], [1, 25, 11, 21, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 23, 3, 12], [], [], []]
 b := ![[], [21, 9, 0, 30, 11], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 5
  hpos := by decide
  P := [24, 5, 9, 24, 6, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2717156099896908, -4629507445104759, -3923997886808451, -342792898772835, -3636997336332741]
  a := ![18, -5, -17, 19, -53]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-87650196770868, -149338949842089, -126580576993821, -11057835444285, -117322494720411]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 28629151 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀

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


def P37P0 : CertificateIrreducibleZModOfList' 37 5 2 5 [11, 8, 32, 11, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 5, 16, 28, 26], [9, 21, 20, 2, 22], [19, 34, 1, 12, 18], [12, 13, 0, 32, 8], [0, 1]]
 g := ![![[7, 14, 7, 17, 9], [22, 33, 30, 26], [2, 5, 26, 0, 1], [], []], ![[26, 9, 5, 34, 3, 25, 16, 1], [4, 6, 14, 7], [22, 33, 5, 6, 9, 26, 1, 7], [31, 28, 32, 25], [27, 26, 13, 10]], ![[4, 29, 36, 24, 16, 29, 19, 2], [28, 6, 13, 36], [25, 1, 13, 35, 33, 14, 19, 31], [3, 20, 7, 1], [14, 0, 14, 3]], ![[15, 14, 27, 1, 8, 21, 24, 20], [18, 1], [20, 1, 6, 3, 35, 4, 32, 2], [18, 12, 1, 4], [3, 20, 25, 28]], ![[0, 10, 16, 6, 27, 5, 25, 13], [28, 2, 1, 12], [25, 20, 2, 26, 23, 1, 22, 15], [12, 25, 22, 16], [2, 24, 31, 27]]]
 h' := ![![[34, 5, 16, 28, 26], [20, 32, 35, 9, 3], [15, 3, 17, 17, 27], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[9, 21, 20, 2, 22], [5, 29, 14, 9, 26], [7, 17, 33, 9, 9], [19, 34, 30, 7, 12], [8, 23, 9, 18, 5], [34, 5, 16, 28, 26]], ![[19, 34, 1, 12, 18], [9, 17, 23, 4, 8], [24, 1, 10, 2, 31], [5, 29, 3, 18, 17], [1, 7, 14, 22, 1], [9, 21, 20, 2, 22]], ![[12, 13, 0, 32, 8], [24, 30, 34, 24, 16], [0, 10, 9, 1], [12, 11, 9, 18, 12], [32, 12, 34, 9, 35], [19, 34, 1, 12, 18]], ![[0, 1], [0, 3, 5, 28, 21], [30, 6, 5, 8, 7], [26, 0, 32, 31, 32], [11, 32, 16, 25, 33], [12, 13, 0, 32, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 33, 19, 8], [], [], []]
 b := ![[], [35, 5, 21, 10, 31], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 5
  hpos := by decide
  P := [11, 8, 32, 11, 0, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6510571587499076119, 11096730567654282250, 9406983285166745736, 820343057834689772, 8721016555837406528]
  a := ![-84, 26, 81, -92, 253]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![175961394256731787, 299911636963629250, 254242791490993128, 22171433995532156, 235703150157767744]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2097, -1532, 224, 220, -232]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-2097, -1532, 224, 220, -232]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![23, 37, 16, 4, 1]] where
  M :=![![![-2097, -1532, 224, 220, -232], ![-2040, -3501, -1576, -640, 1480], ![9960, 7680, -1077, -792, -280], ![-4096, -236, 2092, 1835, -5312], ![-7892, -5544, 364, 1116, -3165]]]
  hmulB := by decide  
  f := ![![![221383, 118940, 14544, 94292, -120152]], ![![-977928, -525389, -64248, -416512, 530744]], ![![4319768, 2320768, 283803, 1839832, -2344424]], ![![-11700608, -6286068, -768716, -4983397, 6350144]], ![![-274283, -147357, -18020, -116820, 148859]]]
  g := ![![![79, 172, 96, 28, -232], ![-880, -1421, -616, -160, 1480], ![400, 440, 83, 8, -280], ![2880, 4788, 2124, 563, -5312], ![1583, 2721, 1244, 336, -3165]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 4 2 5 [11, 5, 13, 38, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 29, 12, 21], [8, 3, 34, 30], [39, 8, 36, 31], [0, 1]]
 g := ![![[4, 22, 6, 8], [28, 10, 9], [20, 31, 16], [3, 1], []], ![[13, 30, 29, 18, 26, 40], [38, 27, 16], [30, 17, 23], [31, 25, 35, 1, 28, 2], [3, 23, 31]], ![[18, 15, 21, 0, 10, 12], [33, 26, 32], [20, 0, 21], [40, 29, 21, 15, 33, 14], [2, 25, 39]], ![[30, 28, 25, 27, 13, 31], [27, 30, 5], [23, 33, 10], [4, 22, 2, 40, 23, 16], [11, 31, 18]]]
 h' := ![![[38, 29, 12, 21], [2, 19, 13, 34], [8, 4, 37, 38], [8, 15, 38, 37], [0, 0, 1], [0, 1]], ![[8, 3, 34, 30], [10, 13, 16, 11], [31, 16, 23, 4], [22, 22, 7, 8], [17, 9, 28, 2], [38, 29, 12, 21]], ![[39, 8, 36, 31], [2, 4, 39, 36], [18, 32, 23, 27], [19, 38, 23, 12], [1, 9, 14, 6], [8, 3, 34, 30]], ![[0, 1], [32, 5, 14, 1], [1, 30, 40, 13], [7, 7, 14, 25], [6, 23, 39, 33], [39, 8, 36, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [24, 19, 25], []]
 b := ![[], [], [3, 35, 6, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 4
  hpos := by decide
  P := [11, 5, 13, 38, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3832203643482, 6917923976520, 5993469587894, 383616456669, 5756168693274]
  a := ![31, -8, -26, 41, -94]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3135601861020, -5025861406698, -2100127548890, -552220934547, 5756168693274]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 2825761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![221383, 118940, 14544, 94292, -120152]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![221383, 118940, 14544, 94292, -120152]] 
 ![![41, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![221383, 118940, 14544, 94292, -120152], ![-977928, -525389, -64248, -416512, 530744], ![4319768, 2320768, 283803, 1839832, -2344424], ![-11700608, -6286068, -768716, -4983397, 6350144], ![-2467932, -1325880, -162140, -1051116, 1339395]]]
  hmulB := by decide  
  f := ![![![-2097, -1532, 224, 220, -232]], ![![-1533, -1169, 120, 140, -128]], ![![-780, -560, 83, 88, -120]], ![![-1532, -1052, 204, 195, -288]], ![![-1420, -1032, 140, 156, -213]]]
  g := ![![![-79885, 118940, 14544, 94292, -120152], ![352873, -525389, -64248, -416512, 530744], ![-1558724, 2320768, 283803, 1839832, -2344424], ![4221984, -6286068, -768716, -4983397, 6350144], ![890516, -1325880, -162140, -1051116, 1339395]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-2097, -1532, 224, 220, -232]] ![![221383, 118940, 14544, 94292, -120152]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4764, 647, 632, 451, -861]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![4764, 647, 632, 451, -861]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![2, 31, 21, 1, 0], ![8, 4, 24, 0, 1]] where
  M :=![![![4764, 647, 632, 451, -861], ![-6109, -812, -812, -581, 1107], ![7859, 1059, 1061, 755, -1437], ![-9032, -1252, -1212, -863, 1656], ![-3406, -466, -462, -330, 635]]]
  hmulB := by decide  
  f := ![![![-392, -211, -26, -167, 213]], ![![1733, 932, 114, 737, -939]], ![![-7643, -4103, -499, -3255, 4149]], ![![-2020, -1083, -131, -861, 1098]], ![![-4076, -2188, -266, -1736, 2213]]]
  g := ![![![250, -230, 275, 451, -861], ![-321, 297, -353, -581, 1107], ![415, -386, 458, 755, -1437], ![-478, 439, -531, -863, 1656], ![-182, 168, -204, -330, 635]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [13, 15, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 38, 39], [40, 4, 4], [0, 1]]
 g := ![![[42, 39, 31], [14, 11, 23], [25, 1], [42, 10, 1], []], ![[0, 35, 12, 18], [39, 6, 38, 22], [9, 31], [26, 3, 15, 22], [28, 16]], ![[10, 13, 11, 16], [27, 39, 32, 10], [27, 23], [8, 9, 20, 14], [20, 16]]]
 h' := ![![[13, 38, 39], [33, 32, 26], [16, 19, 18], [13, 14, 42], [0, 0, 1], [0, 1]], ![[40, 4, 4], [23, 41, 19], [21, 21, 39], [3, 0, 26], [20, 16, 4], [13, 38, 39]], ![[0, 1], [33, 13, 41], [42, 3, 29], [7, 29, 18], [7, 27, 38], [40, 4, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 31], []]
 b := ![[], [32, 29, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [13, 15, 33, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-316563411, -539903004, -457838354, -39827710, -424602528]
  a := ![16, -4, -18, 10, -48]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![73486331, 55655026, 245790796, -39827710, -424602528]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14193, -24175, -20469, -1808, -18950]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-14193, -24175, -20469, -1808, -18950]] 
 ![![43, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![-14193, -24175, -20469, -1808, -18950], ![-87518, -148651, -125868, -11140, -116446], ![-537670, -913780, -773723, -68450, -715910], ![-1384040, -2351855, -1991385, -176193, -1842520], ![-1264026, -2147976, -1818754, -160916, -1682805]]]
  hmulB := by decide  
  f := ![![![-23111, -12375, -1577, -9994, 12730]], ![![-6727, -3590, -461, -2926, 3724]], ![![-17094, -9180, -1135, -7306, 9310]], ![![17463, 9390, 1106, 7355, -9370]], ![![-4129, -2201, -305, -1838, 2341]]]
  g := ![![![24196, -24175, -20469, -1808, -18950], ![148753, -148651, -125868, -11140, -116446], ![914442, -913780, -773723, -68450, -715910], ![2353536, -2351855, -1991385, -176193, -1842520], ![2149515, -2147976, -1818754, -160916, -1682805]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3526616, 1894648, 231699, 1502023, -1913969]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![3526616, 1894648, 231699, 1502023, -1913969]] 
 ![![43, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![3526616, 1894648, 231699, 1502023, -1913969], ![-15577937, -8369144, -1023460, -6634771, 8454431], ![68811239, 36968309, 4520807, 29307275, -37345097], ![-186382912, -100132737, -12245127, -79382107, 101153456], ![-39312590, -21120370, -2582774, -16743556, 21335643]]]
  hmulB := by decide  
  f := ![![![-77308, 135126, 111289, -4341, 154897]], ![![-31925, 111306, 92304, -647, 117663]], ![![15951, 241895, 202300, 6464, 229030]], ![![189392, 409265, 345511, 25915, 336720]], ![![132308, 437308, 367789, 21229, 381698]]]
  g := ![![![-330536, 1894648, 231699, 1502023, -1913969], ![1460082, -8369144, -1023460, -6634771, 8454431], ![-6449443, 36968309, 4520807, 29307275, -37345097], ![17468969, -100132737, -12245127, -79382107, 101153456], ![3684621, -21120370, -2582774, -16743556, 21335643]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![4764, 647, 632, 451, -861]] ![![-14193, -24175, -20469, -1808, -18950]]
  ![![77308, -135126, -111289, 4341, -154897]] where
 M := ![![![77308, -135126, -111289, 4341, -154897]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![77308, -135126, -111289, 4341, -154897]] ![![3526616, 1894648, 231699, 1502023, -1913969]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![-43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-323031, -173544, -21224, -137586, 175320]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-323031, -173544, -21224, -137586, 175320]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![32, 7, 1, 0, 0], ![13, 35, 0, 1, 0], ![38, 20, 0, 0, 1]] where
  M :=![![![-323031, -173544, -21224, -137586, 175320], ![1426944, 766623, 93754, 607748, -774432], ![-6303152, -3386332, -414107, -2684548, 3420816], ![17072712, 9172172, 1121644, 7271403, -9265656], ![3601064, 1934646, 236578, 1533708, -1954343]]]
  hmulB := by decide  
  f := ![![![-31609, -4784, -4624, -3014, 5256]], ![![38336, 2169, 2574, 3580, -9888]], ![![-17168, -3515, -3277, -1656, 1968]], ![![20413, -647, -134, 1869, -7008]], ![![-9362, -3894, -3438, -944, -839]]]
  g := ![![![-96115, 27322, -21224, -137586, 175320], ![424564, -120685, 93754, 607748, -774432], ![-1875396, 533091, -414107, -2684548, 3420816], ![5079719, -1443943, 1121644, 7271403, -9265656], ![1071434, -304560, 236578, 1533708, -1954343]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [34, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 46], [0, 1]]
 g := ![![[41, 18], [15, 2], [42, 32], [0, 21], [1]], ![[0, 29], [0, 45], [37, 15], [7, 26], [1]]]
 h' := ![![[16, 46], [7, 26], [29, 7], [0, 19], [13, 16], [0, 1]], ![[0, 1], [0, 21], [0, 40], [22, 28], [34, 31], [16, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [44, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [34, 31, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25511, 75732, 74927, -5781, 87615]
  a := ![-12, 6, 16, -18, 49]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-119710, -42526, 74927, -5781, 87615]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1356, 723, 90, 573, -731]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![1356, 723, 90, 573, -731]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![19, 18, 1, 0, 0], ![31, 3, 0, 1, 0], ![37, 3, 0, 0, 1]] where
  M :=![![![1356, 723, 90, 573, -731], ![-5947, -3188, -392, -2527, 3221], ![26213, 14073, 1723, 11157, -14219], ![-70968, -38118, -4666, -30217, 38504], ![-14974, -8042, -986, -6374, 8121]]]
  hmulB := by decide  
  f := ![![![-344, -239, 52, 43, -49]], ![![-417, -644, -254, -105, 271]], ![![-261, -314, -79, -26, 86]], ![![-261, -189, 32, 29, -30]], ![![-321, -241, 32, 32, -29]]]
  g := ![![![190, -9, 90, 573, -731], ![-837, 38, -392, -2527, 3221], ![3696, -165, 1723, 11157, -14219], ![-10005, 447, -4666, -30217, 38504], ![-2109, 95, -986, -6374, 8121]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [18, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 46], [0, 1]]
 g := ![![[6, 34], [7, 24], [26, 9], [16, 8], [1]], ![[0, 13], [0, 23], [41, 38], [45, 39], [1]]]
 h' := ![![[33, 46], [15, 38], [2, 27], [41, 3], [29, 33], [0, 1]], ![[0, 1], [0, 9], [0, 20], [46, 44], [37, 14], [33, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [34, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [18, 14, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6645, 11326, 9692, 829, 9012]
  a := ![4, -2, -5, 2, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11418, -4099, 9692, 829, 9012]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-435629, -740286, -626824, -55458, -579974]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![-435629, -740286, -626824, -55458, -579974]] 
 ![![47, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-435629, -740286, -626824, -55458, -579974], ![-2678038, -4550905, -3853380, -340926, -3565366], ![-16463126, -27976526, -23688527, -2095838, -21917942], ![-42371616, -72004016, -60967904, -5394123, -56410912], ![-38698572, -65762240, -55682808, -4926524, -51520851]]]
  hmulB := by decide  
  f := ![![![-1192479, -645646, -77504, -512002, 651674]], ![![-445280, -241425, -28884, -191462, 243642]], ![![-1337051, -722004, -87223, -572496, 728956]], ![![846956, 453096, 55968, 359141, -457928]], ![![133358, 71084, 8856, 56336, -71871]]]
  g := ![![![874997, -740286, -626824, -55458, -579974], ![5379024, -4550905, -3853380, -340926, -3565366], ![33067367, -27976526, -23688527, -2095838, -21917942], ![85106500, -72004016, -60967904, -5394123, -56410912], ![77728914, -65762240, -55682808, -4926524, -51520851]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-323031, -173544, -21224, -137586, 175320]] ![![1356, 723, 90, 573, -731]]
  ![![7176652988, 3855601215, 471498262, 3056599239, -3894903131]] where
 M := ![![![7176652988, 3855601215, 471498262, 3056599239, -3894903131]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![7176652988, 3855601215, 471498262, 3056599239, -3894903131]] ![![-435629, -740286, -626824, -55458, -579974]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![16074, 7661, -94, 7097, -10293]]]
 hmul := by decide  
 g := ![![![![342, 163, -2, 151, -219]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![368, 675, 608, 55, 569]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![368, 675, 608, 55, 569]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![4, 1, 2, 15, 1]] where
  M :=![![![368, 675, 608, 55, 569], ![2625, 4406, 3724, 317, 3505], ![16257, 27477, 23101, 2041, 21329], ![41112, 70062, 59458, 5293, 54904], ![37508, 63914, 54264, 4816, 50187]]]
  hmulB := by decide  
  f := ![![![2292, 1235, 150, 979, -1247]], ![![-10151, -5458, -666, -4327, 5513]], ![![44873, 24113, 2947, 19117, -24359]], ![![-121568, -65318, -7986, -51783, 65984]], ![![-33215, -17846, -2182, -14148, 18028]]]
  g := ![![![-36, 2, -10, -160, 569], ![-215, 17, -62, -986, 3505], ![-1303, 116, -369, -5998, 21329], ![-3368, 286, -950, -15439, 54904], ![-3080, 259, -870, -14113, 50187]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [38, 5, 11, 8, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 14, 16, 10], [33, 30, 26, 34], [0, 8, 11, 9], [0, 1]]
 g := ![![[22, 39, 39, 6], [40, 10, 52], [30, 6, 22, 52], [0, 45, 1], []], ![[3, 1, 21, 18, 4, 43], [47, 34, 44], [37, 48, 33, 0, 33, 42], [12, 26, 36], [0, 13, 33, 33, 33, 46]], ![[45, 12, 32, 9, 19, 2], [4, 47, 44], [9, 5, 39, 32, 6, 31], [36, 30, 29], [52, 6, 40, 39, 32, 31]], ![[0, 43, 46, 20, 10, 52], [38, 41, 52], [26, 14, 6, 18, 23, 4], [18, 21, 40], [20, 32, 45, 45, 21, 40]]]
 h' := ![![[12, 14, 16, 10], [4, 10, 51, 18], [26, 46, 23, 30], [0, 39, 2, 30], [0, 0, 0, 1], [0, 1]], ![[33, 30, 26, 34], [23, 2, 37, 30], [22, 48, 31, 37], [38, 50, 42, 6], [32, 42, 35, 6], [12, 14, 16, 10]], ![[0, 8, 11, 9], [43, 19, 40, 48], [6, 24, 34, 16], [48, 10, 22, 34], [41, 2, 41, 20], [33, 30, 26, 34]], ![[0, 1], [30, 22, 31, 10], [19, 41, 18, 23], [11, 7, 40, 36], [35, 9, 30, 26], [0, 8, 11, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [16, 37, 29], []]
 b := ![[], [], [33, 40, 23, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [38, 5, 11, 8, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![756962102889, 1467209917246, 1302904514785, 49891235265, 1299447608082]
  a := ![-21, 6, 21, -31, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-83789213763, 3165326588, -24452654743, -366826846905, 1299447608082]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2292, 1235, 150, 979, -1247]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![2292, 1235, 150, 979, -1247]] 
 ![![53, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![2292, 1235, 150, 979, -1247], ![-10151, -5458, -666, -4327, 5513], ![44873, 24113, 2947, 19117, -24359], ![-121568, -65318, -7986, -51783, 65984], ![-25638, -13776, -1684, -10922, 13917]]]
  hmulB := by decide  
  f := ![![![368, 675, 608, 55, 569]], ![![237, 427, 380, 34, 356]], ![![397, 684, 585, 52, 542]], ![![984, 1704, 1466, 131, 1358]], ![![916, 1588, 1368, 122, 1269]]]
  g := ![![![-471, 1235, 150, 979, -1247], ![2081, -5458, -666, -4327, 5513], ![-9193, 24113, 2947, 19117, -24359], ![24902, -65318, -7986, -51783, 65984], ![5252, -13776, -1684, -10922, 13917]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![368, 675, 608, 55, 569]] ![![2292, 1235, 150, 979, -1247]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47558, 37061, -3314, -3985, 2673]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![47558, 37061, -3314, -3985, 2673]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![56, 27, 1, 0, 0], ![42, 4, 0, 1, 0], ![47, 39, 0, 0, 1]] where
  M :=![![![47558, 37061, -3314, -3985, 2673], ![29305, 62284, 32484, 14609, -34455], ![-230711, -197271, 775, 11769, 3033], ![99400, -220, -74916, -41933, 76680], ![166716, 105890, -32648, -24364, 31361]]]
  hmulB := by decide  
  f := ![![![-7602, -11201, -9516, -923, -8481]], ![![-38713, -67892, -57410, -5013, -53481]], ![![-29124, -48787, -41309, -3700, -38076]], ![![-18760, -30826, -26108, -2371, -23946]], ![![-41441, -70461, -59634, -5298, -55159]]]
  g := ![![![4659, 648, -3314, -3985, 2673], ![-13288, 7975, 32484, 14609, -34455], ![-15440, -6501, 775, 11769, 3033], ![41558, -13564, -74916, -41933, 76680], ![26175, -2343, -32648, -24364, 31361]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [12, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 58], [0, 1]]
 g := ![![[45, 5], [53, 19], [22], [21, 41], [50, 1]], ![[0, 54], [0, 40], [22], [6, 18], [41, 58]]]
 h' := ![![[50, 58], [13, 8], [51, 45], [43, 9], [49, 10], [0, 1]], ![[0, 1], [0, 51], [0, 14], [21, 50], [18, 49], [50, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [48, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [12, 9, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13925, 100636, 110445, -18919, 143657]
  a := ![-22, 6, 19, -28, 67]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-205564, -142514, 110445, -18919, 143657]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-173, -6, 6, -2, 2]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-173, -6, 6, -2, 2]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![39, 15, 1, 0, 0], ![42, 47, 0, 1, 0], ![45, 58, 0, 0, 1]] where
  M :=![![![-173, -6, 6, -2, 2], ![18, -161, 2, 22, -14], ![-158, -58, -149, -114, 194], ![792, 572, 188, 153, -296], ![202, 218, 136, 82, -165]]]
  hmulB := by decide  
  f := ![![![-28043, -47654, -40350, -3570, -37334]], ![![-172390, -292951, -248050, -21946, -229510]], ![![-80327, -136503, -115581, -10226, -106942]], ![![-203520, -345851, -292842, -25909, -270954]], ![![-233079, -396082, -335374, -29672, -310307]]]
  g := ![![![-7, -2, 6, -2, 2], ![-6, -7, 2, 22, -14], ![29, -63, -149, -114, 194], ![6, 131, 188, 153, -296], ![-19, 66, 136, 82, -165]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [15, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 58], [0, 1]]
 g := ![![[22, 4], [44, 35], [26], [0, 15], [24, 1]], ![[0, 55], [58, 24], [26], [6, 44], [48, 58]]]
 h' := ![![[24, 58], [48, 57], [23, 34], [0, 47], [53, 30], [0, 1]], ![[0, 1], [0, 2], [13, 25], [7, 12], [6, 29], [24, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [22, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [15, 35, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14967, 47102, 47062, -4198, 55956]
  a := ![-12, 4, 12, -15, 40]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-70545, -62830, 47062, -4198, 55956]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4584427, -893840, -837736, -441270, 568678]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-4584427, -893840, -837736, -441270, 568678]] 
 ![![59, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-4584427, -893840, -837736, -441270, 568678], ![4608470, -1044951, -780674, 403470, -2451850], ![-13873130, -12151010, -10422615, -1530318, -7417610], ![-8546824, -27587854, -23206202, -1357697, -24017128], ![-12271882, -25802410, -21789608, -1664406, -21125115]]]
  hmulB := by decide  
  f := ![![![-429773, 172592, 473308, 254082, -486658]], ![![-182301, -10987, 127250, 71664, -129788]], ![![14656, 30586, 15393, 6426, -15866]], ![![57285, 145270, 84758, 39925, -90470]], ![![-6504, 54574, 52784, 26574, -55255]]]
  g := ![![![283157, -893840, -837736, -441270, 568678], ![507509, -1044951, -780674, 403470, -2451850], ![4707060, -12151010, -10422615, -1530318, -7417610], ![11093333, -27587854, -23206202, -1357697, -24017128], ![10299644, -25802410, -21789608, -1664406, -21125115]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![47558, 37061, -3314, -3985, 2673]] ![![-173, -6, 6, -2, 2]]
  ![![-9652998, -7756663, 467604, 707503, -328139]] where
 M := ![![![-9652998, -7756663, 467604, 707503, -328139]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-9652998, -7756663, 467604, 707503, -328139]] ![![-4584427, -893840, -837736, -441270, 568678]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-35686858, -4842779, -4755164, -3391379, 6473067]]]
 hmul := by decide  
 g := ![![![![-604862, -82081, -80596, -57481, 109713]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1351128, -1039175, -1925236, -1018229, 1990609]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![1351128, -1039175, -1925236, -1018229, 1990609]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![34, 50, 49, 1, 0], ![44, 11, 9, 0, 1]] where
  M :=![![![1351128, -1039175, -1925236, -1018229, 1990609], ![14025961, 14267162, 1943338, 268293, -2265703], ![-12401687, -1565667, 7952567, 4542621, -8108999], ![-23156896, -31528196, -10186900, -3892107, 11037728], ![-3300058, -12723412, -8655324, -4115050, 9105405]]]
  hmulB := by decide  
  f := ![![![230294668, 391353909, 331370666, 29317743, 306603409]], ![![1415746073, 2405836274, 2037091440, 180231465, 1884829961]], ![![8703223945, 14789787265, 12522941953, 1107964129, 11586927385]], ![![8647132359, 14694465063, 12442229917, 1100823322, 11512247465]], ![![2040872220, 3468148949, 2936582317, 259813312, 2717090703]]]
  g := ![![![-846162, 458616, 492664, -1018229, 1990609], ![1714671, 422545, 150628, 268293, -2265703], ![3113855, -2286848, -2322211, 4542621, -8108999], ![-6171890, 682986, 1330931, -3892107, 11037728], ![-4328298, 1522453, 1820221, -4115050, 9105405]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [35, 14, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 1, 40], [2, 59, 21], [0, 1]]
 g := ![![[43, 32, 9], [3, 58], [4, 1, 5], [60, 28, 57], [1]], ![[57, 43, 50, 17], [30, 46], [33, 28, 26, 44], [36, 55, 48, 37], [17, 39, 40, 11]], ![[57, 43, 41, 32], [23, 9], [3, 0, 4, 8], [42, 35, 56, 55], [51, 28, 40, 50]]]
 h' := ![![[20, 1, 40], [36, 48, 58], [43, 36, 34], [35, 15, 35], [26, 47, 22], [0, 1]], ![[2, 59, 21], [32, 4, 35], [17, 6, 30], [12, 20, 42], [24, 24, 6], [20, 1, 40]], ![[0, 1], [33, 9, 29], [17, 19, 58], [0, 26, 45], [53, 51, 33], [2, 59, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 31], []]
 b := ![[], [35, 25, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [35, 14, 39, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5154923067, -11359699956, -10489071784, 11812554, -11055057432]
  a := ![65, -14, -66, 81, -188]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7883048805, 1797627936, 1449633278, 11812554, -11055057432]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1461595819, -198242318, -194665812, -138894488, 265209760]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-1461595819, -198242318, -194665812, -138894488, 265209760]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![12, 25, 1, 0, 0], ![27, 47, 0, 1, 0], ![14, 3, 0, 0, 1]] where
  M :=![![![-1461595819, -198242318, -194665812, -138894488, 265209760], ![1881626752, 255978013, 251247446, 178825544, -340685056], ![-2418727456, -324343096, -319038133, -229773316, 442481248], ![2775113480, 386605530, 378130974, 263927849, -493677400], ![1054562902, 152251226, 148150000, 100404650, -182436405]]]
  hmulB := by decide  
  f := ![![![857801, 1049478, 277696, 100008, -309920]], ![![-1949632, -1211631, 387518, 265264, -349504]], ![![-676324, -357835, 190065, 120732, -180672]], ![![-1025321, -379645, 423220, 240297, -405336]], ![![171692, 258349, 96370, 38290, -102733]]]
  g := ![![![14944401, 170505158, -194665812, -138894488, 265209760], ![-19541664, -219802517, 251247446, 178825544, -340685056], ![23260200, 280713317, -319038133, -229773316, 442481248], ![-32410271, -327708943, 378130974, 263927849, -493677400], ![-14427098, -126609969, 148150000, 100404650, -182436405]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [25, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 60], [0, 1]]
 g := ![![[19, 22], [4], [47, 5], [44, 57], [13, 1]], ![[0, 39], [4], [51, 56], [53, 4], [26, 60]]]
 h' := ![![[13, 60], [34, 49], [45, 2], [59, 35], [41, 22], [0, 1]], ![[0, 1], [0, 12], [10, 59], [26, 26], [22, 39], [13, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [55, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [25, 48, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3422, 100234, 119899, -27494, 165496]
  a := ![24, -5, -23, 31, -71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-49456, -34451, 119899, -27494, 165496]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![1351128, -1039175, -1925236, -1018229, 1990609]] ![![-1461595819, -198242318, -194665812, -138894488, 265209760]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![36896582, 5006941, 4916356, 3506341, -6692493]]]
 hmul := by decide  
 g := ![![![![604862, 82081, 80596, 57481, -109713]]]]
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
  g := ![3, 1, 1, 2, 3, 3, 2, 3, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB6026I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0]
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
    · exact ![841, 841, 29]
    · exact ![28629151]
    · exact ![69343957]
    · exact ![2825761, 41]
    · exact ![79507, 43, 43]
    · exact ![2209, 2209, 47]
    · exact ![7890481, 53]
    · exact ![3481, 3481, 59]
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
  β := ![I29N0, I29N1, I29N2, I41N1, I43N1, I43N2, I47N0, I47N1, I47N2, I53N1, I59N0, I59N1, I59N2, I61N1]
  Il := ![[I29N0, I29N1, I29N2], [], [], [I41N1], [I43N1, I43N2], [I47N0, I47N1, I47N2], [I53N1], [I59N0, I59N1, I59N2], [I61N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
