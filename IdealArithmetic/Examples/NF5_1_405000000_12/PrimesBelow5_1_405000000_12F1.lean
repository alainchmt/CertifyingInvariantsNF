
import IdealArithmetic.Examples.NF5_1_405000000_12.RI5_1_405000000_12
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [21, 15, 13, 28, 8, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 18, 19, 27, 4], [4, 26, 13, 3, 22], [14, 1, 27, 22, 25], [8, 12, 28, 6, 7], [0, 1]]
 g := ![![[3, 15, 12, 12, 1], [25, 23, 18, 13], [7, 21, 1], []], ![[1, 19, 2, 25, 3, 1, 18, 23], [0, 12, 14, 5], [0, 6, 24, 13, 8, 24, 1, 23], [7, 1, 14, 16, 4, 1, 1, 6]], ![[6, 8, 2, 23, 17, 23, 24, 1], [27, 4, 28, 9], [23, 25, 24, 10, 22, 14, 12, 6], [7, 8, 9, 17, 11, 27, 24, 5]], ![[26, 21, 12, 12, 14, 10, 15, 1], [24, 21, 22, 9], [5, 9, 24, 1, 3, 8, 12, 23], [26, 3, 22, 28, 22, 19, 2, 23]], ![[6, 1, 9, 21, 6, 2, 7, 4], [22, 27, 22, 6], [16, 1, 15, 6, 12, 7, 23, 24], [18, 5, 15, 15, 22, 14, 23, 24]]]
 h' := ![![[24, 18, 19, 27, 4], [1, 21, 18, 10, 1], [27, 5, 8, 9, 10], [0, 0, 0, 1], [0, 1]], ![[4, 26, 13, 3, 22], [16, 13, 7, 13, 10], [4, 15, 3, 13, 11], [18, 6, 22, 3, 10], [24, 18, 19, 27, 4]], ![[14, 1, 27, 22, 25], [8, 22, 25, 20, 2], [16, 6, 20, 22, 26], [4, 18, 13, 13, 16], [4, 26, 13, 3, 22]], ![[8, 12, 28, 6, 7], [9, 12, 20, 13, 6], [22, 2, 6, 6, 3], [23, 19, 22, 6, 25], [14, 1, 27, 22, 25]], ![[0, 1], [9, 19, 17, 2, 10], [23, 1, 21, 8, 8], [18, 15, 1, 6, 7], [8, 12, 28, 6, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 12, 16, 18], [], [], []]
 b := ![[], [17, 2, 6, 23, 10], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [21, 15, 13, 28, 8, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2761275918072, 780545184336, 1422004445566, -5033386913942, -2251950601058]
  a := ![0, -7, 2, -8, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![95216410968, 26915351184, 49034636054, -173565065998, -77653469002]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 20511149 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

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


def P31P0 : CertificateIrreducibleZModOfList' 31 5 2 4 [5, 2, 13, 10, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 16, 12, 27, 7], [13, 13, 26, 3, 10], [2, 7, 27, 18, 4], [24, 25, 28, 14, 10], [0, 1]]
 g := ![![[21, 1, 9, 22, 9], [25, 11, 6, 28, 9], [6, 27, 1], []], ![[24, 16, 23, 18, 28, 6, 14, 10], [2, 10, 2, 24, 25, 7, 0, 18], [20, 25, 29, 26, 27, 16, 19, 14], [0, 6, 6, 17, 6, 0, 24, 2]], ![[25, 9, 6, 14, 4, 8, 24, 28], [17, 13, 25, 0, 12, 25, 25, 14], [13, 4, 18, 8, 14, 10, 1, 25], [11, 20, 15, 28, 10, 23, 0, 8]], ![[9, 3, 9, 20, 7, 4], [11, 0, 17, 25, 21, 7, 17, 16], [10, 3, 29, 26, 3, 14, 18, 28], [1, 21, 20, 2, 23, 4, 19, 2]], ![[12, 11, 11, 8, 9, 10, 20, 1], [4, 28, 19, 14, 28, 9, 4, 7], [11, 12, 0, 6, 16, 10, 7, 2], [30, 22, 15, 15, 8, 8, 14, 8]]]
 h' := ![![[19, 16, 12, 27, 7], [30, 20, 11, 20, 3], [1, 8, 18, 21, 3], [0, 0, 0, 1], [0, 1]], ![[13, 13, 26, 3, 10], [21, 8, 26, 11, 20], [0, 22, 19, 17, 21], [8, 0, 18, 25, 23], [19, 16, 12, 27, 7]], ![[2, 7, 27, 18, 4], [6, 6, 13, 8, 28], [21, 4, 30, 22, 19], [3, 21, 16, 30, 24], [13, 13, 26, 3, 10]], ![[24, 25, 28, 14, 10], [9, 16, 20, 1], [30, 0, 30, 18, 2], [3, 8, 29, 14, 10], [2, 7, 27, 18, 4]], ![[0, 1], [7, 12, 23, 22, 11], [6, 28, 27, 15, 17], [3, 2, 30, 23, 5], [24, 25, 28, 14, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 22, 24, 1], [], [], []]
 b := ![[], [30, 6, 9, 13, 22], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 5
  hpos := by decide
  P := [5, 2, 13, 10, 4, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14550021520521209, 10314294845584998, -5575439674036474, -16793568980177220, 6871274947032392]
  a := ![3, -62, -1, -63, -58]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![469355532920039, 332719188567258, -179852892710854, -541728031618620, 221654030549432]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9218, -7433, 5424, 9232, -7067]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-9218, -7433, 5424, 9232, -7067]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![32, 5, 1, 0, 0], ![25, 10, 0, 1, 0], ![10, 7, 0, 0, 1]] where
  M :=![![![-9218, -7433, 5424, 9232, -7067], ![-42402, -6531, -33330, 85848, 51062], ![153186, 124575, -92379, -151730, 120634], ![383103, 62890, 292970, -769569, -449625], ![-768195, -518877, 240220, 926946, -285158]]]
  hmulB := by decide  
  f := ![![![333251386, 663039281, 494004146, 126015542, 120757553]], ![![724545318, 1441559275, 1074047478, 273978952, 262547062]], ![![407416544, 810598630, 603944605, 154060278, 147632104]], ![![434343181, 864171901, 643859796, 164242263, 157389228]], ![![228578029, 454780232, 338838464, 86434344, 82827852]]]
  g := ![![![-9268, -2092, 5424, 9232, -7067], ![-44126, -28535, -33330, 85848, 51062], ![153952, 34036, -92379, -151730, 120634], ![398474, 255165, 292970, -769569, -449625], ![-777765, -243063, 240220, 926946, -285158]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [30, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 36], [0, 1]]
 g := ![![[2, 21], [21], [5, 30], [11], [1]], ![[0, 16], [21], [18, 7], [11], [1]]]
 h' := ![![[14, 36], [3, 13], [35, 24], [15, 17], [7, 14], [0, 1]], ![[0, 1], [0, 24], [1, 13], [31, 20], [18, 23], [14, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [7, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [30, 23, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2025, -363, -1598, 4178, 2447]
  a := ![1, -6, 1, -7, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2157, -1386, -1598, 4178, 2447]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3689647, -7340934, -5469428, -1395198, -1336982]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-3689647, -7340934, -5469428, -1395198, -1336982]] 
 ![![37, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![-3689647, -7340934, -5469428, -1395198, -1336982], ![-8021892, -15960417, -11891472, -3033396, -2906828], ![-8720484, -17350320, -12927021, -3297556, -3159964], ![-5468946, -10881046, -8107028, -2068023, -1981734], ![-587424, -1168734, -870772, -222126, -212857]]]
  hmulB := by decide  
  f := ![![![1025, 618, -228, -1254, 182]], ![![916, 503, -96, -1204, 12]], ![![-270, -172, 51, 360, -64]], ![![702, 866, -1108, -135, 1470]], ![![2242, 1198, -60, -3162, -113]]]
  g := ![![![8999505, -7340934, -5469428, -1395198, -1336982], ![19566436, -15960417, -11891472, -3033396, -2906828], ![21270362, -17350320, -12927021, -3297556, -3159964], ![13339454, -10881046, -8107028, -2068023, -1981734], ![1432790, -1168734, -870772, -222126, -212857]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-319, -91, 196, 28, 76]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-319, -91, 196, 28, 76]] 
 ![![37, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![-319, -91, 196, 28, 76], ![456, 161, -238, -160, -40], ![-120, -111, 321, -238, -280], ![-1068, -638, 246, 1283, -176], ![-18, 487, -804, 436, 1339]]]
  hmulB := by decide  
  f := ![![![-2113801099, -4205631391, -3133446710, -799311312, -765959852]], ![![-2009491767, -3998096916, -2978821124, -759867852, -728162180]], ![![-1791789419, -3564955014, -2656104523, -677546034, -649275260]], ![![-1398664661, -2782791629, -2073346060, -528890105, -506822036]], ![![-1608728758, -3200736421, -2384739906, -608323600, -582941149]]]
  g := ![![![-156, -91, 196, 28, 76], ![185, 161, -238, -160, -40], ![204, -111, 321, -238, -280], ![-317, -638, 246, 1283, -176], ![-1089, 487, -804, 436, 1339]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2

def I37N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5160010096, -10266387144, -7649071926, -1951202712, -1869788301]] i)))

def SI37N3: IdealEqSpanCertificate' Table ![![-5160010096, -10266387144, -7649071926, -1951202712, -1869788301]] 
 ![![37, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-5160010096, -10266387144, -7649071926, -1951202712, -1869788301], ![-11218729806, -22320852349, -16630368864, -4242242868, -4065234246], ![-12195702738, -24264643572, -18078609481, -4611674748, -4419251490], ![-7648389567, -15217281918, -11337784392, -2892156835, -2771480883], ![-821513007, -1634487222, -1217790654, -310646370, -297684574]]]
  hmulB := by decide  
  f := ![![![-4924, -606, -4458, 10614, 6567]], ![![-3726, 263, -4944, 9240, 7182]], ![![-18, 36, -229, 300, 228]], ![![-13159, -8040, 2124, 17519, -2187]], ![![-8157, 1578, -12540, 21198, 18491]]]
  g := ![![![16108444649, -10266387144, -7649071926, -1951202712, -1869788301], ![35022467940, -22320852349, -16630368864, -4242242868, -4065234246], ![38072367858, -24264643572, -18078609481, -4611674748, -4419251490], ![23876631580, -15217281918, -11337784392, -2892156835, -2771480883], ![2564587383, -1634487222, -1217790654, -310646370, -297684574]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N3 : Nat.card (O ⧸ I37N3) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N3)

lemma isPrimeI37N3 : Ideal.IsPrime I37N3 := prime_ideal_of_norm_prime hp37.out _ NI37N3
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-9218, -7433, 5424, 9232, -7067]] ![![-3689647, -7340934, -5469428, -1395198, -1336982]]
  ![![2, -1, 4, -6, -5]] where
 M := ![![![2, -1, 4, -6, -5]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![2, -1, 4, -6, -5]] ![![-319, -91, 196, 28, 76]]
  ![![4924, 606, 4458, -10614, -6567]] where
 M := ![![![4924, 606, 4458, -10614, -6567]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N2 : IdealMulLeCertificate' Table 
  ![![4924, 606, 4458, -10614, -6567]] ![![-5160010096, -10266387144, -7649071926, -1951202712, -1869788301]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2, I37N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
    exact isPrimeI37N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1 ⊙ MulI37N2)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-120967, 122007, 390974, 56644, 100930]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-120967, 122007, 390974, 56644, 100930]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![32, 30, 38, 1, 0], ![32, 7, 32, 0, 1]] where
  M :=![![![-120967, 122007, 390974, 56644, 100930], ![605580, 686085, 130726, 87796, 24716], ![74148, 493023, 598289, 119658, 150876], ![149838, 339148, 308002, 70545, 76082], ![-226512, -59311, 214082, 17768, 57543]]]
  hmulB := by decide  
  f := ![![![247741, 124095, 13652, -366776, -38690]], ![![-232140, -588229, 981742, -396728, -1389724]], ![![-4169172, -2106513, -191501, 6143910, 596268]], ![![-3794150, -2160274, 338312, 5209649, -192322]], ![![-2718344, -1498210, 138006, 3810196, 11871]]]
  g := ![![![-125935, -55703, -121738, 56644, 100930], ![-73044, -51727, -97474, 87796, 24716], ![-209340, -101289, -214067, 119658, 150876], ![-110786, -56336, -117252, 70545, 76082], ![-64304, -24272, -56158, 17768, 57543]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [12, 34, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 34, 36], [27, 6, 5], [0, 1]]
 g := ![![[35, 10, 32], [9, 23], [40, 32], [9, 17, 1], []], ![[35, 37, 28, 10], [33, 21], [27, 18], [32, 7, 26, 25], [3, 25]], ![[8, 33, 27, 4], [27, 16], [1, 2], [21, 39, 18, 40], [34, 25]]]
 h' := ![![[31, 34, 36], [14, 22, 27], [32, 12, 8], [15, 23, 14], [0, 0, 1], [0, 1]], ![[27, 6, 5], [5, 29, 11], [14, 34, 29], [25, 25, 10], [23, 25, 6], [31, 34, 36]], ![[0, 1], [9, 31, 3], [13, 36, 4], [5, 34, 17], [34, 16, 34], [27, 6, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 17], []]
 b := ![[], [35, 16, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [12, 34, 24, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-71561836, 4757115, -89070519, 169599520, 133476756]
  a := ![1, 25, -3, 24, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-238292748, -146769897, -263539231, 169599520, 133476756]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6026567, -10699817, 15854174, -3128072, -22266936]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-6026567, -10699817, 15854174, -3128072, -22266936]] 
 ![![41, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-6026567, -10699817, 15854174, -3128072, -22266936], ![-133601616, -63229345, -15143490, 203587692, 32021584], ![96064752, 177247515, -266817037, 60357866, 375153800], ![1192262208, 569327096, 124461394, -1808868217, -270448860], ![-886971210, -942514971, 1001030186, 531513504, -1366853249]]]
  hmulB := by decide  
  f := ![![![-5747973583, -11434813161, -8518651848, -2173162180, -2082335064]], ![![-2828232558, -5626502241, -4191683786, -1069313824, -1024634384]], ![![-611704462, -1216956047, -906641735, -231284378, -221624064]], ![![-2170496938, -4317953372, -3216797838, -820621301, -786328180]], ![![-583112966, -1159999175, -864156536, -220453812, -211237745]]]
  g := ![![![7017623, -10699817, 15854174, -3128072, -22266936], ![-47402450, -63229345, -15143490, 203587692, 32021584], ![-119667848, 177247515, -266817037, 60357866, 375153800], ![417107370, 569327096, 124461394, -1808868217, -270448860], ![295181996, -942514971, 1001030186, 531513504, -1366853249]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4919, -9788, -7290, -1860, -1782]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-4919, -9788, -7290, -1860, -1782]] 
 ![![41, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![-4919, -9788, -7290, -1860, -1782], ![-10692, -21275, -15856, -4044, -3876], ![-11628, -23132, -17231, -4396, -4212], ![-7290, -14506, -10808, -2757, -2642], ![-786, -1560, -1158, -296, -283]]]
  hmulB := by decide  
  f := ![![![77, 28, -10, -76, -10]], ![![53, 17, -2, -56, -14]], ![![-2, -4, -3, 12, 0]], ![![55, 42, -50, -25, 56]], ![![102, 40, 18, -152, -39]]]
  g := ![![![10237, -9788, -7290, -1860, -1782], ![22255, -21275, -15856, -4044, -3876], ![24194, -23132, -17231, -4396, -4212], ![15173, -14506, -10808, -2757, -2642], ![1630, -1560, -1158, -296, -283]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-120967, 122007, 390974, 56644, 100930]] ![![-6026567, -10699817, 15854174, -3128072, -22266936]]
  ![![77, 28, -10, -76, -10]] where
 M := ![![![77, 28, -10, -76, -10]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![77, 28, -10, -76, -10]] ![![-4919, -9788, -7290, -1860, -1782]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-426257947, -848085391, -631874304, -161184894, -154459416]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-426257947, -848085391, -631874304, -161184894, -154459416]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![17, 16, 30, 36, 1]] where
  M :=![![![-426257947, -848085391, -631874304, -161184894, -154459416], ![-926756496, -1843880287, -1373800994, -350443068, -335820744], ![-1007462232, -2004452929, -1493437219, -380961086, -365065392], ![-631817928, -1257068756, -936591346, -238915203, -228946408], ![-67863516, -135021669, -100599216, -25661866, -24591119]]]
  hmulB := by decide  
  f := ![![![-1, -5, 50, -70, -16]], ![![-96, -139, 130, 88, -248]], ![![-744, -267, -227, 1210, 424]], ![![1320, 1430, -1542, -757, 2120]], ![![601, 966, -1342, 112, 1913]]]
  g := ![![![51152375, 37750355, 93067632, 125566374, -154459416], ![111213864, 82075619, 202344682, 273002412, -335820744], ![120898824, 89223101, 219965687, 296776582, -365065392], ![75820256, 55955204, 137948858, 186119895, -228946408], ![8143849, 6010145, 14817078, 19991126, -24591119]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [21, 16, 39, 24, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 15, 9, 35], [5, 16, 8, 19], [23, 11, 26, 32], [0, 1]]
 g := ![![[25, 10, 9, 11], [7, 6, 0, 15], [6, 20, 11], [19, 1], []], ![[38, 24, 9, 41, 29, 14], [41, 21, 41, 38, 7, 9], [35, 3, 14], [14, 23, 25, 39, 40, 40], [40, 40, 21]], ![[22, 2, 7, 13, 37, 26], [40, 18, 37, 33, 8, 22], [3, 32, 6], [12, 7, 41, 6, 22, 8], [11, 25, 17]], ![[17, 31, 34, 13, 34, 26], [42, 37, 35, 12], [28, 19, 25], [37, 33, 10, 16, 12, 28], [19, 7, 35]]]
 h' := ![![[34, 15, 9, 35], [25, 0, 28, 21], [18, 17, 28, 31], [31, 19, 17, 21], [0, 0, 1], [0, 1]], ![[5, 16, 8, 19], [32, 5, 12, 3], [5, 1, 13, 31], [3, 18, 32, 10], [15, 13, 2, 9], [34, 15, 9, 35]], ![[23, 11, 26, 32], [22, 20, 32, 14], [40, 39, 11, 24], [24, 40, 31, 7], [9, 18, 10, 10], [5, 16, 8, 19]], ![[0, 1], [18, 18, 14, 5], [27, 29, 34], [20, 9, 6, 5], [1, 12, 30, 24], [23, 11, 26, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [26, 33, 39], []]
 b := ![[], [], [20, 2, 23, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [21, 16, 39, 24, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19016918445, 20418089124, -21905545248, -11065877940, 29941141848]
  a := ![-1, -7, 5, -5, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11394941697, -10666050708, -21398600016, -25324348476, 29941141848]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 5, -50, 70, 16]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![1, 5, -50, 70, 16]] 
 ![![43, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![1, 5, -50, 70, 16], ![96, 139, -130, -88, 248], ![744, 267, 227, -1210, -424], ![-1320, -1430, 1542, 757, -2120], ![-2196, -377, -1686, 4450, 2541]]]
  hmulB := by decide  
  f := ![![![426257947, 848085391, 631874304, 161184894, 154459416]], ![![318941742, 634568419, 472791398, 120604416, 115572168]], ![![251427791, 500242254, 372710377, 95074736, 91107720]], ![![282343779, 561752891, 418539478, 106765287, 102310480]], ![![170098805, 338429612, 252150288, 64321048, 61637237]]]
  g := ![![![-27, 5, -50, 70, 16], ![-68, 139, -130, -88, 248], ![637, 267, 227, -1210, -424], ![505, -1430, 1542, 757, -2120], ![-2685, -377, -1686, 4450, 2541]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-426257947, -848085391, -631874304, -161184894, -154459416]] ![![1, 5, -50, 70, 16]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![-43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![301163424611, 599196562312, 446437246078, 113881732794, 109129989616]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![301163424611, 599196562312, 446437246078, 113881732794, 109129989616]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![2, 38, 36, 1, 0], ![10, 12, 34, 0, 1]] where
  M :=![![![301163424611, 599196562312, 446437246078, 113881732794, 109129989616], ![654779937696, 1302754105125, 970629659036, 247598040816, 237266951944], ![711800855832, 1416203267098, 1055156064309, 269159892076, 257929129688], ![446397420216, 888154994116, 661728545504, 168800417225, 161757178492], ![47947516698, 95396667840, 71076218330, 18130841398, 17374327605]]]
  hmulB := by decide  
  f := ![![![13237, 17052, -21246, -3226, 29432]], ![![176592, 73835, 40556, -284400, -71768]], ![![-215304, -283478, 358235, 43228, -497032]], ![![-55178, -170918, 298896, -143099, -424300]], ![![-75448, -152716, 238016, -68590, -335451]]]
  g := ![![![-21657445471, -107188705516, -156674995350, 113881732794, 109129989616], ![-47086929008, -233046273813, -340637790988, 247598040816, 237266951944], ![-51187451600, -253340897618, -370301924677, 269159892076, 257929129688], ![-32101599982, -158879723454, -232230437092, 168800417225, 161757178492], ![-3448030684, -17065260352, -24943855544, 18130841398, 17374327605]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [23, 23, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 6, 44], [41, 40, 3], [0, 1]]
 g := ![![[0, 38, 2], [18, 29, 7], [16, 35, 6], [13, 41, 1], []], ![[35, 42, 17, 33], [46, 43, 36, 19], [37, 32, 0, 13], [20, 32, 39, 41], [4, 9]], ![[42, 9, 22, 3], [43, 2, 9, 9], [6, 10, 0, 7], [12, 9, 41, 14], [45, 9]]]
 h' := ![![[0, 6, 44], [9, 17, 7], [8, 9, 17], [30, 27, 37], [0, 0, 1], [0, 1]], ![[41, 40, 3], [23, 30, 41], [42, 0, 42], [10, 3, 36], [2, 30, 40], [0, 6, 44]], ![[0, 1], [11, 0, 46], [32, 38, 35], [35, 17, 21], [35, 17, 6], [41, 40, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 28], []]
 b := ![[], [12, 3, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [23, 23, 6, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14790839, 782860, 14768834, -32298178, -22319340]
  a := ![0, -4, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6437885, 31828632, 41199166, -32298178, -22319340]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13237, 17052, -21246, -3226, 29432]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![13237, 17052, -21246, -3226, 29432]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![41, 11, 1, 0, 0], ![19, 41, 0, 1, 0], ![40, 35, 0, 0, 1]] where
  M :=![![![13237, 17052, -21246, -3226, 29432], ![176592, 73835, 40556, -284400, -71768], ![-215304, -283478, 358235, 43228, -497032], ![-1579392, -667772, -346984, 2531791, 619372], ![1522806, 1404060, -1267450, -1248422, 1699787]]]
  hmulB := by decide  
  f := ![![![301163424611, 599196562312, 446437246078, 113881732794, 109129989616]], ![![654779937696, 1302754105125, 970629659036, 247598040816, 237266951944]], ![![431108097437, 857735265495, 639064029849, 163018923098, 156216918624]], ![![702435743263, 1397570382727, 1041273451946, 265618574761, 254535574700]], ![![744931538734, 1482120273185, 1104268172930, 281687905994, 269934409155]]]
  g := ![![![-4929, -13768, -21246, -3226, 29432], ![144428, 293617, 40556, -284400, -71768], ![88447, 242547, 358235, 43228, -497032], ![-1281531, -2602817, -346984, 2531791, 619372], ![196102, 149761, -1267450, -1248422, 1699787]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [28, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 46], [0, 1]]
 g := ![![[32, 42], [12, 4], [30, 37], [0, 9], [1]], ![[0, 5], [0, 43], [13, 10], [20, 38], [1]]]
 h' := ![![[44, 46], [40, 29], [6, 2], [0, 15], [19, 44], [0, 1]], ![[0, 1], [0, 18], [0, 45], [2, 32], [28, 3], [44, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [16, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [28, 3, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2315, 5749, -9966, 4420, 13951]
  a := ![13, -7, 4, -6, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4917, -11790, -9966, 4420, 13951]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![301163424611, 599196562312, 446437246078, 113881732794, 109129989616]] ![![13237, 17052, -21246, -3226, 29432]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20, 0, 4, 4, 29]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-20, 0, 4, 4, 29]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![45, 2, 1, 0, 0], ![16, 19, 0, 1, 0], ![11, 30, 0, 0, 1]] where
  M :=![![![-20, 0, 4, 4, 29], ![174, 79, -8, -216, -42], ![-126, -196, 295, -56, -390], ![-1257, -596, -136, 1907, 299], ![927, 990, -1032, -586, 1434]]]
  hmulB := by decide  
  f := ![![![650696, 1294598, 964536, 246046, 235777]], ![![1414662, 2814655, 2097104, 534948, 512630]], ![![634878, 1263132, 941095, 240066, 230047]], ![![721777, 1436055, 1069948, 272933, 261545]], ![![937757, 1865780, 1390124, 354606, 339811]]]
  g := ![![![-11, -18, 4, 4, 29], ![84, 103, -8, -216, -42], ![-155, 226, 295, -56, -390], ![-546, -859, -136, 1907, 299], ![773, -544, -1032, -586, 1434]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [10, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 52], [0, 1]]
 g := ![![[24, 16], [49], [34, 49], [17], [25, 1]], ![[0, 37], [49], [40, 4], [17], [50, 52]]]
 h' := ![![[25, 52], [47, 49], [31, 46], [2, 7], [15, 32], [0, 1]], ![[0, 1], [0, 4], [15, 7], [18, 46], [20, 21], [25, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [39, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [10, 28, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![922, 582, -231, -1244, 328]
  a := ![-1, -1, -1, -2, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![521, 280, -231, -1244, 328]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 4, 6, -6, -4]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![5, 4, 6, -6, -4]] 
 ![![53, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![5, 4, 6, -6, -4], ![-24, -13, 20, 32, -16], ![-48, 6, -45, 116, 80], ![252, 196, -120, -265, 160], ![102, -68, 258, -338, -377]]]
  hmulB := by decide  
  f := ![![![9553, 10080, -12890, -310, -3396]], ![![1418, 1635, -2040, -44, -536]], ![![855, 746, -1011, -30, -268]], ![![5913, 6300, -8034, -191, -2116]], ![![5772, 5904, -7618, -190, -2009]]]
  g := ![![![5, 4, 6, -6, -4], ![-10, -13, 20, 32, -16], ![-117, 6, -45, 116, 80], ![49, 196, -120, -265, 160], ![424, -68, 258, -338, -377]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10413326, 20718416, 15436458, 3937688, 3773387]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![10413326, 20718416, 15436458, 3937688, 3773387]] 
 ![![53, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![49, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![10413326, 20718416, 15436458, 3937688, 3773387], ![22640322, 45045321, 33561456, 8561196, 8203978], ![24611934, 48968052, 36484125, 9306740, 8918414], ![15435081, 30709730, 22880584, 5836611, 5593077], ![1657881, 3298530, 2457602, 626910, 600752]]]
  hmulB := by decide  
  f := ![![![-182, -1162, 1142, -22, 263]], ![![-8, -209, 194, -2, 43]], ![![-100, -438, 439, -2, 111]], ![![-133, -1062, 1050, -53, 244]], ![![-107, -414, 428, -10, 65]]]
  g := ![![![-14488231, 20718416, 15436458, 3937688, 3773387], ![-31499851, 45045321, 33561456, 8561196, 8203978], ![-34242987, 48968052, 36484125, 9306740, 8918414], ![-21475081, 30709730, 22880584, 5836611, 5593077], ![-2306637, 3298530, 2457602, 626910, 600752]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2

def I53N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -5, -4, -2, -1]] i)))

def SI53N3: IdealEqSpanCertificate' Table ![![-2, -5, -4, -2, -1]] 
 ![![53, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![-2, -5, -4, -2, -1], ![-6, -13, -6, -4, -6], ![-18, -19, -9, 14, -2], ![-3, 4, -30, 15, 33], ![45, 19, 8, -72, -16]]]
  hmulB := by decide  
  f := ![![![3146, 149, -1350, -148, -389]], ![![1618, 85, -702, -76, -202]], ![![1910, 81, -811, -90, -234]], ![![915, 47, -396, -43, -114]], ![![1315, 51, -554, -62, -160]]]
  g := ![![![6, -5, -4, -2, -1], ![14, -13, -6, -4, -6], ![12, -19, -9, 14, -2], ![-2, 4, -30, 15, 33], ![13, 19, 8, -72, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N3 : Nat.card (O ⧸ I53N3) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N3)

lemma isPrimeI53N3 : Ideal.IsPrime I53N3 := prime_ideal_of_norm_prime hp53.out _ NI53N3
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-20, 0, 4, 4, 29]] ![![5, 4, 6, -6, -4]]
  ![![3674, -1244, 6702, -10278, -9893]] where
 M := ![![![3674, -1244, 6702, -10278, -9893]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![3674, -1244, 6702, -10278, -9893]] ![![10413326, 20718416, 15436458, 3937688, 3773387]]
  ![![1573, 3334, 2240, 880, 892]] where
 M := ![![![1573, 3334, 2240, 880, 892]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N2 : IdealMulLeCertificate' Table 
  ![![1573, 3334, 2240, 880, 892]] ![![-2, -5, -4, -2, -1]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-25970, -73299, -65720, -36146, -11289]]]
 hmul := by decide  
 g := ![![![![-490, -1383, -1240, -682, -213]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2, I53N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
    exact isPrimeI53N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1 ⊙ MulI53N2)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [47, 45, 3, 18, 42, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 20, 55, 55, 18], [50, 37, 51, 11, 21], [1, 12, 56, 6, 8], [18, 48, 15, 46, 12], [0, 1]]
 g := ![![[35, 23, 16, 40, 35], [17, 51, 4, 34, 1], [57, 39, 49, 22], [35, 17, 1], []], ![[37, 52, 29, 53, 30, 37, 1, 56], [10, 23, 47, 3, 27, 6, 42, 37], [22, 14, 58, 41], [56, 42, 35, 53, 53, 32, 34, 2], [37, 38, 45, 21, 18, 8, 30, 50]], ![[56, 14, 35, 56, 26, 15, 29, 21], [34, 4, 34, 42, 15, 7, 21, 12], [55, 18, 17, 35], [14, 45, 25, 20, 31, 22, 33, 20], [48, 36, 41, 0, 34, 51, 5, 57]], ![[30, 56, 26, 39, 52, 14, 19, 50], [48, 23, 32, 1, 35, 12, 19, 31], [36, 34, 11, 21], [25, 53, 48, 28, 29, 28, 47, 43], [46, 47, 11, 20, 20, 32, 3, 40]], ![[3, 11, 1, 50, 34, 31, 2, 45], [43, 0, 26, 29, 23, 40, 3, 5], [15, 42, 25, 5], [40, 57, 2, 47, 14, 23, 35, 16], [57, 50, 16, 26, 16, 51, 42, 17]]]
 h' := ![![[7, 20, 55, 55, 18], [27, 0, 49, 42, 25], [25, 8, 3, 38, 1], [7, 45, 27, 41, 50], [0, 0, 0, 1], [0, 1]], ![[50, 37, 51, 11, 21], [38, 46, 16, 14, 52], [50, 57, 40, 5, 54], [50, 20, 20, 30, 10], [20, 20, 41, 24, 39], [7, 20, 55, 55, 18]], ![[1, 12, 56, 6, 8], [56, 54, 5, 46, 58], [12, 11, 7, 50, 56], [58, 45, 4, 21, 34], [24, 6, 0, 0, 29], [50, 37, 51, 11, 21]], ![[18, 48, 15, 46, 12], [37, 27, 20, 49, 27], [13, 25, 15, 58, 12], [17, 52, 19, 37, 32], [22, 5, 13, 11, 23], [1, 12, 56, 6, 8]], ![[0, 1], [23, 50, 28, 26, 15], [15, 17, 53, 26, 54], [22, 15, 48, 48, 51], [26, 28, 5, 23, 27], [18, 48, 15, 46, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 33, 37, 43], [], [], []]
 b := ![[], [45, 57, 44, 22, 14], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 5
  hpos := by decide
  P := [47, 45, 3, 18, 42, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13548764677520, 6109494533259, 2173605696798, -21121056966243, -4161960935430]
  a := ![3, 3, 0, -1, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![229640079280, 103550754801, 36840774522, -357984016377, -70541710770]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 714924299 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

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


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [11, 49, 14, 39, 6, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 52, 37, 12, 8], [32, 54, 13, 23, 12], [37, 60, 38, 54, 20], [30, 16, 34, 33, 21], [0, 1]]
 g := ![![[4, 6, 42, 1, 47], [4, 34, 21, 20], [52, 1, 28, 34, 36], [58, 55, 1], []], ![[31, 17, 27, 38, 41, 60, 3, 51], [46, 17, 22, 20], [50, 34, 35, 12, 55, 42, 56, 53], [16, 35, 33, 33, 54, 35, 10, 35], [4, 7, 47, 56, 1, 19, 25, 24]], ![[2, 15, 29, 9, 1, 14, 50, 13], [40, 4, 6, 13], [53, 57, 56, 29, 55, 46, 33, 9], [11, 4, 12, 59, 8, 37, 21, 25], [35, 24, 0, 16, 37, 59, 56, 20]], ![[45, 28, 38, 6, 0, 32, 60, 14], [35, 49, 7, 47], [39, 45, 53, 54, 23, 59, 18, 20], [28, 23, 46, 58, 50, 40, 17, 25], [45, 51, 48, 45, 14, 32, 25, 9]], ![[25, 19, 45, 8, 41, 21, 13, 32], [24, 18, 47, 1], [13, 5, 51, 17, 49, 0, 36, 38], [59, 12, 45, 52, 33, 51, 35, 18], [46, 40, 13, 14, 58, 20, 49, 50]]]
 h' := ![![[17, 52, 37, 12, 8], [58, 11, 40, 32, 13], [38, 55, 41, 18, 9], [33, 30, 20, 30, 55], [0, 0, 0, 1], [0, 1]], ![[32, 54, 13, 23, 12], [2, 30, 55, 23, 40], [52, 22, 30, 26, 52], [51, 8, 34, 29, 50], [50, 37, 36, 47, 16], [17, 52, 37, 12, 8]], ![[37, 60, 38, 54, 20], [43, 39, 20, 36, 22], [19, 4, 41, 3, 14], [36, 19, 43, 15, 57], [53, 2, 30, 29, 34], [32, 54, 13, 23, 12]], ![[30, 16, 34, 33, 21], [1, 21, 46, 43, 18], [52, 60, 19, 10, 48], [14, 22, 37, 4, 60], [16, 20, 20, 15, 48], [37, 60, 38, 54, 20]], ![[0, 1], [50, 21, 22, 49, 29], [58, 42, 52, 4, 60], [5, 43, 49, 44, 22], [20, 2, 36, 30, 24], [30, 16, 34, 33, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 24, 9, 42], [], [], []]
 b := ![[], [22, 41, 28, 21, 10], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [11, 49, 14, 39, 6, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1514846028450, 2007059814449, -2546981465537, -284388113664, 3535014085441]
  a := ![1, 5, -3, 4, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![24833541450, 32902619909, -41753794517, -4662100224, 57951050581]
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



lemma PB1253I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB1253I1 : PrimesBelowBoundCertificateInterval O 23 61 1253 where
  m := 9
  g := ![1, 1, 4, 3, 2, 2, 4, 1, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB1253I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0]
    · exact ![I37N0, I37N1, I37N2, I37N3]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2, I53N3]
    · exact ![I59N0]
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
    · exact ![20511149]
    · exact ![28629151]
    · exact ![1369, 37, 37, 37]
    · exact ![68921, 41, 41]
    · exact ![3418801, 43]
    · exact ![103823, 2209]
    · exact ![2809, 53, 53, 53]
    · exact ![714924299]
    · exact ![844596301]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
      exact NI37N3
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
      exact NI53N3
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
  β := ![I37N1, I37N2, I37N3, I41N1, I41N2, I43N1, I53N1, I53N2, I53N3]
  Il := ![[], [], [I37N1, I37N2, I37N3], [I41N1, I41N2], [I43N1], [], [I53N1, I53N2, I53N3], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
