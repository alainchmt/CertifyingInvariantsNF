
import IdealArithmetic.Examples.NF5_1_145800000_1.RI5_1_145800000_1
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


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [11, 8, 1, 1, 16, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 22, 8, 26, 22], [5, 19, 23, 9, 26], [25, 4, 6, 25, 18], [9, 12, 21, 27, 21], [0, 1]]
 g := ![![[5, 26, 1, 0, 1], [19, 12, 11, 25], [23, 13, 1], []], ![[23, 19, 7, 20, 23, 23, 6, 1], [23, 24], [19, 26, 12, 11, 15, 21, 25, 1], [17, 23, 14, 12, 5, 9, 1, 5]], ![[6, 8, 4, 5, 11, 1, 5, 10], [14, 8, 23, 5], [13, 16, 14, 3, 20, 0, 21, 3], [12, 13, 22, 14, 9, 23, 8, 2]], ![[25, 25, 13, 7, 8, 11, 11, 26], [1, 21, 25, 25], [22, 24, 6, 16, 4, 13, 25, 2], [21, 21, 15, 8, 1, 11, 8, 3]], ![[26, 10, 8, 12, 5, 10, 11, 19], [9, 2, 14, 6], [17, 26, 28, 20, 17, 8, 15, 19], [5, 0, 27, 8, 24, 15, 7, 10]]]
 h' := ![![[3, 22, 8, 26, 22], [0, 23, 27, 8, 1], [8, 21, 7, 14, 24], [0, 0, 0, 1], [0, 1]], ![[5, 19, 23, 9, 26], [12, 2, 4, 5, 2], [2, 11, 10, 16], [14, 2, 12, 24, 2], [3, 22, 8, 26, 22]], ![[25, 4, 6, 25, 18], [13, 23, 23, 10, 4], [15, 20, 12, 23, 18], [22, 26, 25, 18, 17], [5, 19, 23, 9, 26]], ![[9, 12, 21, 27, 21], [25, 25, 28, 22, 13], [6, 22, 28, 1, 24], [24, 25, 3, 3, 19], [25, 4, 6, 25, 18]], ![[0, 1], [8, 14, 5, 13, 9], [22, 13, 1, 4, 21], [7, 5, 18, 12, 20], [9, 12, 21, 27, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 27, 27, 15], [], [], []]
 b := ![[], [28, 16, 28, 10, 27], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [11, 8, 1, 1, 16, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-88197407158, 31305931955, -12116068543, 30330049533, -20742238342]
  a := ![0, -8, -9, -4, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3041289902, 1079514895, -417795467, 1045863777, -715249598]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![331, 169, 109, 60, 84]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![331, 169, 109, 60, 84]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![19, 26, 27, 1, 0], ![21, 3, 6, 0, 1]] where
  M :=![![![331, 169, 109, 60, 84], ![1008, 466, 313, 150, 240], ![2880, 1377, 856, 438, 600], ![696, 448, 246, 181, 172], ![-456, -186, -92, -36, -29]]]
  hmulB := by decide  
  f := ![![![205, -97, 21, -36, 12]], ![![144, 196, -121, 54, -144]], ![![-1728, 267, 106, 138, 216]], ![![-1247, 324, 9, 139, 80]], ![![-153, 3, 20, 6, 31]]]
  g := ![![![-83, -53, -65, 60, 84], ![-222, -134, -167, 150, 240], ![-582, -381, -470, 438, 600], ![-205, -154, -183, 181, 172], ![27, 27, 34, -36, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [19, 2, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 9, 11], [7, 21, 20], [0, 1]]
 g := ![![[23, 18, 5], [3, 27, 9], [12, 17, 16], [1]], ![[17, 29, 6, 27], [28, 29], [19, 24], [30, 23, 4, 29]], ![[1, 14, 0, 20], [28, 1, 3, 25], [22, 20, 26, 10], [11, 1, 5, 2]]]
 h' := ![![[28, 9, 11], [5, 5, 6], [20, 14, 3], [12, 29, 4], [0, 1]], ![[7, 21, 20], [13, 1, 26], [5, 11], [23, 25], [28, 9, 11]], ![[0, 1], [27, 25, 30], [3, 6, 28], [10, 8, 27], [7, 21, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 12], []]
 b := ![[], [3, 18, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [19, 2, 27, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2952666269, 1876791487, -1135393877, 1163905242, -2265710704]
  a := ![3, -126, -124, -65, -310]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![726227707, -696374603, -611824877, 1163905242, -2265710704]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![523, -906, 392, -288, 414]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![523, -906, 392, -288, 414]] 
 ![![31, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![523, -906, 392, -288, 414], ![4968, 169, -780, -132, -1152], ![-13824, 5952, -1115, 2232, -528], ![-3540, -2310, 1666, -521, 2064], ![8406, -2844, 282, -1122, -101]]]
  hmulB := by decide  
  f := ![![![3527108113, 1746479946, 1117124620, 593975916, 835666854]], ![![1233705392, 610880545, 390745796, 207759804, 292298016]], ![![4219257395, 2089204014, 1336345857, 710535996, 999655650]], ![![1298062731, 642747672, 411129398, 218597779, 307546002]], ![![2955999375, 1463690214, 936239994, 497799438, 700355821]]]
  g := ![![![-393, -906, 392, -288, 414], ![1888, 169, -780, -132, -1152], ![-1127, 5952, -1115, 2232, -528], ![-2723, -2310, 1666, -521, 2064], ![1155, -2844, 282, -1122, -101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2013811, -997157, -637825, -339132, -477126]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![-2013811, -997157, -637825, -339132, -477126]] 
 ![![31, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-2013811, -997157, -637825, -339132, -477126], ![-5725512, -2835040, -1813415, -964194, -1356528], ![-16278336, -8060367, -5155762, -2741322, -3856776], ![-4850796, -2401916, -1536370, -816889, -1149284], ![2053110, 1016616, 650272, 345750, 486437]]]
  hmulB := by decide  
  f := ![![![407, 53, -45, -144, -150]], ![![152, 46, -31, -54, -96]], ![![79, 34, -13, -42, -30]], ![![231, -61, 23, -85, 38]], ![![451, 37, -49, -138, -169]]]
  g := ![![![1217394, -997157, -637825, -339132, -477126], ![3461201, -2835040, -1813415, -964194, -1356528], ![9840620, -8060367, -5155762, -2741322, -3856776], ![2932415, -2401916, -1536370, -816889, -1149284], ![-1241151, 1016616, 650272, 345750, 486437]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![331, 169, 109, 60, 84]] ![![523, -906, 392, -288, 414]]
  ![![-407, -53, 45, 144, 150]] where
 M := ![![![-407, -53, 45, 144, 150]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-407, -53, 45, 144, 150]] ![![-2013811, -997157, -637825, -339132, -477126]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29332, -13926, -9291, -4737, -6977]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-29332, -13926, -9291, -4737, -6977]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![26, 13, 9, 30, 1]] where
  M :=![![![-29332, -13926, -9291, -4737, -6977], ![-83724, -41011, -25640, -13884, -18948], ![-227376, -117684, -73843, -40152, -55536], ![-69210, -33236, -22742, -11365, -17294], ![25893, 15444, 9397, 5337, 7256]]]
  hmulB := by decide  
  f := ![![![-3934, 648, -55, 1149, 227]], ![![2724, -3631, 2024, -1692, 4596]], ![![55152, -6684, -727, -15432, -6768]], ![![-14898, 11456, -5826, 6887, -12586]], ![![-1883, 6995, -4198, 2433, -9876]]]
  g := ![![![4110, 2075, 1446, 5529, -6977], ![11052, 5549, 3916, 14988, -18948], ![32880, 16332, 11513, 43944, -55536], ![10282, 5178, 3592, 13715, -17294], ![-4399, -2132, -1511, -5739, 7256]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 4 2 5 [6, 13, 8, 6, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 9, 32, 22], [22, 6, 23, 8], [9, 21, 19, 7], [0, 1]]
 g := ![![[0, 32, 9, 26], [15, 3, 10], [5, 23, 28, 36], [1], []], ![[21, 27, 33, 1, 34, 2], [28, 24, 27], [26, 36, 11, 24, 14, 14], [17, 11, 1], [12, 21, 3]], ![[1, 35, 12, 14, 9, 29], [17, 31, 36], [24, 18, 30, 8, 16, 29], [16, 32, 4], [24, 21, 27]], ![[8, 2, 1, 17, 20, 1], [27, 22, 9], [0, 20, 0, 14, 33, 28], [25, 13, 9], [24, 9, 12]]]
 h' := ![![[0, 9, 32, 22], [33, 2, 1, 27], [7, 18, 19, 26], [31, 24, 29, 31], [0, 0, 1], [0, 1]], ![[22, 6, 23, 8], [7, 4, 29, 8], [29, 5, 7, 8], [13, 28, 19, 2], [2, 14, 27, 1], [0, 9, 32, 22]], ![[9, 21, 19, 7], [6, 13, 6, 6], [21, 10, 36, 6], [27, 13, 8, 6], [7, 11, 14, 2], [22, 6, 23, 8]], ![[0, 1], [20, 18, 1, 33], [21, 4, 12, 34], [8, 9, 18, 35], [11, 12, 32, 34], [9, 21, 19, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [17, 6, 27], []]
 b := ![[], [], [24, 35, 2, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 4
  hpos := by decide
  P := [6, 13, 8, 6, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![304033099, -163586365, 81902036, -117417941, 164162297]
  a := ![1, -9, -9, -5, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-107140179, -62099898, -37717801, -136278023, 164162297]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1874161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3934, -648, 55, -1149, -227]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![3934, -648, 55, -1149, -227]] 
 ![![37, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![3934, -648, 55, -1149, -227], ![-2724, 3631, -2024, 1692, -4596], ![-55152, 6684, 727, 15432, 6768], ![14898, -11456, 5826, -6887, 12586], ![52227, -5646, -1115, -14421, -7430]]]
  hmulB := by decide  
  f := ![![![29332, 13926, 9291, 4737, 6977]], ![![24460, 11647, 7724, 3960, 5792]], ![![29928, 14472, 9529, 4926, 7158]], ![![26446, 12566, 8399, 4276, 6313]], ![![6435, 2970, 2006, 1008, 1501]]]
  g := ![![![1570, -648, 55, -1149, -227], ![-1480, 3631, -2024, 1692, -4596], ![-21714, 6684, 727, 15432, 6768], ![7057, -11456, 5826, -6887, 12586], ![20478, -5646, -1115, -14421, -7430]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-29332, -13926, -9291, -4737, -6977]] ![![3934, -648, 55, -1149, -227]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![70505063, -14172078, 2582372, -21313020, -246906]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![70505063, -14172078, 2582372, -21313020, -246906]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![15, 39, 1, 0, 0], ![5, 16, 0, 1, 0], ![8, 10, 0, 0, 1]] where
  M :=![![![70505063, -14172078, 2582372, -21313020, -246906], ![-2962872, 57679877, -35732004, 16975668, -85252080], ![-1023024960, 162573024, -10596535, 297120456, 67902672], ![137286780, -189073626, 105798694, -86987041, 240706344], ![978615990, -143669028, 2743554, -280885506, -82649689]]]
  hmulB := by decide  
  f := ![![![-1678537608341, -831143298822, -531635444008, -282670925232, -397690741902]], ![![-4772288902824, -2363042639891, -1511504965956, -803668212636, -1130683700928]], ![![-5484525262107, -2715713008503, -1737088289899, -923611018572, -1299431666226]], ![![-2165671017965, -1072351876360, -685922953274, -364705698169, -513105759366]], ![![-1449753565742, -717858780802, -459173733730, -244142984790, -343485643981]]]
  g := ![![![3422191, 5575434, 2582372, -21313020, -246906], ![27564768, 49564345, -35732004, 16975668, -85252080], ![-70558551, -118466247, -10596535, 297120456, 67902672], ![-71717297, -130012036, 105798694, -86987041, 240706344], ![73246042, 123658472, 2743554, -280885506, -82649689]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [14, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 40], [0, 1]]
 g := ![![[32, 16], [23], [33], [25, 9], [1]], ![[39, 25], [23], [33], [11, 32], [1]]]
 h' := ![![[3, 40], [39, 4], [22, 33], [19, 22], [27, 3], [0, 1]], ![[0, 1], [10, 37], [39, 8], [3, 19], [36, 38], [3, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [20, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [14, 38, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![107318, -86899, 76998, -50973, 151960]
  a := ![1, 44, 48, 18, 121]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-48987, -92533, 76998, -50973, 151960]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11338, 6593, -3106, 4639, -6401]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-11338, 6593, -3106, 4639, -6401]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![8, 29, 1, 0, 0], ![16, 12, 0, 1, 0], ![15, 33, 0, 0, 1]] where
  M :=![![![-11338, 6593, -3106, 4639, -6401], ![-76812, 3186, 4831, 19770, 18556], ![222672, -98217, 41512, -82350, 79080], ![196566, 3010, -19330, -47453, -64178], ![-228999, 94672, -38741, 82917, -71862]]]
  hmulB := by decide  
  f := ![![![4491971584, 2224240947, 1422721360, 756461909, 1064268983]], ![![12771227796, 6323790624, 4044971839, 2150714262, 3025847636]], ![![10795403668, 5345443179, 3419178213, 1817979368, 2557721716]], ![![5754789734, 2849536940, 1822687904, 969124391, 1363464594]], ![![11810986833, 5848318501, 3740839166, 1989006714, 2798340705]]]
  g := ![![![861, 6152, -3106, 4639, -6401], ![-17320, -24061, 4831, 19770, 18556], ![536, -71305, 41512, -82350, 79080], ![50564, 79290, -19330, -47453, -64178], ![-4093, 63283, -38741, 82917, -71862]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [16, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 40], [0, 1]]
 g := ![![[37, 18], [1], [5], [33, 37], [1]], ![[0, 23], [1], [5], [23, 4], [1]]]
 h' := ![![[23, 40], [16, 10], [27, 40], [5, 13], [25, 23], [0, 1]], ![[0, 1], [0, 31], [4, 1], [17, 28], [21, 18], [23, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [28, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [16, 18, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![33179, -14463, 6850, -12743, 11066]
  a := ![-1, -7, -14, 5, -38]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![397, -10375, 6850, -12743, 11066]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-356, 182, -43, 65, -29]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-356, 182, -43, 65, -29]] 
 ![![41, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-356, 182, -43, 65, -29], ![-348, -333, 218, -84, 260], ![3120, -558, -157, -252, -336], ![-498, 734, -300, 221, -298], ![-1587, 152, 149, 81, 240]]]
  hmulB := by decide  
  f := ![![![18819386, 9318592, 5960577, 3169243, 4458819]], ![![7731152, 3828151, 2448652, 1301950, 1831718]], ![![7841418, 3882750, 2483576, 1320519, 1857843]], ![![7072768, 3502146, 2240125, 1191076, 1675729]], ![![-467967, -231718, -148217, -78807, -110874]]]
  g := ![![![-82, 182, -43, 65, -29], ![84, -333, 218, -84, 260], ![381, -558, -157, -252, -336], ![-267, 734, -300, 221, -298], ![-149, 152, 149, 81, 240]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![70505063, -14172078, 2582372, -21313020, -246906]] ![![-11338, 6593, -3106, 4639, -6401]]
  ![![-3268652673200, 78527534095, 241291453914, 825126704255, 875504146661]] where
 M := ![![![-3268652673200, 78527534095, 241291453914, 825126704255, 875504146661]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![-3268652673200, 78527534095, 241291453914, 825126704255, 875504146661]] ![![-356, 182, -43, 65, -29]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![88803926535823, -16965455444405, 2700415691801, -26595345488412, -1632604796954]]]
 hmul := by decide  
 g := ![![![![2165949427703, -413791596205, 65863797361, -648666963132, -39819629194]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1108, -810, 267, -303, 229]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![1108, -810, 267, -303, 229]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![20, 25, 1, 0, 0], ![17, 0, 0, 1, 0], ![38, 9, 0, 0, 1]] where
  M :=![![![1108, -810, 267, -303, 229], ![2748, 919, -884, 228, -1212], ![-14544, 3960, -65, 1968, 912], ![450, -3044, 1582, -1091, 1918], ![8703, -1632, -317, -1053, -1016]]]
  hmulB := by decide  
  f := ![![![1206217114, 597269472, 382039561, 203130693, 285785303]], ![![3429423636, 1698110581, 1086185468, 577525548, 812522772]], ![![2781632708, 1377350959, 881013647, 468435552, 659043664]], ![![544446128, 269587496, 172439901, 91686412, 128993943]], ![![1755146675, 869076981, 555899479, 295572129, 415841492]]]
  g := ![![![-181, -222, 267, -303, 229], ![1456, 789, -884, 228, -1212], ![-1892, -61, -65, 1968, 912], ![-1989, -1392, 1582, -1091, 1918], ![1664, 359, -317, -1053, -1016]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [20, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 42], [0, 1]]
 g := ![![[20, 15], [0, 16], [40], [0, 40], [1]], ![[40, 28], [7, 27], [40], [39, 3], [1]]]
 h' := ![![[30, 42], [0, 12], [17, 39], [0, 30], [23, 30], [0, 1]], ![[0, 1], [16, 31], [26, 4], [40, 13], [20, 13], [30, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [10, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [20, 13, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26756, -4696, 180, -7494, -3124]
  a := ![0, -4, 8, -18, 20]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6262, 440, 180, -7494, -3124]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![273224, 61529, -62662, -49793, -174887]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![273224, 61529, -62662, -49793, -174887]] 
 ![![43, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![27, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![273224, 61529, -62662, -49793, -174887], ![-2098644, 560106, -163151, 673350, -199172], ![-2390064, -1317231, 1034284, 216126, 2693400], ![6436122, -1471934, 346958, -1995791, 243670], ![1853187, 1376830, -1023797, -67437, -2619348]]]
  hmulB := by decide  
  f := ![![![48335355922454, 23933694998241, 15309033459080, 8139823444423, 11451946898995]], ![![7692204336692, 3808865559072, 2436316259953, 1295391003214, 1822490264504]], ![![39436421749734, 19527306088206, 12490515246058, 6641215404261, 9343549853835]], ![![28561433946664, 14142456091325, 9046130717032, 4809833820576, 6766972512649]], ![![24707780983429, 12234284466415, 7825581058755, 4160866741754, 5853938393837]]]
  g := ![![![160154, 61529, -62662, -49793, -174887], ![-252095, 560106, -163151, 673350, -199172], ![-2138742, -1317231, 1034284, 216126, 2693400], ![1005925, -1471934, 346958, -1995791, 243670], ![1994987, 1376830, -1023797, -67437, -2619348]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20, 6, -1, 5, 1]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-20, 6, -1, 5, 1]] 
 ![![43, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-20, 6, -1, 5, 1], ![12, -21, 12, -12, 20], ![240, -24, -13, -48, -48], ![-102, 60, -26, 41, -42], ![-189, 8, 15, 39, 48]]]
  hmulB := by decide  
  f := ![![![-27542, -13640, -8723, -4639, -6525]], ![![-5664, -2805, -1794, -954, -1342]], ![![-9662, -4784, -3060, -1627, -2289]], ![![-22680, -11232, -7183, -3820, -5373]], ![![13, 6, 4, 2, 3]]]
  g := ![![![-5, 6, -1, 5, 1], ![10, -21, 12, -12, 20], ![49, -24, -13, -48, -48], ![-37, 60, -26, 41, -42], ![-39, 8, 15, 39, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2

def I43N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-56, 130, -59, 41, -63]] i)))

def SI43N3: IdealEqSpanCertificate' Table ![![-56, 130, -59, 41, -63]] 
 ![![43, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-56, 130, -59, 41, -63], ![-756, -3, 108, 24, 164], ![1968, -900, 185, -336, 96], ![570, 318, -244, 77, -306], ![-1221, 434, -51, 171, 12]]]
  hmulB := by decide  
  f := ![![![358, -156, 47, -139, 91]], ![![92, -27, 4, -32, 4]], ![![28, -36, 7, -22, 22]], ![![138, -102, 40, -67, 90]], ![![225, -76, 24, -78, 39]]]
  g := ![![![-5, 130, -59, 41, -63], ![-120, -3, 108, 24, 164], ![286, -900, 185, -336, 96], ![100, 318, -244, 77, -306], ![-181, 434, -51, 171, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N3 : Nat.card (O ⧸ I43N3) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N3)

lemma isPrimeI43N3 : Ideal.IsPrime I43N3 := prime_ideal_of_norm_prime hp43.out _ NI43N3
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![1108, -810, 267, -303, 229]] ![![273224, 61529, -62662, -49793, -174887]]
  ![![-161278399, 24077667, -701145, 46403098, 13029622]] where
 M := ![![![-161278399, 24077667, -701145, 46403098, 13029622]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-161278399, 24077667, -701145, 46403098, 13029622]] ![![-20, 6, -1, 5, 1]]
  ![![-3849489370, 1431948935, -551710930, 1349013237, -969578359]] where
 M := ![![![-3849489370, 1431948935, -551710930, 1349013237, -969578359]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N2 : IdealMulLeCertificate' Table 
  ![![-3849489370, 1431948935, -551710930, 1349013237, -969578359]] ![![-56, 130, -59, 41, -63]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![43621049, -426345, -6897759, -11297390, -39784460]]]
 hmul := by decide  
 g := ![![![![1014443, -9915, -160413, -262730, -925220]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2, I43N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
    exact isPrimeI43N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1 ⊙ MulI43N2)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-317, -157, -109, -54, -84]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-317, -157, -109, -54, -84]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![39, 5, 20, 1, 0], ![5, 16, 36, 0, 1]] where
  M :=![![![-317, -157, -109, -54, -84], ![-1008, -446, -295, -150, -216], ![-2592, -1395, -812, -474, -600], ![-696, -394, -264, -137, -208], ![276, 210, 92, 72, 67]]]
  hmulB := by decide  
  f := ![![![53, -19, 7, -18, 12]], ![![144, 20, -25, -30, -72]], ![![-864, 255, -82, 282, -120]], ![![-315, 93, -30, 103, -44]], ![![-589, 195, -69, 198, -113]]]
  g := ![![![47, 31, 85, -54, -84], ![126, 80, 223, -150, -216], ![402, 225, 644, -474, -600], ![121, 77, 212, -137, -208], ![-61, -26, -80, 72, 67]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [40, 15, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 17, 34], [0, 29, 13], [0, 1]]
 g := ![![[18, 5, 17], [19, 21, 17], [33, 44, 16], [22, 32, 1], []], ![[30, 8, 42, 28], [37, 8, 5, 27], [25, 28, 13, 21], [45, 2, 28, 18], [31, 28]], ![[0, 39, 33, 44], [26, 35, 28, 20], [26, 46, 39, 22], [2, 14, 9, 44], [5, 28]]]
 h' := ![![[32, 17, 34], [39, 19, 39], [43, 29, 8], [13, 35, 43], [0, 0, 1], [0, 1]], ![[0, 29, 13], [25, 22, 38], [42, 42, 43], [23, 45, 40], [19, 20, 29], [32, 17, 34]], ![[0, 1], [41, 6, 17], [41, 23, 43], [14, 14, 11], [35, 27, 17], [0, 29, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 31], []]
 b := ![[], [40, 35, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [40, 15, 15, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10823953, 2774942, -776871, 3316988, -878347]
  a := ![13, -8, -13, 2, -35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2889250, 5182, -755237, 3316988, -878347]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-53, 19, -7, 18, -12]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-53, 19, -7, 18, -12]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![6, 21, 1, 0, 0], ![26, 22, 0, 1, 0], ![36, 27, 0, 0, 1]] where
  M :=![![![-53, 19, -7, 18, -12], ![-144, -20, 25, 30, 72], ![864, -255, 82, -282, 120], ![312, 88, -82, -53, -224], ![-852, 240, -74, 276, -101]]]
  hmulB := by decide  
  f := ![![![317, 157, 109, 54, 84]], ![![1008, 446, 295, 150, 216]], ![![546, 249, 163, 84, 120]], ![![662, 304, 204, 103, 152]], ![![816, 372, 251, 126, 187]]]
  g := ![![![-1, 2, -7, 18, -12], ![-78, -67, 25, 30, 72], ![72, 21, 82, -282, 120], ![218, 192, -82, -53, -224], ![-84, -33, -74, 276, -101]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [41, 3, 1] where
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
 g := ![![[23, 32], [17, 34], [32, 9], [31, 9], [1]], ![[21, 15], [9, 13], [5, 38], [4, 38], [1]]]
 h' := ![![[44, 46], [8, 28], [4, 9], [45, 44], [6, 44], [0, 1]], ![[0, 1], [18, 19], [24, 38], [7, 3], [15, 3], [44, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [17, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [41, 3, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-648, 153, 112, 259, 275]
  a := ![-1, -4, -2, -4, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-382, -326, 112, 259, 275]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-317, -157, -109, -54, -84]] ![![-53, 19, -7, 18, -12]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![-47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1069, -234, -32, -100, -94]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![1069, -234, -32, -100, -94]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![3, 50, 9, 1, 0], ![39, 35, 37, 0, 1]] where
  M :=![![![1069, -234, -32, -100, -94], ![-1128, 1155, -428, 372, -400], ![-4800, -840, 1127, -168, 1488], ![3540, -1586, 294, -547, 88], ![1746, 824, -686, 258, -819]]]
  hmulB := by decide  
  f := ![![![416525, 206246, 131924, 70144, 98686]], ![![1184232, 586383, 375076, 199428, 280576]], ![![3366912, 1667160, 1066387, 567000, 797712]], ![![1731447, 857342, 548393, 291581, 410226]], ![![3431013, 1698899, 1086689, 577794, 812899]]]
  g := ![![![95, 152, 82, -100, -94], ![252, -65, 208, 372, -400], ![-1176, -840, -989, -168, 1488], ![33, 428, 37, -547, 88], ![621, 313, 515, 258, -819]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [13, 16, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 0, 39], [31, 52, 14], [0, 1]]
 g := ![![[13, 48, 47], [4, 7], [7, 39, 7], [3, 17], [1]], ![[27, 15, 2, 26], [13, 9], [12, 14, 48, 8], [31, 28], [49, 15, 40, 12]], ![[30, 41, 33, 33], [48, 43], [6, 3, 14, 21], [26, 38], [4, 27, 8, 41]]]
 h' := ![![[43, 0, 39], [14, 39, 43], [15, 10, 22], [24, 41, 31], [40, 37, 21], [0, 1]], ![[31, 52, 14], [47, 22, 47], [2, 47, 50], [4, 6, 31], [6, 28, 44], [43, 0, 39]], ![[0, 1], [49, 45, 16], [14, 49, 34], [16, 6, 44], [6, 41, 41], [31, 52, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 47], []]
 b := ![[], [9, 29, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [13, 16, 32, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![597736, -129055, 57145, -169699, 61258]
  a := ![3, 3, 7, -1, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-24193, 117205, -12870, -169699, 61258]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-416525, -206246, -131924, -70144, -98686]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-416525, -206246, -131924, -70144, -98686]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![37, 52, 1, 0, 0], ![15, 33, 0, 1, 0], ![30, 39, 0, 0, 1]] where
  M :=![![![-416525, -206246, -131924, -70144, -98686], ![-1184232, -586383, -375076, -199428, -280576], ![-3366912, -1667160, -1066387, -567000, -797712], ![-1003308, -496798, -317774, -168961, -237712], ![424650, 210272, 134498, 71514, 100611]]]
  hmulB := by decide  
  f := ![![![-1069, 234, 32, 100, 94]], ![![1128, -1155, 428, -372, 400]], ![![451, -954, 421, -292, 430]], ![![333, -623, 270, -193, 274]], ![![192, -733, 346, -222, 363]]]
  g := ![![![159951, 241836, -131924, -70144, -98686], ![454760, 687569, -375076, -199428, -280576], ![1292939, 1954844, -1066387, -567000, -797712], ![385285, 582527, -317774, -168961, -237712], ![-163072, -246555, 134498, 71514, 100611]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [40, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 52], [0, 1]]
 g := ![![[38, 4], [47], [42, 24], [44], [17, 1]], ![[0, 49], [47], [26, 29], [44], [34, 52]]]
 h' := ![![[17, 52], [19, 2], [16, 43], [17, 36], [9, 37], [0, 1]], ![[0, 1], [0, 51], [5, 10], [46, 17], [2, 16], [17, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [33, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [40, 36, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14438, -6575, 4042, -5825, 7378]
  a := ![1, 6, 10, -2, 27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5077, -5892, 4042, -5825, 7378]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![1069, -234, -32, -100, -94]] ![![-416525, -206246, -131924, -70144, -98686]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![403567, 199830, 127820, 67962, 95616]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![403567, 199830, 127820, 67962, 95616]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![37, 56, 1, 0, 0], ![48, 15, 0, 1, 0], ![29, 39, 0, 0, 1]] where
  M :=![![![403567, 199830, 127820, 67962, 95616], ![1147392, 568141, 363408, 193224, 271848], ![3262176, 1615296, 1033213, 549360, 772896], ![972096, 481344, 307888, 163705, 230316], ![-411444, -203730, -130314, -69288, -97481]]]
  hmulB := by decide  
  f := ![![![-619, 42, 68, 30, 120]], ![![1440, -745, 192, -312, 120]], ![![1003, -658, 209, -270, 168]], ![![-192, -141, 104, -47, 132]], ![![647, -489, 170, -198, 151]]]
  g := ![![![-175607, -198416, 127820, 67962, 95616], ![-499272, -564121, 363408, 193224, 271848], ![-1419491, -1603864, 1033213, 549360, 772896], ![-422996, -477937, 307888, 163705, 230316], ![179033, 202287, -130314, -69288, -97481]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [18, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 58], [0, 1]]
 g := ![![[4, 20], [2, 36], [48], [48, 27], [46, 1]], ![[39, 39], [6, 23], [48], [51, 32], [33, 58]]]
 h' := ![![[46, 58], [23, 16], [49, 6], [21, 15], [57, 33], [0, 1]], ![[0, 1], [51, 43], [30, 53], [3, 44], [41, 26], [46, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [54, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [18, 13, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![242, -33, -15, -22, -48]
  a := ![4, 0, -1, 1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![55, 51, -15, -22, -48]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![146, -93, 46, -65, 95]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![146, -93, 46, -65, 95]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![54, 26, 1, 0, 0], ![2, 5, 0, 1, 0], ![37, 6, 0, 0, 1]] where
  M :=![![![146, -93, 46, -65, 95], ![1140, -66, -63, -294, -260], ![-3120, 1437, -620, 1182, -1176], ![-2922, -12, 272, 703, 918], ![3249, -1382, 573, -1191, 1062]]]
  hmulB := by decide  
  f := ![![![447916, 221791, 141868, 75431, 106125]], ![![1273500, 630576, 403347, 214458, 301724]], ![![1032528, 511263, 327028, 173880, 244634]], ![![141394, 70012, 44783, 23811, 33500]], ![![402665, 199383, 127535, 67810, 95403]]]
  g := ![![![-97, -26, 46, -65, 95], ![250, 78, -63, -294, -260], ![1212, 317, -620, 1182, -1176], ![-898, -273, 272, 703, 918], ![-1095, -283, 573, -1191, 1062]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [14, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 58], [0, 1]]
 g := ![![[18, 51], [48, 53], [22], [47, 36], [43, 1]], ![[28, 8], [26, 6], [22], [2, 23], [27, 58]]]
 h' := ![![[43, 58], [36, 46], [9, 17], [50, 9], [47, 6], [0, 1]], ![[0, 1], [8, 13], [32, 42], [24, 50], [10, 53], [43, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [7, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [14, 16, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15761, 6631, 3250, 8051, 5722]
  a := ![7, -19, -18, -23, -32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7103, -2584, 3250, 8051, 5722]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![40, 1, -6, -1, -9]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![40, 1, -6, -1, -9]] 
 ![![59, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  M :=![![![40, 1, -6, -1, -9], ![-108, 48, -9, 18, -4], ![-48, -105, 62, -30, 72], ![198, -42, -6, -19, -18], ![-15, 68, -33, 21, -36]]]
  hmulB := by decide  
  f := ![![![2, -27, 24, -5, 53]], ![![12, -18, 15, -6, 32]], ![![-4, 9, -4, 4, -10]], ![![-28, -9, 12, 6, 29]], ![![9, -34, 27, -9, 60]]]
  g := ![![![9, 1, -6, -1, -9], ![-36, 48, -9, 18, -4], ![10, -105, 62, -30, 72], ![55, -42, -6, -19, -18], ![-18, 68, -33, 21, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![403567, 199830, 127820, 67962, 95616]] ![![146, -93, 46, -65, 95]]
  ![![2, -27, 24, -5, 53]] where
 M := ![![![2, -27, 24, -5, 53]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![2, -27, 24, -5, 53]] ![![40, 1, -6, -1, -9]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [36, 21, 55, 25, 8, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 59, 38, 38, 27], [50, 42, 54, 53, 4], [42, 45, 33, 31, 35], [52, 36, 58, 0, 56], [0, 1]]
 g := ![![[11, 33, 16, 20, 57], [60, 14, 60, 36], [50, 58, 52, 46, 12], [39, 53, 1], []], ![[4, 7, 52, 1, 49, 22, 42, 14], [54, 25, 18, 42], [34, 23, 55, 37, 32, 34, 34, 56], [37, 41, 49, 51, 14, 1, 44, 19], [35, 31, 25, 3, 8, 55, 1, 41]], ![[30, 1, 29, 48, 15, 39, 19, 57], [40, 4, 6, 13], [40, 52, 49, 24, 30, 30, 29, 15], [20, 31, 33, 49, 33, 29, 51, 36], [7, 13, 17, 5, 19, 22, 19, 3]], ![[0, 55, 6, 37, 33, 31, 49, 40], [12, 26, 26, 16], [13, 41, 59, 45, 33, 17, 26, 26], [33, 50, 34, 57, 57, 40, 48, 7], [6, 36, 6, 10, 5, 12, 41, 53]], ![[39, 9, 26, 37, 41, 27, 11, 19], [24, 8, 9, 57], [39, 0, 31, 14, 1, 20, 50, 45], [27, 54, 39, 43, 58, 58, 39, 13], [51, 55, 7, 25, 60, 24, 24, 58]]]
 h' := ![![[31, 59, 38, 38, 27], [21, 31, 5, 28, 39], [30, 35, 41, 29, 6], [60, 18, 0, 54, 16], [0, 0, 0, 1], [0, 1]], ![[50, 42, 54, 53, 4], [12, 25, 20, 40, 22], [59, 19, 56, 24, 15], [2, 22, 42, 23, 44], [44, 8, 5, 26, 45], [31, 59, 38, 38, 27]], ![[42, 45, 33, 31, 35], [9, 33, 58, 55, 50], [30, 20, 38, 17, 14], [35, 46, 52, 22, 18], [3, 52, 14, 40, 3], [50, 42, 54, 53, 4]], ![[52, 36, 58, 0, 56], [51, 23, 15, 24, 55], [42, 50, 1, 4, 4], [13, 12, 21, 15, 11], [1, 38, 20, 6, 54], [42, 45, 33, 31, 35]], ![[0, 1], [37, 10, 24, 36, 17], [13, 59, 47, 48, 22], [45, 24, 7, 8, 33], [58, 24, 22, 49, 20], [52, 36, 58, 0, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 28, 26, 51], [], [], []]
 b := ![[], [37, 31, 44, 27, 32], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [36, 21, 55, 25, 8, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-100986415, -7357027, 3748816, 18966059, 24087497]
  a := ![1, -3, -3, -5, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1655515, -120607, 61456, 310919, 394877]
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



lemma PB752I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB752I1 : PrimesBelowBoundCertificateInterval O 23 61 752 where
  m := 9
  g := ![1, 3, 2, 3, 4, 2, 2, 3, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB752I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1, I43N2, I43N3]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
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
    · exact ![20511149]
    · exact ![29791, 31, 31]
    · exact ![1874161, 37]
    · exact ![1681, 1681, 41]
    · exact ![1849, 43, 43, 43]
    · exact ![103823, 2209]
    · exact ![148877, 2809]
    · exact ![3481, 3481, 59]
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
      exact NI31N1
      exact NI31N2
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
      exact NI43N3
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
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
  β := ![I31N1, I31N2, I37N1, I41N2, I43N1, I43N2, I43N3, I59N2]
  Il := ![[], [I31N1, I31N2], [I37N1], [I41N2], [I43N1, I43N2, I43N3], [], [], [I59N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
