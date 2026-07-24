
import IdealArithmetic.Examples.NF5_3_12000000000_4.RI5_3_12000000000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1992621, 794050, -3237891, -952347, 13264246]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![1992621, 794050, -3237891, -952347, 13264246]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![9, 26, 1, 0, 0], ![12, 28, 0, 1, 0], ![27, 23, 0, 0, 1]] where
  M :=![![![1992621, 794050, -3237891, -952347, 13264246], ![-5576858, -2228439, 9068124, 2666838, -37149754], ![15629072, 6206362, -25374665, -7464522, 103943536], ![-9346172, -3793762, 15256020, 4483423, -62515036], ![5952432, 2363016, -9663390, -2842740, 39584455]]]
  hmulB := by decide  
  f := ![![![-2871, 2426, 2685, -465, -4546]], ![![19322, -71067, 46290, 14100, -172454]], ![![17629, -55190, 32416, 10965, -125506]], ![![8756, -48526, 38856, 9631, -135296]], ![![12293, -50703, 36183, 10077, -130801]]]
  g := ![![![-10881822, -6670094, -3237891, -952347, 13264246], ![30477632, 18681835, 9068124, 2666838, -37149754], ![-85272419, -52267140, -25374665, -7464522, 103943536], ![51291536, 31443438, 15256020, 4483423, -62515036], ![-32473947, -19904641, -9663390, -2842740, 39584455]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [15, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 28], [0, 1]]
 g := ![![[11, 16], [20], [11, 6], [9, 1]], ![[10, 13], [20], [7, 23], [18, 28]]]
 h' := ![![[9, 28], [13, 25], [9, 22], [10, 8], [0, 1]], ![[0, 1], [6, 4], [4, 7], [24, 21], [9, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [17, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [15, 20, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-295628, 515782, -124284, -50939, 830661]
  a := ![99, -397, 273, 62, -1053]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-723919, -480405, -124284, -50939, 830661]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![215, 79, -344, -99, 1398]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![215, 79, -344, -99, 1398]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![14, 13, 1, 0, 0], ![2, 1, 0, 1, 0], ![16, 21, 0, 0, 1]] where
  M :=![![![215, 79, -344, -99, 1398], ![-618, -109, 870, 255, -3594], ![1578, 258, -2158, -705, 9354], ![-540, -1360, 1949, 662, -8220], ![642, 76, -860, -264, 3635]]]
  hmulB := by decide  
  f := ![![![3865, -8153, 3802, 594, -17988]], ![![22908, -51791, 23763, 3684, -112836]], ![![17122, -38529, 17697, 2745, -84012]], ![![13300, -30305, 13880, 2150, -65934]], ![![20750, -46637, 21427, 3324, -101713]]]
  g := ![![![-591, -852, -344, -99, 1398], ![1524, 2200, 870, 255, -3594], ![-4016, -5773, -2158, -705, 9354], ![3530, 5009, 1949, 662, -8220], ![-1550, -2235, -860, -264, 3635]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [28, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 28], [0, 1]]
 g := ![![[6, 28], [20], [16, 6], [6, 1]], ![[0, 1], [20], [23, 23], [12, 28]]]
 h' := ![![[6, 28], [15, 12], [16, 22], [6, 8], [0, 1]], ![[0, 1], [0, 17], [3, 7], [25, 21], [6, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [19, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [28, 23, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-206220, 448587, -177642, -52668, 897462]
  a := ![-97, 327, -267, -60, 1032]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-412872, -552969, -177642, -52668, 897462]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4317, 272, -6749, -44, 16464]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![4317, 272, -6749, -44, 16464]] 
 ![![29, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![4317, 272, -6749, -44, 16464], ![-31960, 99229, -56151, -19675, 220200], ![-7550, -442160, 474755, 87322, -1521150], ![371222, -630758, 105266, 125467, -794634], ![26076, -159202, 127822, 31508, -444023]]]
  hmulB := by decide  
  f := ![![![-2848557, 6582216, -3005219, -464794, 14285826]], ![![-2498923, 5759539, -2631124, -407049, 12505878]], ![![-5608382, 12853600, -5879351, -910126, 27936882]], ![![-11886430, 27203130, -12446962, -1927095, 59139870]], ![![-3216696, 7389054, -3378080, -522798, 16053469]]]
  g := ![![![-5359, 272, -6749, -44, 16464], ![-143055, 99229, -56151, -19675, 220200], ![806530, -442160, 474755, 87322, -1521150], ![719868, -630758, 105266, 125467, -794634], ![257930, -159202, 127822, 31508, -444023]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![1992621, 794050, -3237891, -952347, 13264246]] ![![215, 79, -344, -99, 1398]]
  ![![3858211929, 1538764347, -6270645209, -1844288232, 25688462594]] where
 M := ![![![3858211929, 1538764347, -6270645209, -1844288232, 25688462594]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![3858211929, 1538764347, -6270645209, -1844288232, 25688462594]] ![![4317, 272, -6749, -44, 16464]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![32348236963, 12901394459, -52574695457, -15462984991, 215378650232]]]
 hmul := by decide  
 g := ![![![![1115456447, 444875671, -1812920533, -533206379, 7426850008]]]]
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


def P31P0 : CertificateIrreducibleZModOfList' 31 5 2 4 [18, 13, 29, 12, 29, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 4, 24, 2, 24], [19, 0, 4, 15, 28], [11, 21, 26, 11, 25], [8, 5, 8, 3, 16], [0, 1]]
 g := ![![[2, 4, 2, 16, 25], [5, 9, 1, 27, 18], [23, 2, 1], []], ![[9, 5, 26, 13, 0, 26, 27, 23], [10, 17, 21, 7, 5, 0, 13, 12], [25, 4, 18, 3, 6, 10, 3, 30], [4, 19, 23, 2, 30, 18, 11, 29]], ![[13, 5, 4, 18, 20, 2, 25, 9], [26, 10, 4, 24, 17, 30, 10, 9], [8, 0, 21, 19, 4, 29, 4, 18], [7, 14, 0, 23, 29, 8, 10, 4]], ![[30, 21, 24, 18, 14, 26, 6, 4], [20, 19, 29, 29, 18, 24, 12, 16], [30, 6, 9, 12, 6, 13, 19, 2], [27, 30, 30, 14, 25, 22, 12, 1]], ![[14, 9, 0, 3, 10, 8, 1, 19], [5, 15, 0, 4, 1, 11, 17, 4], [21, 11, 25, 12, 27, 17, 25, 4], [6, 25, 19, 30, 26, 23, 18, 4]]]
 h' := ![![[26, 4, 24, 2, 24], [3, 18, 22, 9, 5], [20, 6, 2, 25, 24], [0, 0, 0, 1], [0, 1]], ![[19, 0, 4, 15, 28], [1, 20, 30, 24, 17], [30, 8, 7, 29, 4], [20, 30, 8, 27, 28], [26, 4, 24, 2, 24]], ![[11, 21, 26, 11, 25], [15, 13, 15, 18, 11], [13, 29, 30, 14, 11], [6, 29, 10, 27, 5], [19, 0, 4, 15, 28]], ![[8, 5, 8, 3, 16], [4, 18, 24, 23, 19], [9, 21, 15, 24, 7], [8, 5, 20, 24, 14], [11, 21, 26, 11, 25]], ![[0, 1], [4, 24, 2, 19, 10], [2, 29, 8, 1, 16], [1, 29, 24, 14, 15], [8, 5, 8, 3, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 24, 30], [], [], []]
 b := ![[], [2, 11, 10, 22], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 5
  hpos := by decide
  P := [18, 13, 29, 12, 29, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7368500639558, -21075123226258, 12027002731364, 2278995085190, -50222580513408]
  a := ![30, -122, 83, 19, -319]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![237693569018, -679842684718, 387967830044, 73515970490, -1620083242368]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8428069, 2468651, -2867956, -574158, 11764422]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-8428069, 2468651, -2867956, -574158, 11764422]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![19, 28, 5, 1, 0], ![32, 32, 33, 0, 1]] where
  M :=![![![-8428069, 2468651, -2867956, -574158, 11764422], ![-10897368, 11632559, -6697443, -1139814, 30348936], ![-35621964, 70892616, -33537088, -5274747, 158168628], ![-78638262, 173368228, -80007443, -12438100, 379412874], ![-12422538, 28684478, -13098850, -2026110, 62265083]]]
  hmulB := by decide  
  f := ![![![1176977, -8866625, 7531132, 1754229, -25720992]], ![![12848946, 1223177, -20521758, -211581, 50395698]], ![![-96136614, 296604006, -166931416, -58814721, 656029818]], ![![-3692995, 27093335, -22867943, -5360542, 78246774]], ![![-74346680, 259246930, -160403490, -51384411, 608262005]]]
  g := ![![![-10107583, -9673417, -10492516, -574158, 11764422], ![-25956942, -25070773, -27094953, -1139814, 30348936], ![-135048591, -130886772, -141262921, -5274747, 158168628], ![-323879090, -314042620, -338876805, -12438100, 379412874], ![-53146192, -51542354, -55613947, -2026110, 62265083]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [22, 29, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 6, 1], [33, 30, 36], [0, 1]]
 g := ![![[25, 10, 34], [], [18, 14, 7], [1, 1], []], ![[20, 5, 24, 10], [14, 21], [1, 2, 3, 9], [22, 12], [13, 1]], ![[20, 34, 17, 12], [19, 21], [27, 36, 19, 1], [34, 36], [15, 1]]]
 h' := ![![[5, 6, 1], [10, 10, 21], [11, 24], [15, 23, 9], [0, 0, 1], [0, 1]], ![[33, 30, 36], [18, 8, 11], [20, 33, 24], [1, 10, 34], [35, 31, 30], [5, 6, 1]], ![[0, 1], [36, 19, 5], [26, 17, 13], [20, 4, 31], [19, 6, 6], [33, 30, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 23], []]
 b := ![[], [14, 15, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [22, 29, 36, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-490084454, 385546912, 223642372, 130558038, 144256818]
  a := ![-113, 472, -311, -72, 1202]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-205051496, -213143144, -140260076, 130558038, 144256818]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-293, 990, -602, -192, 2272]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-293, 990, -602, -192, 2272]] 
 ![![37, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![-293, 990, -602, -192, 2272], ![-320, -3557, 4216, 690, -13120], ![11060, -18320, 2617, 3678, -22220], ![-8472, 61028, -51266, -12095, 175784], ![2140, -32, -3180, 24, 7543]]]
  hmulB := by decide  
  f := ![![![2594743, -244534, 700326, 152472, -2697128]], ![![546029, -50871, 147166, 32058, -566520]], ![![1795047, -164958, 482995, 105282, -1858324]], ![![1704408, -150156, 456314, 99661, -1752880]], ![![1049833, -97194, 282734, 61608, -1088129]]]
  g := ![![![-585, 990, -602, -192, 2272], ![2687, -3557, 4216, 690, -13120], ![8619, -18320, 2617, 3678, -22220], ![-40554, 61028, -51266, -12095, 175784], ![-861, -32, -3180, 24, 7543]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-421, 891, -304, -177, 1496]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-421, 891, -304, -177, 1496]] 
 ![![37, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![-421, 891, -304, -177, 1496], ![902, -7021, 6008, 1389, -20474], ![10390, 290, -15862, -33, 38390], ![-21888, 79372, -50419, -15730, 189376], ![974, 6056, -7806, -1194, 23969]]]
  hmulB := by decide  
  f := ![![![-7807, -1925, 11370, 3408, -46294]], ![![-2478, -341, 3329, 1014, -13480]], ![![-7498, -902, 10010, 3057, -40488]], ![![-5075, 1793, 4363, 1490, -16912]], ![![-8163, -1621, 11512, 3474, -46761]]]
  g := ![![![-1440, 891, -304, -177, 1496], ![16963, -7021, 6008, 1389, -20474], ![-24977, 290, -15862, -33, 38390], ![-164556, 79372, -50419, -15730, 189376], ![-18711, 6056, -7806, -1194, 23969]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-8428069, 2468651, -2867956, -574158, 11764422]] ![![-293, 990, -602, -192, 2272]]
  ![![-7807, -1925, 11370, 3408, -46294]] where
 M := ![![![-7807, -1925, 11370, 3408, -46294]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-7807, -1925, 11370, 3408, -46294]] ![![-421, 891, -304, -177, 1496]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5495, -3595, -4460, 723, 7638]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![5495, -3595, -4460, 723, 7638]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![31, 16, 36, 1, 0], ![32, 4, 15, 0, 1]] where
  M :=![![![5495, -3595, -4460, 723, 7638], ![-31182, 114947, -73790, -22779, 276114], ![-51090, -379050, 473800, 74757, -1464690], ![411212, -879888, 306511, 174772, -1492404], ![18094, -162044, 142752, 32052, -482369]]]
  hmulB := by decide  
  f := ![![![83545, -8383, 24072, 5334, -93072]], ![![68796, -5495, 14459, 2874, -54852]], ![![46476, -7404, 24140, 6015, -95412]], ![![131677, -15017, 45099, 10438, -175746]], ![![88826, -9806, 29112, 6669, -113237]]]
  g := ![![![-6374, -1115, -3538, 723, 7638], ![-199041, -15245, -82816, -22779, 276114], ![1085403, 104478, 481778, 74757, -1464690], ![1042688, 55936, 400019, 174772, -1492404], ![352690, 30600, 151815, 32052, -482369]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [10, 39, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 28, 1], [7, 12, 40], [0, 1]]
 g := ![![[25, 4, 4], [6, 20], [9, 21], [11, 3, 1], []], ![[10, 35, 36, 33], [17, 36], [10, 21], [16, 34, 40, 21], [18, 1]], ![[11, 3, 39, 39], [31, 31], [], [7, 37, 27, 36], [20, 1]]]
 h' := ![![[37, 28, 1], [31, 39, 2], [38, 10, 26], [13, 33, 29], [0, 0, 1], [0, 1]], ![[7, 12, 40], [39, 40, 22], [39, 11, 35], [4, 20, 12], [0, 7, 12], [37, 28, 1]], ![[0, 1], [2, 3, 17], [36, 20, 21], [6, 29], [13, 34, 28], [7, 12, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 6], []]
 b := ![[], [14, 39, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [10, 39, 38, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![586702396, -222448814, -505107722, -229439931, 559189644]
  a := ![135, -541, 372, 87, -1436]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-248651911, 29556866, -15441826, -229439931, 559189644]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83545, -8383, 24072, 5334, -93072]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![83545, -8383, 24072, 5334, -93072]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![25, 14, 1, 0, 0], ![1, 16, 0, 1, 0], ![30, 15, 0, 0, 1]] where
  M :=![![![83545, -8383, 24072, 5334, -93072], ![68796, -5495, 14459, 2874, -54852], ![46476, -7404, 24140, 6015, -95412], ![34990, -1360, 2443, 80, -7890], ![-3898, -750, 3352, 1020, -13825]]]
  hmulB := by decide  
  f := ![![![5495, -3595, -4460, 723, 7638]], ![![-31182, 114947, -73790, -22779, 276114]], ![![-8543, 27813, -16360, -5514, 63216]], ![![-2005, 23309, -21429, -4609, 71538]], ![![-6946, 35471, -26778, -7023, 94841]]]
  g := ![![![55331, 23545, 24072, 5334, -93072], ![32927, 13875, 14459, 2874, -54852], ![56081, 24136, 24140, 6015, -95412], ![5135, 1988, 2443, 80, -7890], ![7952, 3497, 3352, 1020, -13825]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [39, 30, 1] where
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
 g := ![![[26, 20], [21], [16], [22, 39], [1]], ![[0, 21], [21], [16], [0, 2], [1]]]
 h' := ![![[11, 40], [1, 26], [0, 29], [3, 37], [2, 11], [0, 1]], ![[0, 1], [0, 15], [32, 12], [0, 4], [0, 30], [11, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [36, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [39, 30, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-672697, 1517424, -651232, -168092, 3093792]
  a := ![132, -528, 368, 74, -1404]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1878965, -806896, -651232, -168092, 3093792]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![5495, -3595, -4460, 723, 7638]] ![![83545, -8383, 24072, 5334, -93072]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26879, -31801, 73580, 6219, -204228]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-26879, -31801, 73580, 6219, -204228]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![3, 42, 12, 1, 0], ![2, 6, 11, 0, 1]] where
  M :=![![![-26879, -31801, 73580, 6219, -204228], ![271638, -704975, 332172, 139893, -1403946], ![-269754, 4158546, -3954836, -822093, 13079718], ![-2781048, 3340972, 662449, -666464, 1275336], ![-277746, 1301984, -948778, -257838, 3399139]]]
  hmulB := by decide  
  f := ![![![-259775, 24241, -67772, -14580, 260658]], ![![-200556, 21133, -61239, -13776, 237492]], ![![-171912, 12108, -27260, -4629, 101304]], ![![-264105, 26027, -73009, -15968, 281808]], ![![-84028, 7134, -18496, -3735, 70471]]]
  g := ![![![8440, 21683, 52220, 6219, -204228], ![61857, 42865, 327834, 139893, -1403946], ![-557277, -925392, -3208526, -822093, 13079718], ![-77496, 550708, -124853, -666464, 1275336], ![-146570, -192178, -819657, -257838, 3399139]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [20, 19, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 37, 16], [22, 5, 27], [0, 1]]
 g := ![![[37, 36, 35], [25, 5, 36], [42, 36], [21, 13, 1], []], ![[22, 37, 9, 36], [37, 26, 41, 40], [33, 11], [28, 37, 10, 13], [40, 41]], ![[40, 23, 23, 18], [27, 41, 22, 8], [41, 41], [29, 8, 30, 26], [29, 41]]]
 h' := ![![[34, 37, 16], [16, 22, 11], [34, 8, 6], [10, 29, 6], [0, 0, 1], [0, 1]], ![[22, 5, 27], [36, 16, 20], [34, 21, 29], [36, 24, 21], [12, 33, 5], [34, 37, 16]], ![[0, 1], [3, 5, 12], [21, 14, 8], [29, 33, 16], [33, 10, 37], [22, 5, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 19], []]
 b := ![[], [28, 2, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [20, 19, 30, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9392265336, 16311506596, -4408661245, -549427858, 29154305362]
  a := ![-226, 916, -624, -131, 2405]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1536106802, -3152054780, -7407276417, -549427858, 29154305362]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37153, -3559, 10048, 2186, -38722]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![37153, -3559, 10048, 2186, -38722]] 
 ![![43, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] where
  M :=![![![37153, -3559, 10048, 2186, -38722], ![29352, -2811, 7935, 1726, -30584], ![23196, -2264, 6304, 1367, -24292], ![13902, -1508, 3839, 836, -14834], ![-678, 42, -170, -38, 653]]]
  hmulB := by decide  
  f := ![![![5631061, 2245827, -9152008, -2691739, 37492316]], ![![2645303, 1055022, -4299338, -1264498, 17612762]], ![![4955256, 1976296, -8053640, -2368693, 32992718]], ![![4360358, 1739034, -7086769, -2084322, 29031812]], ![![4581530, 1827244, -7446234, -2190046, 30504405]]]
  g := ![![![22642, -3559, 10048, 2186, -38722], ![17885, -2811, 7935, 1726, -30584], ![14222, -2264, 6304, 1367, -24292], ![8752, -1508, 3839, 836, -14834], ![-372, 42, -170, -38, 653]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1591872407, 634883864, -2587226214, -760940972, 10598887612]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![1591872407, 634883864, -2587226214, -760940972, 10598887612]] 
 ![![43, 0, 0, 0, 0], ![26, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![1591872407, 634883864, -2587226214, -760940972, 10598887612], ![-4457073840, -1777607457, 7243958922, 2130553994, -29675760880], ![12479333892, 4977112352, -20282316493, -5965325156, 83088982276], ![-7487159076, -2986091276, 12168672588, 3578984131, -49850450788], ![4752620688, 1895479948, -7724303064, -2271830212, 31643549227]]]
  hmulB := by decide  
  f := ![![![373637, -514024, -20694, 102412, -391532]], ![![191734, -147161, -132846, 29518, 193096]], ![![-42480, -450304, 535595, 88852, -1674452]], ![![804535, -1860268, 745146, 369351, -3388784]], ![![74104, -287212, 190080, 56908, -703629]]]
  g := ![![![-1083539679, 634883864, -2587226214, -760940972, 10598887612], ![3033796144, -1777607457, 7243958922, 2130553994, -29675760880], ![-8494307396, 4977112352, -20282316493, -5965325156, 83088982276], ![5096283943, -2986091276, 12168672588, 3578984131, -49850450788], ![-3234966020, 1895479948, -7724303064, -2271830212, 31643549227]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-26879, -31801, 73580, 6219, -204228]] ![![37153, -3559, 10048, 2186, -38722]]
  ![![-373637, 514024, 20694, -102412, 391532]] where
 M := ![![![-373637, 514024, 20694, -102412, 391532]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-373637, 514024, 20694, -102412, 391532]] ![![1591872407, 634883864, -2587226214, -760940972, 10598887612]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![30317, 12081, -49345, -14514, 202134]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![30317, 12081, -49345, -14514, 202134]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![34, 6, 1, 0, 0], ![6, 17, 0, 1, 0], ![46, 32, 0, 0, 1]] where
  M :=![![![30317, 12081, -49345, -14514, 202134], ![-84960, -34111, 138244, 40647, -566400], ![238566, 93576, -386222, -113679, 1581798], ![-141364, -60274, 233601, 68494, -957972], ![90886, 35600, -147068, -43290, 602317]]]
  hmulB := by decide  
  f := ![![![1057, 7773, -9731, -1533, 30072]], ![![-26418, 46585, -9271, -9264, 62286]], ![![-922, 1614, -312, -321, 2136]], ![![-4930, 17751, -11224, -3518, 42228]], ![![-16188, 36804, -14338, -7308, 66073]]]
  g := ![![![-159639, -125817, -49345, -14514, 202134], ![447346, 352558, 138244, 40647, -566400], ![-1249160, -984555, -386222, -113679, 1581798], ![756850, 596358, 233601, 68494, -957972], ![-475652, -374898, -147068, -43290, 602317]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [13, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 46], [0, 1]]
 g := ![![[11, 25], [3, 9], [16, 42], [44, 4], [1]], ![[8, 22], [32, 38], [26, 5], [36, 43], [1]]]
 h' := ![![[45, 46], [8, 42], [27, 3], [39, 29], [34, 45], [0, 1]], ![[0, 1], [18, 5], [21, 44], [28, 18], [38, 2], [45, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [13, 2, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1478, 4744, -2990, -426, 12318]
  a := ![3, -16, 9, 0, -32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9870, -7750, -2990, -426, 12318]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![847, -722, 456, 80, -2032]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![847, -722, 456, 80, -2032]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![7, 22, 1, 0, 0], ![45, 5, 0, 1, 0], ![32, 27, 0, 0, 1]] where
  M :=![![![847, -722, 456, 80, -2032], ![2304, -4305, 2070, 328, -9728], ![12240, -27200, 12529, 1946, -59440], ![29436, -66784, 30618, 4745, -145412], ![4836, -11068, 5064, 784, -24061]]]
  hmulB := by decide  
  f := ![![![65, 14, -108, -8, 304]], ![![-432, 1185, -606, -220, 2384]], ![![-191, 440, -179, -82, 776]], ![![111, -19, -144, 1, 348]], ![![-196, 649, -390, -124, 1467]]]
  g := ![![![1257, 930, 456, 80, -2032], ![6050, 4493, 2070, 328, -9728], ![37001, 27496, 12529, 1946, -59440], ![90527, 67277, 30618, 4745, -145412], ![14980, 11133, 5064, 784, -24061]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [14, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 46], [0, 1]]
 g := ![![[15, 37], [10, 9], [45, 17], [26, 14], [1]], ![[0, 10], [0, 38], [0, 30], [0, 33], [1]]]
 h' := ![![[25, 46], [1, 15], [28, 44], [12, 39], [33, 25], [0, 1]], ![[0, 1], [0, 32], [0, 3], [0, 8], [0, 22], [25, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [5, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [14, 22, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-110890, 159602, -11656, -10839, 203421]
  a := ![-64, 259, -173, -42, 681]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-128745, -106854, -11656, -10839, 203421]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7915, -334205, 362147, 65999, -1157716]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![-7915, -334205, 362147, 65999, -1157716]] 
 ![![47, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-7915, -334205, 362147, 65999, -1157716], ![863454, -1146299, -91427, 228454, -764258], ![-3497472, 16381858, -11933534, -3244183, 42758624], ![-5880898, -5350658, 14414175, 1043198, -39253154], ![-1326494, 3733582, -1927076, -740618, 7839035]]]
  hmulB := by decide  
  f := ![![![183757, -370285, 194359, 33316, -902282]], ![![97085, -198586, 100107, 16659, -467646]], ![![194235, -431945, 208531, 33761, -981820]], ![![353800, -800194, 366821, 56824, -1742076]], ![![70722, -159316, 76092, 12222, -358937]]]
  g := ![![![112269, -334205, 362147, 65999, -1157716], ![556548, -1146299, -91427, 228454, -764258], ![-6251224, 16381858, -11933534, -3244183, 42758624], ![689549, -5350658, 14414175, 1043198, -39253154], ![-1526640, 3733582, -1927076, -740618, 7839035]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![30317, 12081, -49345, -14514, 202134]] ![![847, -722, 456, 80, -2032]]
  ![![-183757, 370285, -194359, -33316, 902282]] where
 M := ![![![-183757, 370285, -194359, -33316, 902282]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-183757, 370285, -194359, -33316, 902282]] ![![-7915, -334205, 362147, 65999, -1157716]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![-47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17893, 6959, -28891, -8524, 118560]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![17893, 6959, -28891, -8524, 118560]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![2, 10, 52, 1, 0], ![39, 21, 50, 0, 1]] where
  M :=![![![17893, 6959, -28891, -8524, 118560], ![-49592, -20859, 81574, 24139, -334776], ![138494, 65984, -235808, -69085, 961662], ![-88320, -35010, 144507, 40532, -580320], ![52678, 23740, -88250, -26036, 361307]]]
  hmulB := by decide  
  f := ![![![-45709, 84577, -40769, -6467, 191490]], ![![-240706, 534135, -246127, -38236, 1167582]], ![![-1493972, 3400018, -1557670, -241313, 7398924]], ![![-1582000, 3597474, -1648431, -255396, 7829718]], ![![-1549855, 3507572, -1608984, -249415, 7640483]]]
  g := ![![![-86583, -45237, -104031, -8524, 118560], ![244498, 127699, 293682, 24139, -334776], ![-702418, -366756, -843896, -69085, 961662], ![423832, 221630, 510431, 40532, -580320], ![-263891, -137799, -316976, -26036, 361307]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [43, 2, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 16, 30], [41, 36, 23], [0, 1]]
 g := ![![[13, 12, 49], [39, 38], [39, 27, 46], [37, 38], [1]], ![[37, 49, 14, 14], [23, 52], [35, 3, 27, 50], [37, 1], [28, 6, 16, 23]], ![[32, 44, 13, 8], [15, 15], [7, 51, 31, 21], [22, 10], [43, 45, 40, 30]]]
 h' := ![![[24, 16, 30], [9, 26, 46], [19, 29, 12], [46, 1, 29], [10, 51, 12], [0, 1]], ![[41, 36, 23], [42, 8, 51], [17, 5, 30], [35, 33, 14], [6, 39, 1], [24, 16, 30]], ![[0, 1], [50, 19, 9], [35, 19, 11], [48, 19, 10], [27, 16, 40], [41, 36, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 29], []]
 b := ![[], [37, 1, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [43, 2, 41, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-234274005, 170700710, 123735965, 60048630, 8504400]
  a := ![-91, 366, -251, -58, 968]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12944205, -11478830, -64604015, 60048630, 8504400]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-356185, -142056, 578897, 170262, -2371522]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-356185, -142056, 578897, 170262, -2371522]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![27, 2, 1, 0, 0], ![44, 26, 0, 1, 0], ![27, 39, 0, 0, 1]] where
  M :=![![![-356185, -142056, 578897, 170262, -2371522], ![997280, 397739, -1620847, -476715, 6640000], ![-2792270, -1113640, 4538201, 1334754, -18591310], ![1675254, 668194, -2722798, -800815, 11154262], ![-1063408, -424114, 1728324, 508326, -7080295]]]
  hmulB := by decide  
  f := ![![![47017, -4624, 12759, 2772, -49220]], ![![37456, -4367, 10405, 2241, -40432]], ![![25961, -2670, 7086, 1536, -27386]], ![![57842, -6252, 15896, 3437, -61562]], ![![51515, -5607, 14170, 3063, -54895]]]
  g := ![![![765154, 1637032, 578897, 170262, -2371522], ![-2142347, -4583509, -1620847, -476715, 6640000], ![5998349, 12833348, 4538201, 1334754, -18591310], ![-3598838, -7699646, -2722798, -800815, 11154262], ![2284405, 4887439, 1728324, 508326, -7080295]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [28, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 52], [0, 1]]
 g := ![![[30, 36], [43], [48, 24], [24], [8, 1]], ![[0, 17], [43], [28, 29], [24], [16, 52]]]
 h' := ![![[8, 52], [5, 6], [34, 34], [2, 17], [41, 36], [0, 1]], ![[0, 1], [0, 47], [41, 19], [32, 36], [11, 17], [8, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [44, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [28, 45, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-437866, 894836, -324082, -94947, 1689606]
  a := ![-111, 448, -307, -66, 1181]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-625082, -1167604, -324082, -94947, 1689606]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![17893, 6959, -28891, -8524, 118560]] ![![-356185, -142056, 578897, 170262, -2371522]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-59119191691, -23578410563, 96084788249, 28259938087, -393623050424]]]
 hmul := by decide  
 g := ![![![![-1115456447, -444875671, 1812920533, 533206379, -7426850008]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [58, 25, 36, 24, 14, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 35, 42, 27, 22], [30, 7, 34, 42, 21], [41, 17, 2, 11, 30], [20, 58, 40, 38, 45], [0, 1]]
 g := ![![[13, 53, 30, 21, 53], [37, 27, 41, 16, 46], [0, 20, 8, 20], [54, 45, 1], []], ![[16, 14, 15, 41, 29, 24, 58, 28], [38, 50, 43, 44, 39, 43, 29, 9], [50, 41, 19, 5], [34, 45, 51, 55, 30, 52, 21, 5], [24, 17, 48, 33, 36, 6, 49, 28]], ![[48, 9, 42, 58, 47, 42, 47, 12], [27, 22, 23, 19, 22, 15, 48, 5], [29, 52, 44, 29], [41, 15, 22, 17, 45, 12, 57, 35], [0, 14, 45, 6, 47, 1, 16, 57]], ![[5, 5, 15, 29, 42, 9, 47, 55], [16, 26, 0, 50, 51, 45, 12, 10], [12, 22, 9, 49], [26, 44, 3, 2, 3, 39, 56, 10], [4, 41, 17, 4, 18, 30, 36, 37]], ![[37, 6, 23, 47, 30, 56, 6, 4], [50, 3, 17, 49, 34, 12, 24, 45], [0, 3, 18, 41], [35, 56, 41, 22, 39, 22, 52, 20], [39, 20, 38, 32, 20, 17, 49, 29]]]
 h' := ![![[13, 35, 42, 27, 22], [37, 22, 56, 14, 42], [25, 31, 29, 13, 39], [54, 52, 0, 9, 16], [0, 0, 0, 1], [0, 1]], ![[30, 7, 34, 42, 21], [46, 31, 52, 20, 22], [39, 8, 51, 5, 20], [44, 44, 46, 24, 8], [38, 52, 37, 11, 14], [13, 35, 42, 27, 22]], ![[41, 17, 2, 11, 30], [35, 39, 29, 46, 3], [55, 32, 24, 44, 15], [47, 37, 2, 42, 18], [37, 34, 30, 26, 10], [30, 7, 34, 42, 21]], ![[20, 58, 40, 38, 45], [3, 32, 14, 3, 46], [2, 33, 45, 19, 43], [52, 41, 1, 37, 7], [13, 4, 54, 28, 16], [41, 17, 2, 11, 30]], ![[0, 1], [19, 53, 26, 35, 5], [5, 14, 28, 37, 1], [51, 3, 10, 6, 10], [15, 28, 56, 52, 19], [20, 58, 40, 38, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 30, 32, 54], [], [], []]
 b := ![[], [10, 14, 36, 24, 19], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 5
  hpos := by decide
  P := [58, 25, 36, 24, 14, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![180073448235820, -134086661556108, -112784909576746, -5045269350796, 102071042502506]
  a := ![67, -259, 176, 49, -712]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3052092342980, -2272655280612, -1911608636894, -85513039844, 1730017669534]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1373935, -132166, 374008, 81527, -1441792]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![1373935, -132166, 374008, 81527, -1441792]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![8, 51, 50, 23, 1]] where
  M :=![![![1373935, -132166, 374008, 81527, -1441792], ![1089990, -102441, 287847, 62173, -1107770], ![847734, -85406, 248239, 55292, -960298], ![517302, -44588, 127658, 27071, -488714], ![-29376, 1218, -722, 334, 1391]]]
  hmulB := by decide  
  f := ![![![-323, 4770, -4516, -943, 14954]], ![![-9162, 6417, 6993, -1289, -11306]], ![![50970, -190430, 123277, 37736, -459910]], ![![46866, 140616, -217562, -27667, 643858]], ![![52016, -97695, 24511, 19420, -142809]]]
  g := ![![![211611, 1203266, 1187928, 544963, -1441792], ![163150, 924489, 912727, 418703, -1107770], ![139838, 801472, 791199, 362986, -960298], ![72574, 407866, 402678, 184713, -488714], ![-664, -1143, -1152, -519, 1391]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 4 2 5 [60, 41, 18, 46, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 52, 41, 32], [13, 37, 36, 23], [42, 32, 45, 6], [0, 1]]
 g := ![![[21, 17, 24, 25], [11, 50, 52], [59, 52, 60, 36], [49, 24, 15, 1], []], ![[23, 37, 37, 50, 28, 33], [47, 2, 34], [46, 47, 58, 22, 60, 6], [13, 46, 32, 50, 21, 29], [10, 60, 39, 24, 30, 11]], ![[20, 19, 52, 53, 5, 50], [59, 56, 39], [20, 51, 16, 60, 13, 31], [60, 1, 56, 38, 34, 38], [40, 10, 43, 27, 29, 28]], ![[60, 24, 12, 58, 58, 43], [18, 44, 19], [15, 29, 23, 12, 50, 24], [1, 37, 52, 22, 2, 6], [50, 37, 39, 16, 48, 33]]]
 h' := ![![[21, 52, 41, 32], [15, 12, 32, 5], [59, 34, 37, 33], [49, 28, 40, 55], [0, 0, 0, 1], [0, 1]], ![[13, 37, 36, 23], [31, 53, 16, 49], [44, 10, 30, 20], [34, 7, 49, 2], [60, 4, 15, 50], [21, 52, 41, 32]], ![[42, 32, 45, 6], [34, 3, 40, 41], [6, 4, 60, 51], [14, 37, 28, 2], [41, 49, 40, 11], [13, 37, 36, 23]], ![[0, 1], [57, 54, 34, 27], [10, 13, 56, 18], [15, 50, 5, 2], [23, 8, 6, 60], [42, 32, 45, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [59, 13, 20], []]
 b := ![[], [], [14, 53, 3, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 4
  hpos := by decide
  P := [60, 41, 18, 46, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-685166223802, 1982093672708, -1193572255950, -114973272894, 5041293461900]
  a := ![96, -380, 263, 61, -1021]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-672385474082, -4182358571872, -4151774513950, -1902700375354, 5041293461900]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 13845841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![323, -4770, 4516, 943, -14954]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![323, -4770, 4516, 943, -14954]] 
 ![![61, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![323, -4770, 4516, 943, -14954], ![9162, -6417, -6993, 1289, 11306], ![-50970, 190430, -123277, -37736, 459910], ![-46866, -140616, 217562, 27667, -643858], ![-16404, 37490, -14732, -7444, 67609]]]
  hmulB := by decide  
  f := ![![![-1373935, 132166, -374008, -81527, 1441792]], ![![-761145, 73179, -207051, -45124, 798146]], ![![-216609, 20900, -59251, -12935, 228466]], ![![-594092, 57064, -161506, -35193, 622546]], ![![-67089, 6480, -18382, -4015, 70885]]]
  g := ![![![2253, -4770, 4516, 943, -14954], ![3548, -6417, -6993, 1289, 11306], ![-92201, 190430, -123277, -37736, 459910], ![63076, -140616, 217562, 27667, -643858], ![-18529, 37490, -14732, -7444, 67609]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![1373935, -132166, 374008, 81527, -1441792]] ![![323, -4770, 4516, 943, -14954]]
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


lemma PB5356I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB5356I1 : PrimesBelowBoundCertificateInterval O 23 61 5356 where
  m := 9
  g := ![3, 1, 3, 2, 3, 3, 2, 1, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB5356I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
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
    · exact ![50653, 37, 37]
    · exact ![68921, 1681]
    · exact ![79507, 43, 43]
    · exact ![2209, 2209, 47]
    · exact ![148877, 2809]
    · exact ![714924299]
    · exact ![13845841, 61]
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
      exact NI37N1
      exact NI37N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I29N0, I29N1, I29N2, I37N1, I37N2, I41N1, I43N1, I43N2, I47N0, I47N1, I47N2, I53N1, I61N1]
  Il := ![[I29N0, I29N1, I29N2], [], [I37N1, I37N2], [I41N1], [I43N1, I43N2], [I47N0, I47N1, I47N2], [I53N1], [], [I61N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
