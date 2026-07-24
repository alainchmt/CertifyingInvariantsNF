
import IdealArithmetic.Examples.NF5_1_145800000_5.RI5_1_145800000_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 516, 294, 124, 8]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![277, 516, 294, 124, 8]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![5, 2, 18, 1, 0], ![26, 19, 26, 0, 1]] where
  M :=![![![277, 516, 294, 124, 8], ![-48, 507, 1112, 580, 248], ![-744, -460, 1747, 988, 580], ![-1716, -2072, 1884, 1167, 864], ![-2592, -3372, 2248, 1452, 1167]]]
  hmulB := by decide  
  f := ![![![-151, -212, 318, -108, -32]], ![![192, 423, -744, 668, -216]], ![![648, 588, -657, -636, 668]], ![![317, 258, -256, -413, 376]], ![![626, 725, -982, -72, 383]]]
  g := ![![![-19, 4, -74, 124, 8], ![-324, -185, -544, 580, 248], ![-716, -464, -1073, 988, 580], ![-1035, -718, -1434, 1167, 864], ![-1386, -981, -1870, 1452, 1167]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [15, 23, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 6, 9], [5, 22, 20], [0, 1]]
 g := ![![[6, 13, 5], [3, 20], [6, 3, 4], [1]], ![[6, 17, 13, 7], [14, 6], [26, 14, 20, 16], [23, 9, 16, 4]], ![[18, 3, 17, 16], [13, 22], [6, 4, 15, 16], [0, 17, 2, 25]]]
 h' := ![![[26, 6, 9], [22, 17, 18], [26, 13, 22], [14, 6, 2], [0, 1]], ![[5, 22, 20], [23, 16, 27], [28, 18, 21], [5, 20, 11], [26, 6, 9]], ![[0, 1], [24, 25, 13], [25, 27, 15], [9, 3, 16], [5, 22, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 9], []]
 b := ![[], [13, 13, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [15, 23, 27, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14547, -31251, 69177, -56164, 21191]
  a := ![0, -2, -3, -3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9817, -11088, 18247, -56164, 21191]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![133385, 73015, -29082, -296580, 217598]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![133385, 73015, -29082, -296580, 217598]] 
 ![![29, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![133385, 73015, -29082, -296580, 217598], ![-1305588, -1636481, 2322010, -275762, -593160], ![1779480, 2880851, -4602281, 2618590, -275762], ![1480080, 509888, 341036, -4326519, 2915170], ![-8745510, -10750122, 15085738, -1116549, -4326519]]]
  hmulB := by decide  
  f := ![![![2159582433853, -1073323688913, 121122761640, -59913463772, 207676081066]], ![![254905974104, -126689593403, 14296706186, -7071876306, 24513013680]], ![![1576231444605, -783395216682, 88404824265, -43729511814, 151578177400]], ![![1060464620362, -527056425558, 59477425552, -29420552613, 101979499838]], ![![69302115611, -34443511487, 3886891970, -1922653997, 6664432693]]]
  g := ![![![151261, 73015, -29082, -296580, 217598], ![-1347174, -1636481, 2322010, -275762, -593160], ![1742051, 2880851, -4602281, 2618590, -275762], ![1721892, 509888, 341036, -4326519, 2915170], ![-9054735, -10750122, 15085738, -1116549, -4326519]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37573796185, 18674371903, -2107371262, 1042412756, -3613281262]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![-37573796185, 18674371903, -2107371262, 1042412756, -3613281262]] 
 ![![29, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-37573796185, 18674371903, -2107371262, 1042412756, -3613281262], ![21679687572, -10774917351, 1215931186, -601461262, 2084825512], ![-6254476536, 3108507331, -350789791, 173518430, -601461262], ![-9035460000, 4490670560, -506764572, 250671471, -868894326], ![2606682978, -1295534982, 146198930, -72317409, 250671471]]]
  hmulB := by decide  
  f := ![![![2803, 3711, -5200, 1140, 1014]], ![![1530, 1941, -2622, 314, 708]], ![![924, 1419, -2121, 1038, 26]], ![![3992, 5236, -7408, 1525, 1506]], ![![-711, -1507, 2674, -2297, 739]]]
  g := ![![![-11899726245, 18674371903, -2107371262, 1042412756, -3613281262], ![6866017634, -10774917351, 1215931186, -601461262, 2084825512], ![-1980810196, 3108507331, -350789791, 173518430, -601461262], ![-2861555430, 4490670560, -506764572, 250671471, -868894326], ![825543783, -1295534982, 146198930, -72317409, 250671471]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![277, 516, 294, 124, 8]] ![![133385, 73015, -29082, -296580, 217598]]
  ![![-2803, -3711, 5200, -1140, -1014]] where
 M := ![![![-2803, -3711, 5200, -1140, -1014]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-2803, -3711, 5200, -1140, -1014]] ![![-37573796185, 18674371903, -2107371262, 1042412756, -3613281262]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 5 2 4 [26, 6, 10, 1, 9, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 30, 22, 22, 2], [13, 10, 10, 8, 20], [7, 10, 10, 22, 5], [29, 11, 20, 10, 4], [0, 1]]
 g := ![![[7, 24, 11, 15, 19], [16, 11, 22, 11, 2], [18, 22, 1], []], ![[7, 13, 14, 9, 19, 15, 24, 2], [4, 28, 18, 5, 15, 30, 20, 2], [18, 26, 5, 6, 11, 1, 21, 10], [0, 8, 26, 2, 29, 6, 6, 8]], ![[7, 11, 6, 21, 29, 4, 4, 14], [21, 6, 6, 25, 7, 22, 23, 25], [11, 22, 3, 15, 14, 22, 3, 20], [16, 17, 3, 21, 8, 1, 3, 2]], ![[23, 4, 0, 7, 10, 11, 3, 2], [18, 16, 23, 0, 7, 23, 26, 16], [17, 10, 22, 29, 19, 1, 14, 28], [26, 19, 12, 0, 28, 29, 29, 1]], ![[7, 6, 16, 21, 22, 25], [8, 17, 1, 5, 21, 23, 27, 4], [1, 28, 6, 11, 9, 4], [24, 0, 18, 16, 7, 15, 28, 2]]]
 h' := ![![[4, 30, 22, 22, 2], [18, 30, 27, 0, 22], [28, 2, 3, 4, 23], [0, 0, 0, 1], [0, 1]], ![[13, 10, 10, 8, 20], [14, 8, 24, 5, 1], [13, 14, 20, 27, 30], [2, 23, 3, 22, 6], [4, 30, 22, 22, 2]], ![[7, 10, 10, 22, 5], [25, 22, 21, 6, 17], [30, 3, 3, 13, 28], [14, 6, 12, 16, 1], [13, 10, 10, 8, 20]], ![[29, 11, 20, 10, 4], [1, 24, 11, 2, 22], [6, 17, 28, 23, 11], [8, 14, 1, 24, 24], [7, 10, 10, 22, 5]], ![[0, 1], [8, 9, 10, 18], [27, 26, 8, 26, 1], [19, 19, 15, 30], [29, 11, 20, 10, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 17, 22, 20], [], [], []]
 b := ![[], [12, 24, 2, 9, 21], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 5
  hpos := by decide
  P := [26, 6, 10, 1, 9, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17173779521893, -22910050834187, 34713457514604, -9101594488975, -5265086723169]
  a := ![3, -65, 2, -66, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-553992887803, -739033897877, 1119788952084, -293599822225, -169841507199]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-631750537589, 313983299178, -35432483880, 17526704402, -60752242560]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-631750537589, 313983299178, -35432483880, 17526704402, -60752242560]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![35, 13, 12, 20, 1]] where
  M :=![![![-631750537589, 313983299178, -35432483880, 17526704402, -60752242560], ![364513455360, -181165080989, 20444172756, -10112725200, 35053408804], ![-105160226412, 52265178842, -5898036969, 2917468354, -10112725200], ![-151918552080, 75504309604, -8520533536, 4214688231, -14609236048], ![43827708144, -21782598616, 2458129364, -1215915512, 4214688231]]]
  hmulB := by decide  
  f := ![![![-72401, -91450, 68928, 43742, 33976]], ![![-203856, -275281, 156860, 103880, 87484]], ![![-262452, -373434, 162139, 113118, 103880]], ![![-209712, -328036, 67536, 58259, 69376]], ![![-344215, -491079, 209916, 146942, 135643]]]
  g := ![![![40393998703, 29831417634, 18745795320, 33312744746, -60752242560], ![-23306914940, -17212416093, -10816127916, -19221105440, 35053408804], ![6723923124, 4965692066, 3120396363, 5545188442, -10112725200], ![9713640800, 7173631844, 4507845920, 8010794843, -14609236048], ![-2802334593, -2069555287, -1300489984, -2311072436, 4214688231]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 4 2 5 [36, 20, 17, 9, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 15, 10], [28, 9, 20, 31], [12, 12, 7, 6], [0, 1]]
 g := ![![[25, 25, 35, 11], [12, 21, 34], [19, 8, 21, 7], [1], []], ![[19, 27, 24, 19, 10], [32, 23, 7], [25, 17, 20, 33, 30], [8, 2, 27], [26]], ![[19, 11, 27, 1, 19, 14], [15, 34, 30], [21, 8, 25, 23, 14, 6], [20, 14, 30], [20, 28, 36]], ![[30, 1, 13, 23, 33, 15], [17, 26, 25], [7, 27, 29, 18], [36, 15, 7], [2, 19, 36]]]
 h' := ![![[25, 15, 10], [3, 2, 19, 23], [19, 36, 16, 16], [1, 17, 20, 28], [0, 0, 1], [0, 1]], ![[28, 9, 20, 31], [29, 15, 1, 1], [16, 29, 13, 9], [11, 9, 9, 15], [22, 8, 24, 29], [25, 15, 10]], ![[12, 12, 7, 6], [3, 15, 15, 26], [32, 20, 22, 17], [9, 8, 30, 31], [27, 21, 4, 17], [28, 9, 20, 31]], ![[0, 1], [33, 5, 2, 24], [4, 26, 23, 32], [3, 3, 15], [35, 8, 8, 28], [12, 12, 7, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [28, 4, 4], []]
 b := ![[], [], [5, 21, 13, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 4
  hpos := by decide
  P := [36, 20, 17, 9, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-409423, -585186, 652751, -202284, -173188]
  a := ![1, -4, -1, -5, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![152761, 45034, 73811, 88148, -173188]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1874161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4409, -13649, 25794, -28941, 11538]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-4409, -13649, 25794, -28941, 11538]] 
 ![![37, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-4409, -13649, 25794, -28941, 11538], ![-69228, -70919, 88082, 40050, -57882], ![173646, 240955, -360329, 117023, 40050], ![-85536, -218082, 397164, -400379, 145964], ![-437892, -428042, 511738, 324182, -400379]]]
  hmulB := by decide  
  f := ![![![-172526387249, 85746510781, -9676348620, 4786413001, -16590986960]], ![![-155847330938, 77456933145, -8740883814, 4323684642, -14987046774]], ![![-66056429716, 32830388751, -3704853807, 1832608675, -6352311560]], ![![-19772794028, 9827181358, -1108980784, 548558165, -1901449240]], ![![-27653764902, 13744064826, -1550994454, 767200554, -2659322207]]]
  g := ![![![3921, -13649, 25794, -28941, 11538], ![35026, -70919, 88082, 40050, -57882], ![-99530, 240955, -360329, 117023, 40050], ![67424, -218082, 397164, -400379, 145964], ![217750, -428042, 511738, 324182, -400379]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-631750537589, 313983299178, -35432483880, 17526704402, -60752242560]] ![![-4409, -13649, 25794, -28941, 11538]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![262885, 312835, -430902, -1369, 146890]]]
 hmul := by decide  
 g := ![![![![7105, 8455, -11646, -37, 3970]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [2, 25, 9, 14, 23, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 6, 29, 4, 12], [9, 5, 27, 4, 33], [18, 31, 28, 37, 18], [9, 39, 39, 37, 19], [0, 1]]
 g := ![![[9, 36, 18, 29, 20], [3, 29, 1, 23], [14, 15, 39, 37], [1], []], ![[21, 32, 20, 2, 15, 8, 21, 34], [0, 39, 29, 8], [11, 37, 14, 20], [19, 8, 15, 15, 35, 12, 16, 11], [40, 12, 23, 21]], ![[12, 32, 21, 6, 28, 29, 2, 32], [17, 5, 17, 32], [20, 37, 21, 2], [22, 28, 15, 38, 34, 13, 12, 40], [25, 27, 22, 23]], ![[20, 13, 6, 25, 34, 10, 15, 32], [32, 21, 14, 33], [17, 38, 28, 10], [29, 10, 31, 24, 12, 5, 7, 20], [25, 21, 30, 37]], ![[20, 32, 24, 27, 10, 34, 36, 26], [23, 31, 4, 37], [32, 16, 4, 16], [38, 33, 7, 11, 8, 26, 30, 6], [3, 13, 32, 33]]]
 h' := ![![[23, 6, 29, 4, 12], [37, 23, 33, 4, 15], [17, 7, 0, 28, 8], [39, 16, 32, 27, 18], [0, 0, 1], [0, 1]], ![[9, 5, 27, 4, 33], [2, 16, 8, 13, 18], [24, 31, 29, 24, 7], [13, 2, 2, 17, 26], [39, 31, 8, 26, 31], [23, 6, 29, 4, 12]], ![[18, 31, 28, 37, 18], [27, 36, 19, 25, 18], [26, 13, 11, 39, 27], [36, 11, 7, 8, 17], [31, 26, 18, 14, 6], [9, 5, 27, 4, 33]], ![[9, 39, 39, 37, 19], [13, 0, 10, 25, 15], [6, 36, 21, 39, 22], [32, 18, 39, 15, 25], [28, 39, 11, 24, 22], [18, 31, 28, 37, 18]], ![[0, 1], [3, 7, 12, 15, 16], [34, 36, 21, 34, 18], [37, 35, 2, 15, 37], [34, 27, 3, 18, 23], [9, 39, 39, 37, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 32, 5, 39], [], [], []]
 b := ![[], [2, 15, 40, 25, 7], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [2, 25, 9, 14, 23, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3723255100, -2447941900, -5867658994, 10921225883, -9532207506]
  a := ![1, 18, 4, 17, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-90811100, -59705900, -143113634, 266371363, -232492866]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 115856201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![312317, -155221, 17518, -8664, 30034]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![312317, -155221, 17518, -8664, 30034]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![9, 37, 3, 14, 1]] where
  M :=![![![312317, -155221, 17518, -8664, 30034], ![-180204, 89563, -10102, 5002, -17328], ![51984, -25841, 2923, -1438, 5002], ![75096, -37336, 4220, -2079, 7226], ![-21678, 10754, -1206, 607, -2079]]]
  hmulB := by decide  
  f := ![![![-1, -3, 8, -8, 2]], ![![-12, -9, 14, 14, -16]], ![![48, 65, -89, 22, 14]], ![![-36, -72, 128, -103, 30]], ![![-21, -29, 51, -19, -5]]]
  g := ![![![977, -29453, -1688, -9980, 30034], ![-564, 16993, 974, 5758, -17328], ![162, -4905, -281, -1662, 5002], ![234, -7086, -406, -2401, 7226], ![-69, 2039, 117, 691, -2079]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [27, 37, 16, 42, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 16, 9, 17], [11, 39, 24, 35], [5, 30, 10, 34], [0, 1]]
 g := ![![[34, 36, 7, 14], [34, 5, 3, 25], [20, 9, 10], [1, 1], []], ![[33, 8, 27, 4, 27, 9], [12, 37, 37, 26, 0, 11], [12, 26, 36], [13, 7, 28, 26, 36, 11], [36, 36, 31]], ![[33, 5, 23, 29, 21, 11], [18, 4, 28, 33, 26, 25], [8, 17, 24], [33, 23, 10, 5, 22, 14], [27, 24, 21]], ![[21, 2, 24, 16, 41, 26], [15, 15, 13, 12, 5, 26], [25, 34, 13], [39, 15, 7, 3, 34, 42], [14, 30, 38]]]
 h' := ![![[28, 16, 9, 17], [28, 14, 24, 33], [17, 22, 15, 5], [16, 22, 33, 28], [0, 0, 1], [0, 1]], ![[11, 39, 24, 35], [25, 39, 32, 16], [33, 32, 13, 26], [23, 20, 35, 6], [27, 11, 36, 26], [28, 16, 9, 17]], ![[5, 30, 10, 34], [12, 26, 0, 2], [10, 25, 39, 20], [21, 37, 11, 29], [37, 28, 33, 3], [11, 39, 24, 35]], ![[0, 1], [37, 7, 30, 35], [22, 7, 19, 35], [40, 7, 7, 23], [34, 4, 16, 14], [5, 30, 10, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [22, 10, 33], []]
 b := ![[], [], [36, 39, 31, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [27, 37, 16, 42, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-138337913, -216326915, 341347964, -177544285, 8739302]
  a := ![-1, 2, -4, 4, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5046317, -12550723, 7328606, -6974291, 8739302]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 3, -8, 8, -2]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![1, 3, -8, 8, -2]] 
 ![![43, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![38, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![1, 3, -8, 8, -2], ![12, 9, -14, -14, 16], ![-48, -65, 89, -22, -14], ![36, 72, -128, 103, -30], ![90, 74, -78, -113, 103]]]
  hmulB := by decide  
  f := ![![![-312317, 155221, -17518, 8664, -30034]], ![![-104757, 52064, -5876, 2906, -10074]], ![![-277210, 137773, -15549, 7690, -26658]], ![![-219642, 109162, -12320, 6093, -21122]], ![![-239181, 118873, -13416, 6635, -23001]]]
  g := ![![![2, 3, -8, 8, -2], ![7, 9, -14, -14, 16], ![-31, -65, 89, -22, -14], ![40, 72, -128, 103, -30], ![45, 74, -78, -113, 103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![312317, -155221, 17518, -8664, 30034]] ![![1, 3, -8, 8, -2]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1037, -3005, 1670, 885, 954]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![1037, -3005, 1670, 885, 954]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![17, 17, 32, 33, 1]] where
  M :=![![![1037, -3005, 1670, 885, 954], ![-5724, -4925, 3530, 2386, 1770], ![-5310, -8177, 3925, 2645, 2386], ![-4296, -7774, 1988, 1539, 1760], ![-5280, -8194, 1026, 1108, 1539]]]
  hmulB := by decide  
  f := ![![![-257, -385, 596, -271, -12]], ![![72, 435, -890, 1204, -542]], ![![1626, 1759, -2275, -619, 1204]], ![![-3648, -5358, 8224, -3479, -348]], ![![-1499, -2468, 3968, -2348, 301]]]
  g := ![![![-323, -409, -614, -651, 954], ![-762, -745, -1130, -1192, 1770], ![-976, -1037, -1541, -1619, 2386], ![-728, -802, -1156, -1203, 1760], ![-669, -731, -1026, -1057, 1539]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [27, 22, 30, 28, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 31, 26, 3], [34, 17, 26, 21], [33, 45, 42, 23], [0, 1]]
 g := ![![[7, 46, 24, 3], [9, 31, 18, 1], [0, 33, 11, 4], [19, 1], []], ![[12, 18, 11, 7, 41, 32], [25, 17, 32, 28, 31, 32], [25, 45, 30, 28, 33, 28], [29, 45, 43, 27, 22, 8], [37, 45, 9]], ![[22, 16, 9, 10, 23, 24], [23, 32, 4, 20, 10, 36], [27, 9, 35, 27, 30, 1], [37, 36, 6, 19, 37, 14], [37, 24, 18]], ![[35, 30, 28, 0, 40, 39], [0, 6, 27, 10, 8, 44], [37, 36, 30, 12, 24, 29], [40, 35, 34, 0, 35, 31], [5, 45, 12]]]
 h' := ![![[46, 31, 26, 3], [39, 46, 19, 35], [0, 18, 23, 1], [4, 25, 19, 2], [0, 0, 1], [0, 1]], ![[34, 17, 26, 21], [21, 23, 1, 29], [3, 39, 5, 18], [36, 29, 43, 42], [36, 24, 23, 9], [46, 31, 26, 3]], ![[33, 45, 42, 23], [37, 40, 6, 34], [0, 5, 5, 18], [44, 1, 29, 44], [16, 23, 27, 19], [34, 17, 26, 21]], ![[0, 1], [35, 32, 21, 43], [31, 32, 14, 10], [30, 39, 3, 6], [14, 0, 43, 19], [33, 45, 42, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [11, 26, 33], []]
 b := ![[], [], [30, 30, 36, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [27, 22, 30, 28, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-206887797, -87922948, -12341096, 548308144, -379944276]
  a := ![0, -10, 4, -20, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![133024785, 135555952, 258422888, 278435516, -379944276]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 385, -596, 271, 12]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![257, 385, -596, 271, 12]] 
 ![![47, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![31, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![257, 385, -596, 271, 12], ![-72, -435, 890, -1204, 542], ![-1626, -1759, 2275, 619, -1204], ![3648, 5358, -8224, 3479, 348], ![-1044, -3680, 7098, -8398, 3479]]]
  hmulB := by decide  
  f := ![![![-1037, 3005, -1670, -885, -954]], ![![-496, 1895, -1070, -578, -606]], ![![-571, 2156, -1185, -640, -680]], ![![-394, 1572, -824, -447, -484]], ![![-351, 1517, -768, -419, -459]]]
  g := ![![![37, 385, -596, 271, 12], ![-8, -435, 890, -1204, 542], ![-239, -1759, 2275, 619, -1204], ![526, 5358, -8224, 3479, 348], ![-135, -3680, 7098, -8398, 3479]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![1037, -3005, 1670, 885, 954]] ![![257, 385, -596, 271, 12]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, -43, 6, -4, 8]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![101, -43, 6, -4, 8]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![6, 41, 14, 26, 1]] where
  M :=![![![101, -43, 6, -4, 8], ![-48, 43, -6, 4, -8], ![24, 5, 3, -2, 4], ![12, -24, 28, -1, 2], ![-6, 12, -14, 27, -1]]]
  hmulB := by decide  
  f := ![![![1, 1, 0, 0, 0]], ![![0, 1, 2, 0, 0]], ![![0, 1, 1, 2, 0]], ![![0, 0, 0, 1, 2]], ![![0, 1, 2, 1, 1]]]
  g := ![![![1, -7, -2, -4, 8], ![0, 7, 2, 4, -8], ![0, -3, -1, -2, 4], ![0, -2, 0, -1, 2], ![0, 1, 0, 1, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [40, 15, 32, 19, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 18, 45, 10], [3, 26, 5, 18], [52, 8, 3, 25], [0, 1]]
 g := ![![[31, 46, 19, 49], [49, 15, 11], [29, 16, 49, 10], [11, 34, 1], []], ![[8, 18, 21, 30, 39, 29], [9, 10, 36], [18, 46, 9, 43, 22, 52], [17, 35, 37], [47, 27, 25, 2, 12, 46]], ![[22, 0, 18, 21, 29, 33], [13, 47, 38], [49, 23, 27, 30, 40, 23], [50, 51, 46], [44, 41, 38, 24, 52, 2]], ![[47, 37, 37, 10, 48, 11], [7, 4, 40], [4, 18, 26, 44, 49, 42], [14, 2, 28], [37, 47, 38, 9, 38, 43]]]
 h' := ![![[32, 18, 45, 10], [37, 20, 30, 7], [6, 29, 39, 45], [37, 12, 52, 13], [0, 0, 0, 1], [0, 1]], ![[3, 26, 5, 18], [5, 49, 15, 26], [10, 8, 4, 47], [24, 35, 26, 39], [42, 34, 15, 14], [32, 18, 45, 10]], ![[52, 8, 3, 25], [9, 34, 33, 29], [23, 47, 32, 41], [5, 28, 30, 49], [16, 45, 26, 29], [3, 26, 5, 18]], ![[0, 1], [44, 3, 28, 44], [35, 22, 31, 26], [32, 31, 51, 5], [3, 27, 12, 9], [52, 8, 3, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 1], []]
 b := ![[], [], [13, 20, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [40, 15, 32, 19, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30744973, -54781030, 90573629, -62195832, 13017199]
  a := ![13, 0, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2053739, -11103513, -1729569, -7559302, 13017199]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0, 0, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![1, 1, 0, 0, 0]] 
 ![![53, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![1, 1, 0, 0, 0], ![0, 1, 2, 0, 0], ![0, 1, 1, 2, 0], ![0, 0, 0, 1, 2], ![-6, -8, 10, -1, 1]]]
  hmulB := by decide  
  f := ![![![101, -43, 6, -4, 8]], ![![1, 0, 0, 0, 0]], ![![50, -21, 3, -2, 4]], ![![25, -11, 2, -1, 2]], ![![38, -16, 2, -1, 3]]]
  g := ![![![0, 1, 0, 0, 0], ![-1, 1, 2, 0, 0], ![-1, 1, 1, 2, 0], ![-1, 0, 0, 1, 2], ![-5, -8, 10, -1, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![101, -43, 6, -4, 8]] ![![1, 1, 0, 0, 0]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1795, 395, -38, 95, -78]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-1795, 395, -38, 95, -78]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![42, 55, 57, 1, 0], ![25, 12, 51, 0, 1]] where
  M :=![![![-1795, 395, -38, 95, -78], ![468, -1209, 10, 2, 190], ![-570, -521, -259, -85, 2], ![-240, 182, -516, -261, -180], ![540, 342, -718, -426, -261]]]
  hmulB := by decide  
  f := ![![![187, 283, -440, 207, 4]], ![![-24, -285, 606, -884, 414]], ![![-1242, -1365, 1785, 399, -884]], ![![-1044, -1316, 1873, -246, -462]], ![![-1009, -1160, 1563, 148, -633]]]
  g := ![![![-65, -66, -25, 95, -78], ![-74, -61, -166, 2, 190], ![50, 70, 76, -85, 2], ![258, 283, 399, -261, -180], ![423, 456, 625, -426, -261]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [56, 56, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 12, 56], [30, 46, 3], [0, 1]]
 g := ![![[45, 48, 17], [7, 12, 16], [45, 41], [21, 29, 26], [1]], ![[49, 22, 14, 10], [5, 1, 57, 38], [55, 49], [25, 54, 6, 14], [53, 38, 58, 32]], ![[46, 22, 46, 46], [16, 30, 39, 53], [11, 9], [48, 19, 42, 41], [47, 10, 33, 27]]]
 h' := ![![[17, 12, 56], [21, 25, 31], [33, 55, 4], [4, 41, 49], [3, 3, 47], [0, 1]], ![[30, 46, 3], [40, 54, 53], [23, 4, 19], [25, 8, 7], [57, 57, 29], [17, 12, 56]], ![[0, 1], [45, 39, 34], [42, 0, 36], [56, 10, 3], [1, 58, 42], [30, 46, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 48], []]
 b := ![[], [55, 7, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [56, 56, 12, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![35741, 32132, -35780, -35762, 37131]
  a := ![-1, -4, 2, -5, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![10330, 26330, 1847, -35762, 37131]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4901, -15524, 29450, -33384, 13412]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-4901, -15524, 29450, -33384, 13412]] 
 ![![59, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![43, 0, 0, 1, 0], ![42, 0, 0, 0, 1]] where
  M :=![![![-4901, -15524, 29450, -33384, 13412], ![-80472, -82747, 103072, 45488, -66768], ![200304, 278372, -416587, 136456, 45488], ![-96228, -248720, 454276, -462075, 169840], ![-509520, -500336, 600480, 369356, -462075]]]
  hmulB := by decide  
  f := ![![![185440577, -92163780, 10400702, -5144696, 17832716]], ![![61047716, -30340611, 3423960, -1693648, 5870592]], ![![113673372, -56495540, 6375557, -3153640, 10931296]], ![![135907405, -67545876, 7622594, -3770475, 13069420]], ![![131790462, -65499784, 7391700, -3656252, 12673525]]]
  g := ![![![1993, -15524, 29450, -33384, 13412], ![-21828, -82747, 103072, 45488, -66768], ![31388, 278372, -416587, 136456, 45488], ![21359, -248720, 454276, -462075, 169840], ![-145682, -500336, 600480, 369356, -462075]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-92675, 46059, -5198, 2571, -8912]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-92675, 46059, -5198, 2571, -8912]] 
 ![![59, 0, 0, 0, 0], ![43, 1, 0, 0, 0], ![49, 0, 1, 0, 0], ![46, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![-92675, 46059, -5198, 2571, -8912], ![53472, -26577, 2998, -1484, 5142], ![-15426, 7667, -867, 427, -1484], ![-22284, 11078, -1252, 617, -2144], ![6432, -3192, 358, -180, 617]]]
  hmulB := by decide  
  f := ![![![203, 187, -224, -181, 206]], ![![127, 108, -122, -143, 144]], ![![187, 190, -245, -106, 160]], ![![202, 184, -216, -189, 208]], ![![-94, -144, 222, -108, 1]]]
  g := ![![![-30712, 46059, -5198, 2571, -8912], ![17723, -26577, 2998, -1484, 5142], ![-5110, 7667, -867, 427, -1484], ![-7384, 11078, -1252, 617, -2144], ![2132, -3192, 358, -180, 617]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-1795, 395, -38, 95, -78]] ![![-4901, -15524, 29450, -33384, 13412]]
  ![![203, 187, -224, -181, 206]] where
 M := ![![![203, 187, -224, -181, 206]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![203, 187, -224, -181, 206]] ![![-92675, 46059, -5198, 2571, -8912]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47338891, -71461026, 110990182, -51808290, -1294890]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-47338891, -71461026, 110990182, -51808290, -1294890]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![4, 30, 1, 0, 0], ![2, 48, 0, 1, 0], ![52, 25, 0, 0, 1]] where
  M :=![![![-47338891, -71461026, 110990182, -51808290, -1294890], ![7769340, 74010411, -155870952, 223275254, -103616580], ![310849740, 340415514, -444072489, -104062662, 223275254], ![-673710432, -996717596, 1534727260, -667347743, -52254372], ![156763116, 639525902, -1257989456, 1560854446, -667347743]]]
  hmulB := by decide  
  f := ![![![791436497297, -393348045794, 44388658958, -21956886034, 76108429190]], ![![-456650575140, 226957722735, -25611799688, 12668888726, -43913772068]], ![![-170525081128, 84751859012, -9564106433, 4730888590, -16398533714]], ![![-330262885094, 164142381520, -18523193816, 9162505909, -31759708664]], ![![486615205964, -241850274911, 27292390304, -13500206516, 46795311309]]]
  g := ![![![-5251619, -14458956, 110990182, -51808290, -1294890], ![91356800, -55355061, -155870952, 223275254, -103616580], ![-152705708, 214356010, -444072489, -104062662, 223275254], ![-45257322, -224581712, 1534727260, -667347743, -52254372], ![602772044, -325542791, -1257989456, 1560854446, -667347743]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [40, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 60], [0, 1]]
 g := ![![[2, 36], [27], [33, 25], [58, 12], [42, 1]], ![[50, 25], [27], [46, 36], [13, 49], [23, 60]]]
 h' := ![![[42, 60], [14, 55], [22, 24], [59, 56], [28, 16], [0, 1]], ![[0, 1], [6, 6], [54, 37], [32, 5], [29, 45], [42, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [43, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [40, 19, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1028, -945, 822, 1623, -1288]
  a := ![3, -4, 7, -8, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![974, -1169, 822, 1623, -1288]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, -6, 3, 2]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![1, 1, -6, 3, 2]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![14, 20, 1, 0, 0], ![25, 4, 0, 1, 0], ![5, 24, 0, 0, 1]] where
  M :=![![![1, 1, -6, 3, 2], ![-12, -21, 22, -14, 6], ![-18, -19, 9, 19, -14], ![48, 62, -100, 23, 16], ![-48, -90, 142, -108, 23]]]
  hmulB := by decide  
  f := ![![![6865, -3413, 384, -191, 660]], ![![-3960, 1969, -226, 108, -382]], ![![296, -147, 15, -9, 28]], ![![2581, -1283, 144, -72, 248]], ![![-1003, 499, -58, 27, -97]]]
  g := ![![![0, 1, -6, 3, 2], ![0, -9, 22, -14, 6], ![-9, 1, 9, 19, -14], ![13, 26, -100, 23, 16], ![9, -50, 142, -108, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [37, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 60], [0, 1]]
 g := ![![[29, 16], [25], [41, 15], [35, 57], [25, 1]], ![[2, 45], [25], [50, 46], [57, 4], [50, 60]]]
 h' := ![![[25, 60], [54, 57], [8, 56], [47, 25], [51, 39], [0, 1]], ![[0, 1], [15, 4], [5, 5], [1, 36], [50, 22], [25, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [31, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [37, 36, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-712, -991, 1302, -79, -99]
  a := ![1, 0, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-270, -399, 1302, -79, -99]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![48685429, 67023338, -99846532, 30969656, 12118334]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![48685429, 67023338, -99846532, 30969656, 12118334]] 
 ![![61, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![58, 0, 0, 0, 1]] where
  M :=![![![48685429, 67023338, -99846532, 30969656, 12118334], ![-72710004, -148107775, 255230016, -211811398, 61939312], ![-185817936, -156497242, 161588785, 224260360, -211811398], ![671789196, 909184904, -1343169240, 373400183, 193290704], ![-579872112, -1108852838, 1875638424, -1439814592, 373400183]]]
  hmulB := by decide  
  f := ![![![234856814795137, -116725057056062, 13172225125972, -6515650917140, 22584987792694]], ![![82480983585850, -40993477338587, 4626044534200, -2288276356030, 7931777534508]], ![![8341107132674, -4145573577798, 467820961641, -231407985284, 802121935158]], ![![108728973610888, -54038864741656, 6098194422664, -3016476389033, 10455913505648]], ![![223039378051978, -110851729601970, 12509430063616, -6187798848580, 21448564884019]]]
  g := ![![![-45838503, 67023338, -99846532, 30969656, 12118334], ![82187542, -148107775, 255230016, -211811398, 61939312], ![146552702, -156497242, 161588785, 224260360, -211811398], ![-628032888, 909184904, -1343169240, 373400183, 193290704], ![634773958, -1108852838, 1875638424, -1439814592, 373400183]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-47338891, -71461026, 110990182, -51808290, -1294890]] ![![1, 1, -6, 3, 2]]
  ![![-3612273055, -3751044683, 4707757032, 1915508599, -2936021596]] where
 M := ![![![-3612273055, -3751044683, 4707757032, 1915508599, -2936021596]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![-3612273055, -3751044683, 4707757032, 1915508599, -2936021596]] ![![48685429, 67023338, -99846532, 30969656, 12118334]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![2211422741084994341, 4573868673343925935, -7915752666687623012, 6680984448916731723, -1999329452337807574]]]
 hmul := by decide  
 g := ![![![![36252831821065481, 74981453661375835, -129766437158813492, 109524335228143143, -32775892661275534]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)


lemma PB752I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB752I1 : PrimesBelowBoundCertificateInterval O 23 61 752 where
  m := 9
  g := ![3, 1, 2, 1, 2, 2, 2, 3, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB752I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0]
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1, I61N2]
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
    · exact ![28629151]
    · exact ![1874161, 37]
    · exact ![115856201]
    · exact ![3418801, 43]
    · exact ![4879681, 47]
    · exact ![7890481, 53]
    · exact ![205379, 59, 59]
    · exact ![3721, 3721, 61]
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
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
  β := ![I29N1, I29N2, I37N1, I43N1, I47N1, I53N1, I59N1, I59N2, I61N2]
  Il := ![[I29N1, I29N2], [], [I37N1], [], [I43N1], [I47N1], [I53N1], [I59N1, I59N2], [I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
