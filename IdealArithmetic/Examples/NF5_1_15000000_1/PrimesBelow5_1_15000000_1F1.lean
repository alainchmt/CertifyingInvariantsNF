
import IdealArithmetic.Examples.NF5_1_15000000_1.RI5_1_15000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, -22, 2, 40, -18]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![79, -22, 2, 40, -18]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![24, 25, 25, 1, 0], ![28, 2, 20, 0, 1]] where
  M :=![![![79, -22, 2, 40, -18], ![162, 135, -112, -126, 120], ![-1080, -310, 397, 164, -378], ![1350, 234, -374, -19, 282], ![-306, 96, 0, -162, 43]]]
  hmulB := by decide  
  f := ![![![-12421, 1602, 1954, 1528, -2514]], ![![22626, -2925, -3560, -2782, 4584]], ![![-41256, 5314, 6489, 5076, -8346]], ![![-25176, 3235, 3959, 3099, -5088]], ![![-39290, 5062, 6180, 4834, -7949]]]
  g := ![![![-13, -34, -22, 40, -18], ![-6, 105, 22, -126, 120], ![192, -126, 133, 164, -378], ![-210, 5, -191, -19, 282], ![82, 140, 110, -162, 43]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [16, 11, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 9, 5], [3, 19, 24], [0, 1]]
 g := ![![[7, 25, 6], [23, 7], [14, 15, 20], [1]], ![[21, 25, 22, 25], [19, 6], [12, 25, 15, 28], [7, 28, 13, 9]], ![[2, 20, 5, 13], [14, 4], [8, 27, 2, 9], [10, 6, 28, 20]]]
 h' := ![![[4, 9, 5], [15, 8, 8], [8, 7, 23], [13, 18, 7], [0, 1]], ![[3, 19, 24], [11, 25, 18], [5, 4, 8], [10, 23, 20], [4, 9, 5]], ![[0, 1], [1, 25, 3], [14, 18, 27], [12, 17, 2], [3, 19, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 12], []]
 b := ![[], [1, 28, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [16, 11, 22, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9854905, 6071650, -794064, -2638631, -3516509]
  a := ![0, -8, -7, -7, -37]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5918769, 2726567, 4672479, -2638631, -3516509]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12421, -1602, -1954, -1528, 2514]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![12421, -1602, -1954, -1528, 2514]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![12, 18, 1, 0, 0], ![27, 22, 0, 1, 0], ![21, 4, 0, 0, 1]] where
  M :=![![![12421, -1602, -1954, -1528, 2514], ![-22626, 2925, 3560, 2782, -4584], ![41256, -5314, -6489, -5076, 8346], ![-33750, 4358, 5310, 4151, -6834], ![11754, -1512, -1848, -1446, 2377]]]
  hmulB := by decide  
  f := ![![![-79, 22, -2, -40, 18]], ![![-162, -135, 112, 126, -120]], ![![-96, -64, 55, 56, -54]], ![![-243, -90, 96, 59, -84]], ![![-69, -6, 14, -6, -5]]]
  g := ![![![839, 1970, -1954, -1528, 2514], ![-1524, -3587, 3560, 2782, -4584], ![2790, 6544, -6489, -5076, 8346], ![-2277, -5352, 5310, 4151, -6834], ![795, 1864, -1848, -1446, 2377]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [14, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 28], [0, 1]]
 g := ![![[23, 1], [1], [27, 25], [26, 1]], ![[20, 28], [1], [10, 4], [23, 28]]]
 h' := ![![[26, 28], [16, 28], [28, 28], [13, 24], [0, 1]], ![[0, 1], [19, 1], [2, 1], [28, 5], [26, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [5, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [14, 3, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1585978, -900060, 394828, 666486, 491142]
  a := ![3, -61, -63, -66, -235]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1194242, -849456, 394828, 666486, 491142]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![79, -22, 2, 40, -18]] ![![12421, -1602, -1954, -1528, 2514]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![-29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24887, -5241, 7585, 1474, -6180]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-24887, -5241, 7585, 1474, -6180]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![22, 3, 15, 21, 1]] where
  M :=![![![-24887, -5241, 7585, 1474, -6180], ![55620, 1238, -10085, 8852, 4422], ![-39798, 32269, -14518, -44778, 26556], ![-53757, -49940, 41700, 47964, -47967], ![94797, 21411, -29841, -7293, 24838]]]
  hmulB := by decide  
  f := ![![![-173, 217, 41, -22, -168]], ![![1512, 372, -183, -296, -66]], ![![594, 1527, 104, -338, -888]], ![![1323, -16, -154, -150, 207]], ![![1222, 940, -40, -313, -425]]]
  g := ![![![3583, 429, 3235, 4234, -6180], ![-1344, -388, -2465, -2710, 4422], ![-20130, -1529, -13318, -19434, 26556], ![32307, 3031, 24555, 34041, -47967], ![-14569, -1713, -12981, -17061, 24838]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 4 2 4 [3, 7, 27, 7, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 28, 16, 11], [27, 20, 19, 18], [23, 13, 27, 2], [0, 1]]
 g := ![![[19, 27, 6, 7], [12, 7], [28, 22, 24, 1], []], ![[17, 4, 17, 11, 12, 6], [6, 25, 11, 24, 27, 26], [19, 10, 3, 17, 12, 26], [20, 20, 24, 15, 25, 29]], ![[27, 16, 29, 27, 24, 2], [23, 2, 21, 21, 20, 5], [1, 4, 25, 8, 28, 4], [5, 3, 3, 18, 26, 4]], ![[19, 18, 11, 18, 2, 18], [24, 20, 29, 23, 3, 4], [29, 0, 21, 1, 17, 18], [5, 23, 30, 20, 20, 8]]]
 h' := ![![[5, 28, 16, 11], [26, 7, 26, 10], [9, 17, 10], [0, 0, 0, 1], [0, 1]], ![[27, 20, 19, 18], [20, 19, 24, 3], [19, 18, 18, 15], [3, 9, 25, 15], [5, 28, 16, 11]], ![[23, 13, 27, 2], [6, 24, 5, 21], [19, 13, 26, 8], [14, 17, 8, 18], [27, 20, 19, 18]], ![[0, 1], [12, 12, 7, 28], [6, 14, 8, 8], [0, 5, 29, 28], [23, 13, 27, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 23, 29], []]
 b := ![[], [], [15, 13, 30, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 4
  hpos := by decide
  P := [3, 7, 27, 7, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-603370089, -415274778, 20419734, 137136992, 160167942]
  a := ![1, -6, -6, -7, -24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-133131123, -28896084, -76841916, -104077090, 160167942]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 923521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, -217, -41, 22, 168]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![173, -217, -41, 22, 168]] 
 ![![31, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![173, -217, -41, 22, 168], ![-1512, -372, 183, 296, 66], ![-594, -1527, -104, 338, 888], ![-1323, 16, 154, 150, -207], ![-459, -681, -81, 111, 308]]]
  hmulB := by decide  
  f := ![![![24887, 5241, -7585, -1474, 6180]], ![![22290, 5032, -7015, -1712, 5838]], ![![25368, 4031, -6872, 18, 5124]], ![![14579, 4316, -5260, -2308, 4737]], ![![17815, 3705, -5399, -1001, 4382]]]
  g := ![![![103, -217, -41, 22, 168], ![-74, -372, 183, 296, 66], ![640, -1527, -104, 338, 888], ![-111, 16, 154, 150, -207], ![407, -681, -81, 111, 308]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-24887, -5241, 7585, 1474, -6180]] ![![173, -217, -41, 22, 168]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-270133, 34872, 42498, 33224, -54696]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-270133, 34872, 42498, 33224, -54696]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![33, 15, 20, 1, 0], ![30, 10, 16, 0, 1]] where
  M :=![![![-270133, 34872, 42498, 33224, -54696], ![492264, -63547, -77444, -60544, 99672], ![-897048, 115804, 141125, 110328, -181632], ![734130, -94772, -115494, -90291, 148644], ![-255528, 32988, 40200, 31428, -51739]]]
  hmulB := by decide  
  f := ![![![-49, -32, 10, 24, 24]], ![![-216, -111, 36, 64, 72]], ![![-648, -396, 113, 232, 192]], ![![-483, -289, 84, 173, 156]], ![![-390, -234, 68, 140, 125]]]
  g := ![![![7415, 2256, 6842, 33224, -54696], ![-13512, -4111, -12468, -60544, 99672], ![24624, 7492, 22721, 110328, -181632], ![-20151, -6131, -18594, -90291, 148644], ![7014, 2134, 6472, 31428, -51739]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [4, 18, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 14, 34], [3, 22, 3], [0, 1]]
 g := ![![[14, 29, 11], [11, 26], [0, 34, 34], [21, 1], []], ![[19, 1, 4, 3], [24, 25], [26, 36, 20, 27], [25, 3], [31, 9]], ![[33, 6, 7, 7], [0, 25], [7, 0, 29, 27], [13, 11], [25, 9]]]
 h' := ![![[18, 14, 34], [30, 31, 23], [0, 1, 10], [27, 25, 16], [0, 0, 1], [0, 1]], ![[3, 22, 3], [8, 29, 6], [20, 2, 32], [14, 20, 18], [15, 21, 22], [18, 14, 34]], ![[0, 1], [28, 14, 8], [18, 34, 32], [15, 29, 3], [20, 16, 14], [3, 22, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 23], []]
 b := ![[], [22, 13, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [4, 18, 16, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-363230568, -217939160, 34988532, 98482048, 125308040]
  a := ![1, 26, 22, 17, 121]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-199253496, -79682440, -106475164, 98482048, 125308040]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, -32, 10, 24, 24]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-49, -32, 10, 24, 24]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![21, 33, 1, 0, 0], ![29, 22, 0, 1, 0], ![8, 3, 0, 0, 1]] where
  M :=![![![-49, -32, 10, 24, 24], ![-216, -111, 36, 64, 72], ![-648, -396, 113, 232, 192], ![-54, -52, -22, 9, 60], ![-432, -252, 48, 108, 113]]]
  hmulB := by decide  
  f := ![![![-270133, 34872, 42498, 33224, -54696]], ![![492264, -63547, -77444, -60544, 99672]], ![![261483, -33755, -41137, -32160, 52944]], ![![100813, -13014, -15860, -12399, 20412]], ![![-25400, 3279, 3996, 3124, -5143]]]
  g := ![![![-31, -26, 10, 24, 24], ![-92, -79, 36, 64, 72], ![-305, -265, 113, 232, 192], ![-9, 8, -22, 9, 60], ![-148, -123, 48, 108, 113]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P1 : CertificateIrreducibleZModOfList' 37 2 2 5 [6, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 36], [0, 1]]
 g := ![![[14, 33], [10], [30, 27], [26], [1]], ![[17, 4], [10], [19, 10], [26], [1]]]
 h' := ![![[27, 36], [2, 12], [5, 26], [28, 8], [31, 27], [0, 1]], ![[0, 1], [30, 25], [4, 11], [22, 29], [20, 10], [27, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [32, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N1 : CertifiedPrimeIdeal' SI37N1 37 where
  n := 2
  hpos := by decide
  P := [6, 10, 1]
  hirr := P37P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16203, -21331, 6000, 16882, 6909]
  a := ![-1, -6, 1, 10, -51]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18569, -16526, 6000, 16882, 6909]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N1 B_one_repr
lemma NI37N1 : Nat.card (O ⧸ I37N1) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-270133, 34872, 42498, 33224, -54696]] ![![-49, -32, 10, 24, 24]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1954, 1359, -49, -441, -555]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![1954, 1359, -49, -441, -555]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![23, 37, 19, 7, 1]] where
  M :=![![![1954, 1359, -49, -441, -555], ![4995, 3570, 37, -979, -1323], ![11907, 9001, 654, -1863, -2937], ![-594, -50, 504, 559, 402], ![2367, 2535, 1089, 453, -152]]]
  hmulB := by decide  
  f := ![![![50, 41, -35, -37, 39]], ![![-351, -102, 125, 51, -111]], ![![999, 107, -236, 65, 153]], ![![-756, 48, 94, -199, 0]], ![![41, -15, 3, 25, -11]]]
  g := ![![![359, 534, 256, 84, -555], ![864, 1281, 614, 202, -1323], ![1938, 2870, 1377, 456, -2937], ![-240, -364, -174, -55, 402], ![143, 199, 97, 37, -152]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 4 2 5 [16, 23, 31, 30, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 40, 27, 30], [21, 9, 23, 31], [33, 32, 32, 21], [0, 1]]
 g := ![![[36, 13, 23, 16], [32, 29, 33], [24, 5, 23], [11, 1], []], ![[9, 20, 38, 10, 16, 14], [29, 22, 2], [35, 7, 33], [12, 11, 33, 28, 15, 34], [23, 40, 39]], ![[21, 37, 13, 32], [1, 2, 25], [8, 13, 40], [23, 9, 33, 7, 9, 40], [25, 25, 18]], ![[23, 30, 35, 31, 16, 2], [3, 38, 9], [20, 14, 37], [24, 21, 35, 33, 23, 10], [16, 4, 31]]]
 h' := ![![[39, 40, 27, 30], [16, 13, 14, 37], [6, 2, 2, 19], [29, 18, 5, 8], [0, 0, 1], [0, 1]], ![[21, 9, 23, 31], [26, 12, 14, 6], [30, 37, 0, 24], [4, 27, 23, 19], [5, 24, 14, 33], [39, 40, 27, 30]], ![[33, 32, 32, 21], [0, 32, 28], [37, 25, 15, 36], [1, 24, 26, 32], [0, 18, 24, 23], [21, 9, 23, 31]], ![[0, 1], [35, 25, 26, 39], [40, 18, 24, 3], [27, 13, 28, 23], [13, 40, 2, 26], [33, 32, 32, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [18, 25, 3], []]
 b := ![[], [], [0, 12, 29, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 4
  hpos := by decide
  P := [16, 23, 31, 30, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4379967448, 1092509774, -1450597294, -494565052, 1258232130]
  a := ![0, -2, -14, -36, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-599009062, -1108831196, -618463604, -226882682, 1258232130]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 2825761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-50, -41, 35, 37, -39]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-50, -41, 35, 37, -39]] 
 ![![41, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-50, -41, 35, 37, -39], ![351, 102, -125, -51, 111], ![-999, -107, 236, -65, -153], ![756, -48, -94, 199, 0], ![171, 153, -129, -147, 148]]]
  hmulB := by decide  
  f := ![![![-1954, -1359, 49, 441, 555]], ![![-1075, -750, 23, 239, 303]], ![![-767, -551, -4, 153, 207]], ![![-1034, -728, 14, 223, 288]], ![![-439, -327, -17, 75, 112]]]
  g := ![![![-2, -41, 35, 37, -39], ![-5, 102, -125, -51, 111], ![35, -107, 236, -65, -153], ![-42, -48, -94, 199, 0], ![11, 153, -129, -147, 148]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![1954, 1359, -49, -441, -555]] ![![-50, -41, 35, 37, -39]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 5 2 5 [14, 2, 37, 4, 16, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 40, 27, 13, 3], [24, 6, 35, 10, 2], [5, 36, 36, 30, 15], [39, 3, 31, 33, 23], [0, 1]]
 g := ![![[6, 0, 39, 7, 41], [9, 13, 42, 40, 10], [12, 24, 31, 41], [1], []], ![[28, 37, 2, 30, 21, 17, 42, 37], [37, 12, 23, 9, 11, 21, 27, 7], [7, 36, 2, 9], [10, 32, 3, 14, 35, 1, 2, 8], [26, 18, 20, 9]], ![[19, 9, 24, 17, 36, 12, 4, 33], [3, 32, 16, 35, 34, 27, 17, 12], [24, 1, 26, 10], [20, 1, 41, 41, 3, 2, 35, 32], [17, 6, 19, 4]], ![[10, 38, 5, 20, 18, 25, 33, 40], [32, 20, 19, 17, 32, 12, 37, 40], [0, 25, 27, 24], [20, 4, 35, 36, 25, 29, 37, 23], [27, 33, 9, 10]], ![[29, 26, 14, 39, 39, 10, 9, 24], [8, 25, 24, 18, 2, 19, 7, 15], [30, 40, 18, 14], [40, 27, 14, 17, 33, 6, 1, 35], [15, 36, 20, 13]]]
 h' := ![![[2, 40, 27, 13, 3], [3, 25, 3, 29, 27], [28, 40, 28, 21, 15], [29, 41, 6, 39, 27], [0, 0, 1], [0, 1]], ![[24, 6, 35, 10, 2], [6, 0, 3, 20, 27], [41, 22, 28, 38, 26], [28, 25, 28, 33, 40], [27, 28, 0, 29, 19], [2, 40, 27, 13, 3]], ![[5, 36, 36, 30, 15], [17, 29, 34, 9, 9], [31, 30, 0, 30, 36], [25, 7, 37, 32, 15], [37, 41, 35, 0, 4], [24, 6, 35, 10, 2]], ![[39, 3, 31, 33, 23], [15, 40, 30, 7, 19], [16, 5, 3, 20, 24], [39, 4, 18, 7, 14], [34, 16, 35, 29, 23], [5, 36, 36, 30, 15]], ![[0, 1], [7, 35, 16, 21, 4], [14, 32, 27, 20, 28], [41, 9, 40, 18, 33], [21, 1, 15, 28, 40], [39, 3, 31, 33, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 18, 26, 27], [], [], []]
 b := ![[], [41, 14, 25, 1, 34], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 5
  hpos := by decide
  P := [14, 2, 37, 4, 16, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![89694984797, -19109136274, 14965444972, 75547722153, 32852690279]
  a := ![13, -6, -1, 5, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2085929879, -444398518, 348033604, 1756923771, 764016053]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 147008443 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49454, 6385, 7781, 6083, -10013]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-49454, 6385, 7781, 6083, -10013]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![5, 27, 34, 37, 1]] where
  M :=![![![-49454, 6385, 7781, 6083, -10013], ![90117, -11634, -14175, -11081, 18249], ![-164241, 21195, 25844, 20209, -33243], ![134388, -17356, -21142, -16527, 27216], ![-46803, 6027, 7365, 5763, -9464]]]
  hmulB := by decide  
  f := ![![![14, 9, -7, -7, 7]], ![![-63, -14, 23, 7, -21]], ![![189, 23, -38, 15, 21]], ![![-126, 14, 12, -39, 6]], ![![2, 20, -5, -16, 8]]]
  g := ![![![13, 5888, 7409, 8012, -10013], ![-24, -10731, -13503, -14602, 18249], ![42, 19548, 24598, 26600, -33243], ![-36, -16004, -20138, -21777, 27216], ![11, 5565, 7003, 7573, -9464]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [40, 42, 45, 45, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 10, 20, 44], [16, 22, 12, 9], [16, 14, 15, 41], [0, 1]]
 g := ![![[36, 39, 2, 14], [32, 35, 29, 8], [4, 12, 39, 36], [2, 1], []], ![[14, 5, 32, 25, 2, 31], [26, 46, 33, 23, 25, 38], [9, 33, 43, 36, 24, 10], [41, 1, 29, 18, 31, 11], [13, 39, 9]], ![[32, 26, 36, 16, 42, 18], [31, 33, 14, 3, 26, 8], [13, 4, 44, 38, 34, 21], [15, 32, 18, 46, 38, 37], [1, 2, 34]], ![[35, 6, 33, 46, 22, 15], [17, 15, 27, 11, 15, 31], [25, 8, 18, 44, 14, 23], [37, 33, 40, 11, 9, 30], [7, 33, 36]]]
 h' := ![![[17, 10, 20, 44], [36, 14, 40, 22], [28, 18, 18, 33], [14, 17, 9, 6], [0, 0, 1], [0, 1]], ![[16, 22, 12, 9], [3, 43, 5, 16], [18, 17, 27, 12], [42, 37, 24, 13], [4, 20, 30, 24], [17, 10, 20, 44]], ![[16, 14, 15, 41], [9, 40, 27, 40], [9, 37, 25, 11], [6, 23, 18, 26], [28, 18, 37, 5], [16, 22, 12, 9]], ![[0, 1], [39, 44, 22, 16], [29, 22, 24, 38], [28, 17, 43, 2], [23, 9, 26, 18], [16, 14, 15, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 20, 38], []]
 b := ![[], [], [9, 5, 31, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [40, 42, 45, 45, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1685312, 447590, -675692, -360556, 617502]
  a := ![-1, 0, -2, -5, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-29834, -345212, -461080, -493790, 617502]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14, -9, 7, 7, -7]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-14, -9, 7, 7, -7]] 
 ![![47, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![-14, -9, 7, 7, -7], ![63, 14, -23, -7, 21], ![-189, -23, 38, -15, -21], ![126, -14, -12, 39, -6], ![39, 27, -27, -27, 28]]]
  hmulB := by decide  
  f := ![![![49454, -6385, -7781, -6083, 10013]], ![![29649, -3828, -4665, -3647, 6003]], ![![45583, -5885, -7172, -5607, 9229]], ![![23446, -3027, -3689, -2884, 4747]], ![![16779, -2166, -2640, -2064, 3397]]]
  g := ![![![-2, -9, 7, 7, -7], ![9, 14, -23, -7, 21], ![-7, -23, 38, -15, -21], ![3, -14, -12, 39, -6], ![12, 27, -27, -27, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-49454, 6385, 7781, 6083, -10013]] ![![-14, -9, 7, 7, -7]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55, 6, 8, 6, -12]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-55, 6, 8, 6, -12]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![38, 23, 39, 1, 0], ![28, 11, 10, 0, 1]] where
  M :=![![![-55, 6, 8, 6, -12], ![108, -11, -20, -16, 18], ![-162, 34, 19, 6, -48], ![162, -14, -24, -19, 24], ![-18, 24, 0, -6, -19]]]
  hmulB := by decide  
  f := ![![![1, -2, 0, 2, 0]], ![![0, 1, -4, -4, 6]], ![![-54, -22, 15, 10, -12]], ![![-38, -17, 9, 7, -6]], ![![-10, -5, 2, 2, -1]]]
  g := ![![![1, 0, -2, 6, -12], ![4, 3, 8, -16, 18], ![18, 8, 5, 6, -48], ![4, 3, 9, -19, 24], ![14, 7, 8, -6, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [10, 48, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 11, 43], [2, 41, 10], [0, 1]]
 g := ![![[43, 46, 1], [], [11, 39, 6], [2, 16], [1]], ![[17, 50, 15, 16], [37, 6], [9, 35, 2, 15], [51, 4], [7, 14, 39, 7]], ![[19, 6, 11, 1], [4, 6], [49, 22, 3, 43], [50, 36], [29, 40, 32, 46]]]
 h' := ![![[47, 11, 43], [16, 28, 52], [49, 23], [27, 15, 18], [43, 5, 49], [0, 1]], ![[2, 41, 10], [25, 35, 50], [17, 41, 35], [37, 44, 5], [32, 23, 51], [47, 11, 43]], ![[0, 1], [28, 43, 4], [42, 42, 18], [1, 47, 30], [36, 25, 6], [2, 41, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 26], []]
 b := ![[], [41, 16, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [10, 48, 4, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-34971128, -18773663, 3110153, 7162583, 10845444]
  a := ![3, 10, 6, -2, 63]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11524938, -5713452, -7258208, 7162583, 10845444]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26, 13, -5, -7, -5]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![26, 13, -5, -7, -5]] 
 ![![53, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![52, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![26, 13, -5, -7, -5], ![45, 36, -5, -21, -21], ![189, 103, -16, -41, -63], ![36, 30, -10, -17, 6], ![69, 57, 3, -21, -34]]]
  hmulB := by decide  
  f := ![![![198898, -25677, -31291, -24463, 40273]], ![![86981, -11229, -13684, -10698, 17612]], ![![53743, -6938, -8455, -6610, 10882]], ![![184946, -23876, -29096, -22747, 37448]], ![![112381, -14508, -17680, -13822, 22755]]]
  g := ![![![5, 13, -5, -7, -5], ![17, 36, -5, -21, -21], ![33, 103, -16, -41, -63], ![2, 30, -10, -17, 6], ![13, 57, 3, -21, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2968, 383, 467, 365, -601]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![-2968, 383, 467, 365, -601]] 
 ![![53, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![-2968, 383, 467, 365, -601], ![5409, -698, -851, -665, 1095], ![-9855, 1273, 1550, 1211, -1995], ![8064, -1042, -1268, -991, 1632], ![-2805, 363, 441, 345, -568]]]
  hmulB := by decide  
  f := ![![![-260, -179, 21, 81, 89]], ![![-177, -121, 14, 54, 60]], ![![-159, -109, 12, 47, 51]], ![![-34, -25, 1, 10, 13]], ![![-135, -93, 9, 39, 44]]]
  g := ![![![-282, 383, 467, 365, -601], ![514, -698, -851, -665, 1095], ![-937, 1273, 1550, 1211, -1995], ![767, -1042, -1268, -991, 1632], ![-267, 363, 441, 345, -568]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-55, 6, 8, 6, -12]] ![![26, 13, -5, -7, -5]]
  ![![-260, -179, 21, 81, 89]] where
 M := ![![![-260, -179, 21, 81, 89]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![-260, -179, 21, 81, 89]] ![![-2968, 383, 467, 365, -601]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
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


def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [20, 45, 20, 28, 20, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 25, 56, 35, 45], [22, 22, 31, 28, 7], [42, 10, 17, 9, 30], [46, 1, 14, 46, 36], [0, 1]]
 g := ![![[36, 11, 21], [18, 13, 27, 40, 53], [11, 57, 47, 9], [18, 39, 1], []], ![[58, 38, 37, 33, 22, 6, 21, 16], [27, 54, 22, 8, 14, 20, 4, 22], [5, 32, 46, 25], [58, 2, 9, 48, 10, 32, 54, 49], [23, 21, 39, 31, 6, 38, 58, 29]], ![[14, 55, 24, 28, 34, 47, 7, 1], [40, 37, 39, 9, 8, 53, 34, 45], [47, 25, 27, 25], [4, 12, 2, 0, 1, 36, 42, 7], [25, 53, 42, 1, 11, 40, 29, 48]], ![[35, 53, 2, 12, 39, 18, 25, 47], [38, 40, 6, 44, 45, 52, 18, 32], [58, 58, 55, 21], [20, 6, 14, 34, 10, 43, 41, 58], [38, 16, 14, 12, 41, 31, 19, 37]], ![[1, 13, 56, 2, 45, 45, 37, 53], [33, 12, 46, 2, 17, 12, 54, 53], [24, 2, 25, 45], [55, 5, 52, 0, 42, 9, 53, 1], [58, 2, 32, 29, 50, 31, 43, 46]]]
 h' := ![![[47, 25, 56, 35, 45], [53, 41, 20, 27], [52, 40, 15, 44, 42], [53, 3, 48, 28, 3], [0, 0, 0, 1], [0, 1]], ![[22, 22, 31, 28, 7], [52, 28, 54, 10, 49], [7, 4, 31, 48, 52], [15, 27, 43, 28, 54], [54, 23, 38, 20, 12], [47, 25, 56, 35, 45]], ![[42, 10, 17, 9, 30], [16, 29, 15, 27, 28], [32, 39, 49, 17, 23], [38, 52, 4, 35, 5], [0, 23, 12, 11, 1], [22, 22, 31, 28, 7]], ![[46, 1, 14, 46, 36], [18, 6, 52, 33, 34], [10, 24, 51, 25, 8], [52, 24, 31, 36, 32], [50, 32, 32, 6, 36], [42, 10, 17, 9, 30]], ![[0, 1], [11, 14, 36, 21, 7], [27, 11, 31, 43, 52], [25, 12, 51, 50, 24], [6, 40, 36, 21, 10], [46, 1, 14, 46, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 30, 47, 15], [], [], []]
 b := ![[], [56, 19, 30, 38, 39], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 5
  hpos := by decide
  P := [20, 45, 20, 28, 20, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27265587931, -8622453284, -1585977584, -7618494357, -3997834513]
  a := ![1, 4, 0, -5, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-462128609, -146143276, -26880976, -129127023, -67759907]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-235, -75, 89, 44, -82]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-235, -75, 89, 44, -82]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![35, 51, 60, 1, 0], ![9, 32, 14, 0, 1]] where
  M :=![![![-235, -75, 89, 44, -82], ![738, 100, -187, 22, 132], ![-1188, 155, 100, -396, 66], ![261, -424, 234, 540, -363], ![867, 297, -339, -183, 320]]]
  hmulB := by decide  
  f := ![![![653, -79, -101, -80, 130]], ![![-1170, 162, 189, 146, -240]], ![![2160, -261, -326, -256, 438]], ![![1492, -163, -216, -172, 299]], ![![-12, 12, 8, 5, -4]]]
  g := ![![![-17, 5, -23, 44, -82], ![-20, -86, -55, 22, 132], ![198, 299, 376, -396, 66], ![-252, -268, -444, 540, -363], ![72, -10, 101, -183, 320]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [12, 15, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 40, 17], [58, 20, 44], [0, 1]]
 g := ![![[58, 55, 5], [53, 47], [46, 46, 34], [41, 55, 52], [1]], ![[45, 51, 13, 44], [1, 15], [8, 18, 56, 54], [5, 34, 9, 54], [10, 43, 23, 33]], ![[20, 21, 51, 18], [18, 22], [3, 42, 37, 24], [48, 18, 7, 17], [46, 35, 25, 28]]]
 h' := ![![[36, 40, 17], [44, 19, 26], [58, 55, 13], [57, 28, 20], [49, 46, 33], [0, 1]], ![[58, 20, 44], [52, 30, 50], [53, 5, 36], [57, 47, 22], [54, 36, 39], [36, 40, 17]], ![[0, 1], [15, 12, 46], [29, 1, 12], [18, 47, 19], [31, 40, 50], [58, 20, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 2], []]
 b := ![[], [48, 45, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [12, 15, 28, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![60416, 1930, -1318, 16672, -6354]
  a := ![4, -1, 0, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7638, -10574, -14962, 16672, -6354]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![40, 14, -16, -9, 15]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![40, 14, -16, -9, 15]] 
 ![![61, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![55, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![40, 14, -16, -9, 15], ![-135, -21, 36, -1, -27], ![243, -18, -29, 65, -3], ![-81, 70, -32, -96, 57], ![-144, -54, 60, 36, -59]]]
  hmulB := by decide  
  f := ![![![13324, -1740, -2100, -1637, 2709]], ![![2003, -263, -316, -246, 408]], ![![943, -124, -149, -116, 192]], ![![11419, -1492, -1800, -1403, 2322]], ![![13094, -1710, -2064, -1609, 2662]]]
  g := ![![![-8, 14, -16, -9, 15], ![28, -21, 36, -1, -27], ![-48, -18, -29, 65, -3], ![18, 70, -32, -96, 57], ![31, -54, 60, 36, -59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -5, 3, 6, -4]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![1, -5, 3, 6, -4]] 
 ![![61, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![1, -5, 3, 6, -4], ![36, 16, -17, -12, 18], ![-162, -35, 48, 10, -36], ![153, 12, -34, 14, 21], ![-15, 15, -9, -21, 16]]]
  hmulB := by decide  
  f := ![![![-3047, 415, 481, 370, -632]], ![![-2704, 370, 427, 328, -562]], ![![-1962, 269, 310, 238, -408]], ![![-512, 71, 81, 62, -107]], ![![-1145, 157, 181, 139, -238]]]
  g := ![![![3, -5, 3, 6, -4], ![-8, 16, -17, -12, 18], ![12, -35, 48, 10, -36], ![1, 12, -34, 14, 21], ![-10, 15, -9, -21, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-235, -75, 89, 44, -82]] ![![40, 14, -16, -9, 15]]
  ![![30596, 4191, -7849, 799, 5579]] where
 M := ![![![30596, 4191, -7849, 799, 5579]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![30596, 4191, -7849, 799, 5579]] ![![1, -5, 3, 6, -4]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![1491572, 282064, -433588, -51179, 341661]]]
 hmul := by decide  
 g := ![![![![24452, 4624, -7108, -839, 5601]]]]
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


lemma PB242I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB242I1 : PrimesBelowBoundCertificateInterval O 23 61 242 where
  m := 9
  g := ![2, 2, 2, 2, 1, 2, 3, 1, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB242I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0]
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
    · exact ![24389, 841]
    · exact ![923521, 31]
    · exact ![50653, 1369]
    · exact ![2825761, 41]
    · exact ![147008443]
    · exact ![4879681, 47]
    · exact ![148877, 53, 53]
    · exact ![714924299]
    · exact ![226981, 61, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
  β := ![I31N1, I41N1, I47N1, I53N1, I53N2, I61N1, I61N2]
  Il := ![[], [I31N1], [], [I41N1], [], [I47N1], [I53N1, I53N2], [], [I61N1, I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
