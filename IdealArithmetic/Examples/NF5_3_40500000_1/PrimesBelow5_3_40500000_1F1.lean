
import IdealArithmetic.Examples.NF5_3_40500000_1.RI5_3_40500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4514, -989, -1467, -260, 4599]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-4514, -989, -1467, -260, 4599]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![26, 27, 2, 1, 0], ![11, 17, 4, 0, 1]] where
  M :=![![![-4514, -989, -1467, -260, 4599], ![-19355, -4242, -6287, -1114, 19713], ![-82969, -18183, -26958, -4776, 84519], ![-168188, -36851, -54647, -9685, 171336], ![-62359, -13665, -20261, -3590, 63524]]]
  hmulB := by decide  
  f := ![![![-108, -9, 31, 12, -63]], ![![147, -8, -63, -22, 135]], ![![-367, -23, 52, 28, -111]], ![![15, -19, -30, -9, 69]], ![![-12, -12, -17, -4, 38]]]
  g := ![![![-1667, -2488, -667, -260, 4599], ![-7146, -10665, -2859, -1114, 19713], ![-30638, -45726, -12258, -4776, 84519], ![-62106, -92692, -24849, -9685, 171336], ![-23027, -34367, -9213, -3590, 63524]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [2, 0, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 14, 21], [18, 14, 8], [0, 1]]
 g := ![![[21, 10, 7], [12, 28], [25, 9, 25], [1]], ![[3, 24, 13, 17], [0, 4], [7, 2, 23, 8], [4, 23, 12, 10]], ![[24, 11, 26, 17], [10, 13], [9, 7, 1, 21], [13, 6, 28, 19]]]
 h' := ![![[16, 14, 21], [11, 10, 6], [8, 15, 17], [27, 0, 5], [0, 1]], ![[18, 14, 8], [4, 1, 4], [2, 24, 2], [28, 5, 12], [16, 14, 21]], ![[0, 1], [15, 18, 19], [21, 19, 10], [6, 24, 12], [18, 14, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 28], []]
 b := ![[], [14, 25, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [2, 0, 24, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![272032787, 58900526, 78406901, 13513350, -258873792]
  a := ![77, -62, 79, 36, -264]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![95458531, 141203260, 37478461, 13513350, -258873792]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![108, 9, -31, -12, 63]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![108, 9, -31, -12, 63]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![1, 25, 1, 0, 0], ![2, 22, 0, 1, 0], ![21, 24, 0, 0, 1]] where
  M :=![![![108, 9, -31, -12, 63], ![-147, 8, 63, 22, -135], ![367, 23, -52, -28, 111], ![-8, 55, 79, 35, -216], ![191, 21, -29, -14, 56]]]
  hmulB := by decide  
  f := ![![![4514, 989, 1467, 260, -4599]], ![![19355, 4242, 6287, 1114, -19713]], ![![19702, 4318, 6400, 1134, -20067]], ![![20794, 4557, 6755, 1197, -21180]], ![![21437, 4698, 6964, 1234, -21835]]]
  g := ![![![-40, -16, -31, -12, 63], ![89, 41, 63, 22, -135], ![-64, -25, -52, -28, 111], ![151, 86, 79, 35, -216], ![-32, -10, -29, -14, 56]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [26, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 28], [0, 1]]
 g := ![![[12, 1], [4], [0, 7], [7, 1]], ![[19, 28], [4], [20, 22], [14, 28]]]
 h' := ![![[7, 28], [12, 28], [0, 27], [21, 23], [0, 1]], ![[0, 1], [5, 1], [15, 2], [8, 6], [7, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [12, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [26, 22, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6737278, -1310300, -2275498, -301658, 7387092]
  a := ![379, -328, 378, 160, -1299]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5482324, -3968158, -2275498, -301658, 7387092]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-4514, -989, -1467, -260, 4599]] ![![108, 9, -31, -12, 63]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20, 10, -4, -2, 5]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![20, 10, -4, -2, 5]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![26, 16, 30, 1, 0], ![2, 27, 5, 0, 1]] where
  M :=![![![20, 10, -4, -2, 5], ![3, -1, 30, 6, -61], ![221, 38, 31, 18, -139], ![220, 156, 8, -35, -24], ![119, 34, 18, 4, -70]]]
  hmulB := by decide  
  f := ![![![-166, -14, 62, 24, -131]], ![![319, 29, -112, -44, 235]], ![![-559, -42, 219, 84, -467]], ![![-502, -36, 202, 77, -432]], ![![169, 17, -55, -22, 114]]]
  g := ![![![2, -3, 1, -2, 5], ![-1, 50, 5, 6, -61], ![1, 113, 6, 18, -139], ![38, 44, 38, -35, -24], ![5, 60, 8, 4, -70]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [11, 30, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 17, 5], [1, 13, 26], [0, 1]]
 g := ![![[0, 14, 8], [25, 30, 8], [14, 3, 1], [1]], ![[14, 27, 30, 4], [14, 26, 11, 10], [25, 3, 4, 8], [10, 1, 5, 1]], ![[17, 15, 21, 6], [12, 8, 16, 3], [1, 14, 5, 24], [3, 1, 13, 30]]]
 h' := ![![[0, 17, 5], [4, 6, 16], [1, 9, 15], [20, 1, 1], [0, 1]], ![[1, 13, 26], [1, 0, 21], [4, 7, 23], [14, 30, 18], [0, 17, 5]], ![[0, 1], [30, 25, 25], [21, 15, 24], [30, 0, 12], [1, 13, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 17], []]
 b := ![[], [1, 27, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [11, 30, 30, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42686011, 8993553, 12819085, 2293162, -41812677]
  a := ![40, -33, 41, 18, -137]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2151263, 35524040, 4938310, 2293162, -41812677]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![166, 14, -62, -24, 131]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![166, 14, -62, -24, 131]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![15, 2, 1, 0, 0], ![16, 6, 0, 1, 0], ![21, 27, 0, 0, 1]] where
  M :=![![![166, 14, -62, -24, 131], ![-319, -29, 112, 44, -235], ![559, 42, -219, -84, 467], ![-420, -44, 128, 53, -264], ![247, 18, -100, -38, 214]]]
  hmulB := by decide  
  f := ![![![-20, -10, 4, 2, -5]], ![![-3, 1, -30, -6, 61]], ![![-17, -6, -1, 0, 6]], ![![-18, -10, -4, 1, 10]], ![![-20, -7, -24, -4, 52]]]
  g := ![![![-41, -105, -62, -24, 131], ![72, 188, 112, 44, -235], ![-149, -375, -219, -84, 467], ![76, 210, 128, 53, -264], ![-69, -172, -100, -38, 214]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [13, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 30], [0, 1]]
 g := ![![[3, 2], [9, 14], [30, 28], [23, 1]], ![[18, 29], [21, 17], [23, 3], [15, 30]]]
 h' := ![![[23, 30], [7, 8], [13, 13], [11, 20], [0, 1]], ![[0, 1], [5, 23], [2, 18], [6, 11], [23, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [20, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [13, 8, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2013630, -398668, -777589, -101339, 2404478]
  a := ![-240, 198, -243, -111, 823]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1265239, -2037302, -777589, -101339, 2404478]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![20, 10, -4, -2, 5]] ![![166, 14, -62, -24, 131]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-117, -48, -40, -8, 98]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-117, -48, -40, -8, 98]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![23, 28, 22, 1, 0], ![29, 32, 18, 0, 1]] where
  M :=![![![-117, -48, -40, -8, 98], ![-378, -147, -124, -24, 302], ![-1174, -464, -391, -80, 962], ![-1656, -668, -532, -99, 1296], ![-662, -264, -220, -44, 539]]]
  hmulB := by decide  
  f := ![![![11, 0, 0, 0, -2]], ![![10, 9, 4, 0, -14]], ![![70, 0, 37, 8, -98]], ![![61, 8, 26, 5, -74]], ![![53, 8, 22, 4, -63]]]
  g := ![![![-75, -80, -44, -8, 98], ![-232, -247, -136, -24, 302], ![-736, -784, -431, -80, 962], ![-999, -1064, -586, -99, 1296], ![-413, -440, -242, -44, 539]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [35, 8, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 3, 34], [16, 33, 3], [0, 1]]
 g := ![![[29, 31, 12], [1, 11], [10, 5, 27], [0, 1], []], ![[27, 26, 7, 36], [21, 36], [14, 17, 25, 7], [27, 16], [19, 9]], ![[19, 2, 31, 25], [8, 30], [1, 27, 5, 10], [11, 9], [13, 9]]]
 h' := ![![[21, 3, 34], [32, 26, 7], [20, 4, 14], [0, 2, 29], [0, 0, 1], [0, 1]], ![[16, 33, 3], [9, 22, 5], [2, 11, 6], [21, 33, 26], [35, 29, 33], [21, 3, 34]], ![[0, 1], [17, 26, 25], [36, 22, 17], [33, 2, 19], [23, 8, 3], [16, 33, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 29], []]
 b := ![[], [32, 34, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [35, 8, 0, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![946270914, 233226143, 210552552, 28079738, -756020525]
  a := ![135, -105, 140, 70, -463]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![600676545, 638909467, 356788318, 28079738, -756020525]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, -2]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, -2]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![11, 30, 1, 0, 0], ![20, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, -2], ![10, 9, 4, 0, -14], ![70, 0, 37, 8, -98], ![184, 44, 36, 9, -144], ![62, 8, 20, 4, -61]]]
  hmulB := by decide  
  f := ![![![-117, -48, -40, -8, 98]], ![![-378, -147, -124, -24, 302]], ![![-373, -146, -123, -24, 300]], ![![-108, -44, -36, -7, 88]], ![![-59, -24, -20, -4, 49]]]
  g := ![![![1, 0, 0, 0, -2], ![4, -3, 4, 0, -14], ![21, -30, 37, 8, -98], ![40, -28, 36, 9, -144], ![15, -16, 20, 4, -61]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P1 : CertificateIrreducibleZModOfList' 37 2 2 5 [20, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 36], [0, 1]]
 g := ![![[26, 11], [1], [7, 4], [4], [1]], ![[4, 26], [1], [36, 33], [4], [1]]]
 h' := ![![[35, 36], [7, 14], [8, 1], [24, 35], [17, 35], [0, 1]], ![[0, 1], [16, 23], [6, 36], [28, 2], [21, 2], [35, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [1, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N1 : CertifiedPrimeIdeal' SI37N1 37 where
  n := 2
  hpos := by decide
  P := [20, 2, 1]
  hirr := P37P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![185124, 81104, -117216, -30040, 202752]
  a := ![-84, 56, -86, -62, 288]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15148, 97232, -117216, -30040, 202752]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N1 B_one_repr
lemma NI37N1 : Nat.card (O ⧸ I37N1) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-117, -48, -40, -8, 98]] ![![11, 0, 0, 0, -2]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [38, 19, 6, 34, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 12, 4, 14, 20], [20, 33, 36, 29, 36], [0, 29, 35, 18], [10, 7, 7, 21, 26], [0, 1]]
 g := ![![[16, 2, 3, 10, 2], [15, 19, 6, 36], [25, 33, 3, 16], [1], []], ![[33, 38, 29, 22, 33, 18, 1, 20], [39, 34, 31, 33], [17, 22, 27, 23], [2, 28, 38, 15, 22, 14, 8, 20], [24, 18, 26, 31]], ![[27, 30, 26, 39, 22, 10], [22, 13, 5, 36], [1, 27, 37, 4], [10, 16, 19, 39, 4, 23, 40, 9], [18, 2, 20, 25]], ![[17, 37, 25, 11, 24, 32, 37], [15, 2, 8, 8], [36, 38, 28, 16], [29, 22, 15, 23, 39, 20, 21], [5, 37]], ![[29, 17, 27, 19, 26, 9, 20, 7], [6, 34, 18, 20], [4, 36, 39, 36], [32, 39, 34, 13, 8, 21, 7, 28], [26, 13, 28, 20]]]
 h' := ![![[7, 12, 4, 14, 20], [8, 26, 13, 26, 24], [2, 2, 8, 33, 6], [3, 22, 35, 7, 37], [0, 0, 1], [0, 1]], ![[20, 33, 36, 29, 36], [31, 24, 1, 26, 40], [18, 15, 35, 14, 19], [34, 4, 20, 10, 8], [39, 12, 38, 33, 40], [7, 12, 4, 14, 20]], ![[0, 29, 35, 18], [30, 21, 16, 30], [28, 13, 25, 32, 35], [5, 32, 27, 38, 39], [3, 0, 24, 24, 20], [20, 33, 36, 29, 36]], ![[10, 7, 7, 21, 26], [22, 23, 2, 32, 31], [10, 11, 30, 38, 7], [5, 13, 10, 32, 4], [15, 16, 26, 39, 7], [0, 29, 35, 18]], ![[0, 1], [26, 29, 9, 9, 28], [7, 0, 25, 6, 15], [6, 11, 31, 36, 35], [14, 13, 34, 27, 15], [10, 7, 7, 21, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 12, 6, 19], [], [], []]
 b := ![[], [7, 21, 13, 39, 38], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [38, 19, 6, 34, 4, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-373881242649488, -81135153129490, -120913319485218, -21164707021908, 381093543908534]
  a := ![-12, 22, -8, 15, 43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9119054698768, -1978906173890, -2949105353298, -516212366388, 9294964485574]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 5 2 5 [34, 42, 6, 16, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 41, 8, 3, 8], [16, 7, 3, 23, 24], [14, 35, 17, 31, 13], [37, 2, 15, 29, 41], [0, 1]]
 g := ![![[26, 42, 0, 33, 13], [35, 13, 7, 41, 6], [20, 41], [1], []], ![[7, 30, 3, 22, 1, 34, 9, 39], [40, 13, 5, 0, 25, 24, 14, 39], [8, 25, 30, 35], [42, 3, 9, 15, 29, 36, 19, 28], [25, 16, 5, 21]], ![[20, 31, 2, 31, 9, 40, 8, 24], [13, 30, 14, 4, 7, 12, 26, 6], [23, 17, 13, 23], [18, 8, 30, 31, 22, 0, 4, 14], [37, 14, 29, 17]], ![[5, 28, 3, 29, 14, 27, 5, 13], [35, 16, 14, 16, 37, 11, 3, 40], [23, 13, 8, 9], [32, 34, 37, 22, 22, 17, 24, 21], [8, 32, 32, 40]], ![[25, 7, 33, 1, 20, 42, 2, 38], [3, 22, 27, 13, 27, 31], [0, 32, 41, 31], [18, 9, 13, 39, 30, 42, 25, 41], [28, 29, 13, 4]]]
 h' := ![![[19, 41, 8, 3, 8], [14, 32, 29, 11, 23], [3, 20, 29, 37, 36], [9, 1, 37, 27], [0, 0, 1], [0, 1]], ![[16, 7, 3, 23, 24], [6, 41, 17, 11, 8], [2, 28, 10, 6, 8], [39, 31, 10, 26, 32], [27, 7, 4, 38, 5], [19, 41, 8, 3, 8]], ![[14, 35, 17, 31, 13], [9, 11, 26, 3, 42], [2, 41, 15, 21, 22], [28, 26, 9, 8, 25], [30, 0, 26, 26, 30], [16, 7, 3, 23, 24]], ![[37, 2, 15, 29, 41], [29, 4, 41, 1, 42], [27, 13, 5, 29, 20], [11, 4, 41, 30, 3], [10, 29, 38, 23, 9], [14, 35, 17, 31, 13]], ![[0, 1], [4, 41, 16, 17, 14], [21, 27, 27, 36], [8, 24, 32, 38, 26], [30, 7, 17, 42, 42], [37, 2, 15, 29, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 40, 33], [], [], []]
 b := ![[], [39, 41, 12, 12], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 5
  hpos := by decide
  P := [34, 42, 6, 16, 0, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18161128991, 10863707136, -12635414679, -4199009985, 23339649994]
  a := ![-12, 6, -13, -11, 41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![422351837, 252644352, -293846853, -97651395, 542782558]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, 6, -6, -2, 11]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![10, 6, -6, -2, 11]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![42, 20, 1, 0, 0], ![3, 33, 0, 1, 0], ![3, 26, 0, 0, 1]] where
  M :=![![![10, 6, -6, -2, 11], ![-27, -7, 14, 2, -19], ![67, -10, 1, 14, -37], ![8, 96, -80, -49, 216], ![23, 6, -8, 0, 10]]]
  hmulB := by decide  
  f := ![![![-136, -10, 52, 20, -109]], ![![265, 27, -92, -36, 197]], ![![-19, 2, 11, 4, -21]], ![![183, 19, -64, -25, 138]], ![![133, 14, -46, -18, 99]]]
  g := ![![![5, -2, -6, -2, 11], ![-12, 3, 14, 2, -19], ![2, 10, 1, 14, -37], ![61, -49, -80, -49, 216], ![7, -2, -8, 0, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [46, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 46], [0, 1]]
 g := ![![[10, 37], [12, 4], [40, 17], [33, 6], [1]], ![[4, 10], [5, 43], [22, 30], [46, 41], [1]]]
 h' := ![![[10, 46], [12, 32], [40, 2], [33, 8], [1, 10], [0, 1]], ![[0, 1], [3, 15], [13, 45], [19, 39], [7, 37], [10, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [1, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [46, 37, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-296929, -40599, -202723, -33082, 551415]
  a := ![-125, 97, -125, -66, 429]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![141754, -196409, -202723, -33082, 551415]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 12, -14, -6, 30]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![15, 12, -14, -6, 30]] 
 ![![47, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![15, 12, -14, -6, 30], ![-66, -35, 42, 14, -78], ![194, 52, -89, -14, 126], ![-184, 56, -16, -47, 144], ![52, 24, -34, -10, 61]]]
  hmulB := by decide  
  f := ![![![-2915, -644, -954, -170, 2982]], ![![-1445, -319, -472, -84, 1476]], ![![-2069, -456, -675, -120, 2112]], ![![-4540, -1000, -1480, -263, 4632]], ![![-3336, -736, -1090, -194, 3409]]]
  g := ![![![-21, 12, -14, -6, 30], ![55, -35, 42, 14, -78], ![-85, 52, -89, -14, 126], ![-108, 56, -16, -47, 144], ![-42, 24, -34, -10, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![105, 22, 34, 6, -108]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![105, 22, 34, 6, -108]] 
 ![![47, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![45, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![105, 22, 34, 6, -108], ![456, 97, 148, 26, -468], ![1976, 422, 643, 114, -2028], ![4044, 874, 1310, 231, -4128], ![1496, 322, 486, 86, -1531]]]
  hmulB := by decide  
  f := ![![![-1281, -114, 466, 178, -972]], ![![-631, -57, 230, 88, -480]], ![![-991, -84, 357, 136, -744]], ![![-1175, -112, 432, 165, -900]], ![![-233, -20, 84, 32, -175]]]
  g := ![![![-23, 22, 34, 6, -108], ![-101, 97, 148, 26, -468], ![-441, 422, 643, 114, -2028], ![-905, 874, 1310, 231, -4128], ![-335, 322, 486, 86, -1531]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2

def I47N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 5, -5, -2, 10]] i)))

def SI47N3: IdealEqSpanCertificate' Table ![![7, 5, -5, -2, 10]] 
 ![![47, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![43, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![7, 5, -5, -2, 10], ![-22, -10, 15, 4, -26], ![74, 11, -18, 2, 10], ![-28, 49, -27, -27, 96], ![24, 9, -9, -2, 13]]]
  hmulB := by decide  
  f := ![![![33, -1, -51, -16, 130]], ![![12, -2, -33, -10, 86]], ![![10, -5, -54, -16, 142]], ![![-27, -12, -62, -17, 170]], ![![-3, -4, -28, -8, 75]]]
  g := ![![![-1, 5, -5, -2, 10], ![0, -10, 15, 4, -26], ![4, 11, -18, 2, 10], ![-23, 49, -27, -27, 96], ![-1, 9, -9, -2, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N3 : Nat.card (O ⧸ I47N3) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N3)

lemma isPrimeI47N3 : Ideal.IsPrime I47N3 := prime_ideal_of_norm_prime hp47.out _ NI47N3
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![10, 6, -6, -2, 11]] ![![15, 12, -14, -6, 30]]
  ![![-470, -250, 304, 92, -541]] where
 M := ![![![-470, -250, 304, 92, -541]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-470, -250, 304, 92, -541]] ![![105, 22, 34, 6, -108]]
  ![![66, -96, 86, 62, -257]] where
 M := ![![![66, -96, 86, 62, -257]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N2 : IdealMulLeCertificate' Table 
  ![![66, -96, 86, 62, -257]] ![![7, 5, -5, -2, 10]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![1034, 2961, -2679, -1504, 6627]]]
 hmul := by decide  
 g := ![![![![22, 63, -57, -32, 141]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2, I47N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
    exact isPrimeI47N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1 ⊙ MulI47N2)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![46420, 10160, 15082, 2672, -47303]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![46420, 10160, 15082, 2672, -47303]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![16, 32, 46, 9, 1]] where
  M :=![![![46420, 10160, 15082, 2672, -47303], ![199107, 43591, 64686, 11460, -202865], ![853885, 186988, 277421, 49152, -869975], ![1731320, 379206, 562486, 99659, -1763832], ![641899, 140588, 208548, 36950, -653966]]]
  hmulB := by decide  
  f := ![![![-34, 16, -4, -6, 19]], ![![-11, -85, 68, 34, -155]], ![![299, 276, -285, -102, 547]], ![![-648, -238, 322, 55, -456]], ![![133, 154, -154, -61, 312]]]
  g := ![![![15156, 28752, 41340, 8083, -47303], ![64999, 123307, 177292, 34665, -202865], ![278745, 528796, 760307, 148659, -869975], ![565144, 1072110, 1541486, 301399, -1763832], ![209535, 397500, 571528, 111748, -653966]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [20, 16, 35, 24, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 30, 3, 30], [32, 7, 45, 7], [48, 15, 5, 16], [0, 1]]
 g := ![![[37, 51, 31, 10], [37, 39, 25], [34, 44, 36, 52], [11, 29, 1], []], ![[15, 28, 9, 3, 4, 21], [17, 32, 40], [10, 10, 25, 47, 32, 23], [3, 20, 9], [20, 20, 9, 23, 22, 23]], ![[47, 2, 9, 33, 47, 36], [6, 21, 6], [4, 31, 20, 13, 52, 37], [9, 10, 37], [11, 1, 12, 26, 26, 25]], ![[28, 50, 48, 48, 10, 9], [22, 47, 16], [19, 7, 5, 30, 31, 24], [35, 4, 38], [20, 25, 12, 13, 35, 15]]]
 h' := ![![[2, 30, 3, 30], [30, 12, 41, 13], [9, 18, 48, 5], [45, 39, 32, 30], [0, 0, 0, 1], [0, 1]], ![[32, 7, 45, 7], [31, 42, 2, 35], [0, 1, 15, 26], [10, 44, 2, 23], [32, 11, 49, 50], [2, 30, 3, 30]], ![[48, 15, 5, 16], [45, 17, 36, 19], [18, 31, 9, 18], [15, 51, 37, 9], [6, 2, 51, 14], [32, 7, 45, 7]], ![[0, 1], [43, 35, 27, 39], [18, 3, 34, 4], [14, 25, 35, 44], [5, 40, 6, 41], [48, 15, 5, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [0, 9, 46], []]
 b := ![[], [], [5, 10, 39, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [20, 16, 35, 24, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-291451692862, -58707358696, -101984644654, -19523493238, 315272209374]
  a := ![-86, 68, -89, -43, 295]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-100675604582, -191460718088, -275556722186, -53905158068, 315272209374]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![34, -16, 4, 6, -19]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![34, -16, 4, 6, -19]] 
 ![![53, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![34, -16, 4, 6, -19], ![11, 85, -68, -34, 155], ![-299, -276, 285, 102, -547], ![648, 238, -322, -55, 456], ![-23, -72, 62, 28, -134]]]
  hmulB := by decide  
  f := ![![![-46420, -10160, -15082, -2672, 47303]], ![![-37039, -8107, -12034, -2132, 37743]], ![![-51145, -11196, -16617, -2944, 52115]], ![![-46680, -10222, -15166, -2687, 47560]], ![![-13863, -3036, -4504, -798, 14124]]]
  g := ![![![8, -16, 4, 6, -19], ![-5, 85, -68, -34, 155], ![-33, -276, 285, 102, -547], ![84, 238, -322, -55, 456], ![1, -72, 62, 28, -134]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![46420, 10160, 15082, 2672, -47303]] ![![34, -16, 4, 6, -19]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39, -6, 2, 2, 2]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-39, -6, 2, 2, 2]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![33, 44, 1, 0, 0], ![41, 52, 0, 1, 0], ![54, 19, 0, 0, 1]] where
  M :=![![![-39, -6, 2, 2, 2], ![-38, -13, -40, -10, 110], ![-410, -78, -83, -10, 290], ![-636, -150, -234, -43, 720], ![-286, -58, -70, -10, 233]]]
  hmulB := by decide  
  f := ![![![39, 10, 18, 6, -46]], ![![146, 77, 12, -6, -34]], ![![135, 64, 23, 0, -60]], ![![169, 80, 24, -1, -66]], ![![86, 35, 22, 4, -57]]]
  g := ![![![-5, -4, 2, 2, 2], ![-72, 3, -40, -10, 110], ![-219, -24, -83, -10, 290], ![-509, -22, -234, -43, 720], ![-172, -15, -70, -10, 233]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [47, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 58], [0, 1]]
 g := ![![[45, 49], [15, 4], [5], [48, 35], [9, 1]], ![[14, 10], [51, 55], [5], [9, 24], [18, 58]]]
 h' := ![![[9, 58], [3, 52], [20, 57], [45, 8], [49, 34], [0, 1]], ![[0, 1], [58, 7], [2, 2], [58, 51], [1, 25], [9, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [33, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [47, 50, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-68935, -8682, -23308, -4317, 79128]
  a := ![-22, 22, -22, -3, 76]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-57554, -4442, -23308, -4317, 79128]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47, -12, -14, -2, 44]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-47, -12, -14, -2, 44]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![18, 3, 1, 0, 0], ![32, 5, 0, 1, 0], ![45, 17, 0, 0, 1]] where
  M :=![![![-47, -12, -14, -2, 44], ![-192, -39, -70, -14, 212], ![-864, -204, -253, -42, 812], ![-1640, -364, -564, -99, 1728], ![-630, -144, -198, -34, 623]]]
  hmulB := by decide  
  f := ![![![-637, -60, 230, 90, -484]], ![![1160, 99, -442, -170, 932]], ![![-174, -17, 61, 24, -128]], ![![-224, -23, 78, 31, -164]], ![![-169, -19, 54, 22, -113]]]
  g := ![![![-29, -12, -14, -2, 44], ![-136, -57, -70, -14, 212], ![-534, -221, -253, -42, 812], ![-1120, -467, -564, -99, 1728], ![-407, -169, -198, -34, 623]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [29, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 58], [0, 1]]
 g := ![![[42, 57], [22, 20], [12], [0, 1], [21, 1]], ![[0, 2], [29, 39], [12], [21, 58], [42, 58]]]
 h' := ![![[21, 58], [11, 36], [6, 16], [0, 37], [40, 58], [0, 1]], ![[0, 1], [0, 23], [47, 43], [10, 22], [19, 1], [21, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [42, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [29, 38, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-808841, -92466, -746849, -120878, 1912270]
  a := ![245, -185, 244, 134, -839]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1178807, -504341, -746849, -120878, 1912270]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, 2, 12, 4, -26]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-19, 2, 12, 4, -26]] 
 ![![59, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![-19, 2, 12, 4, -26], ![74, 11, -6, -4, 10], ![6, 34, 51, 16, -122], ![156, 50, 22, -3, -48], ![8, 18, 28, 8, -65]]]
  hmulB := by decide  
  f := ![![![3283, 722, 1064, 188, -3338]], ![![906, 199, 294, 52, -922]], ![![2859, 628, 927, 164, -2908]], ![![3852, 846, 1250, 221, -3920]], ![![1603, 352, 520, 92, -1631]]]
  g := ![![![-3, 2, 12, 4, -26], ![2, 11, -6, -4, 10], ![-13, 34, 51, 16, -122], ![-6, 50, 22, -3, -48], ![-7, 18, 28, 8, -65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-39, -6, 2, 2, 2]] ![![-47, -12, -14, -2, 44]]
  ![![-3283, -722, -1064, -188, 3338]] where
 M := ![![![-3283, -722, -1064, -188, 3338]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-3283, -722, -1064, -188, 3338]] ![![-19, 2, 12, 4, -26]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![66, 27, 31, 6, -73]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![66, 27, 31, 6, -73]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![25, 13, 33, 30, 1]] where
  M :=![![![66, 27, 31, 6, -73], ![281, 90, 83, 20, -223], ![835, 361, 236, 26, -601], ![1180, 333, 545, 135, -1368], ![491, 187, 165, 28, -422]]]
  hmulB := by decide  
  f := ![![![-12, -1, 5, 2, -11]], ![![27, 4, -9, -4, 19]], ![![-39, -7, 26, 10, -59]], ![![64, 17, -15, -7, 24]], ![![11, 5, 7, 2, -21]]]
  g := ![![![31, 16, 40, 36, -73], ![96, 49, 122, 110, -223], ![260, 134, 329, 296, -601], ![580, 297, 749, 675, -1368], ![181, 93, 231, 208, -422]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 4 2 5 [28, 10, 31, 10, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 37, 47, 43], [52, 33, 55, 21], [43, 51, 20, 58], [0, 1]]
 g := ![![[19, 13, 54, 47], [22, 22, 36], [60, 1, 23, 9], [37, 8, 51, 1], []], ![[24, 53, 20, 54, 52, 30], [28, 11, 58], [15, 35, 10, 51, 57, 31], [43, 45, 35, 8, 56, 54], [15, 39, 16, 2, 60, 24]], ![[11, 20, 35, 39, 31, 53], [54, 42, 1], [52, 58, 38, 47, 17, 17], [39, 51, 12, 46, 47, 11], [55, 43, 33, 47, 41, 50]], ![[19, 37, 47, 5, 13, 45], [4, 38, 48], [7, 43, 34, 5, 40, 13], [41, 45, 50, 35, 19, 42], [49, 28, 4, 30, 17, 34]]]
 h' := ![![[17, 37, 47, 43], [46, 42, 53, 13], [28, 44, 19, 55], [1, 16, 29, 3], [0, 0, 0, 1], [0, 1]], ![[52, 33, 55, 21], [10, 2, 48, 10], [60, 10, 6, 34], [10, 14, 48, 12], [40, 32, 14, 34], [17, 37, 47, 43]], ![[43, 51, 20, 58], [12, 2, 11, 7], [11, 6, 26, 1], [52, 22, 54, 42], [49, 43, 57, 13], [52, 33, 55, 21]], ![[0, 1], [44, 15, 10, 31], [41, 1, 10, 32], [34, 9, 52, 4], [55, 47, 51, 13], [43, 51, 20, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [54, 18, 36], []]
 b := ![[], [], [12, 57, 45, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 4
  hpos := by decide
  P := [28, 10, 31, 10, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-219916007588, -42582897142, -78284629040, -15666002012, 241527453220]
  a := ![82, -63, 83, 42, -281]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-102591841608, -52171144082, -131945747300, -119040813092, 241527453220]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 13845841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12, -1, 5, 2, -11]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-12, -1, 5, 2, -11]] 
 ![![61, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![-12, -1, 5, 2, -11], ![27, 4, -9, -4, 19], ![-39, -7, 26, 10, -59], ![64, 17, -15, -7, 24], ![-13, -1, 11, 4, -26]]]
  hmulB := by decide  
  f := ![![![66, 27, 31, 6, -73]], ![![23, 9, 10, 2, -24]], ![![31, 13, 12, 2, -29]], ![![28, 9, 13, 3, -32]], ![![47, 19, 21, 4, -50]]]
  g := ![![![5, -1, 5, 2, -11], ![-9, 4, -9, -4, 19], ![28, -7, 26, 10, -59], ![-13, 17, -15, -7, 24], ![12, -1, 11, 4, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![66, 27, 31, 6, -73]] ![![-12, -1, 5, 2, -11]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB312I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB312I1 : PrimesBelowBoundCertificateInterval O 23 61 312 where
  m := 9
  g := ![2, 2, 2, 1, 1, 4, 2, 3, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB312I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1]
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1, I47N2, I47N3]
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
    · exact ![24389, 841]
    · exact ![29791, 961]
    · exact ![50653, 1369]
    · exact ![115856201]
    · exact ![147008443]
    · exact ![2209, 47, 47, 47]
    · exact ![7890481, 53]
    · exact ![3481, 3481, 59]
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
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
      exact NI47N3
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
  β := ![I47N1, I47N2, I47N3, I53N1, I59N2, I61N1]
  Il := ![[], [], [], [], [], [I47N1, I47N2, I47N3], [I53N1], [I59N2], [I61N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
