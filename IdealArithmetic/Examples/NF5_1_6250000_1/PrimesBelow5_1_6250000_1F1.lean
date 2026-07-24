
import IdealArithmetic.Examples.NF5_1_6250000_1.RI5_1_6250000_1
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


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [9, 23, 19, 20, 11, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 26, 0, 3, 17], [13, 28, 8, 14, 10], [8, 14, 7, 19, 16], [23, 18, 14, 22, 15], [0, 1]]
 g := ![![[19, 19, 5, 5, 20], [2, 11, 12, 5], [14, 18, 1], []], ![[2, 13, 18, 28, 15, 7, 4, 27], [16, 7, 12, 20], [14, 18, 24, 19, 15, 17, 26, 27], [28, 12, 12, 16, 7, 1, 4, 12]], ![[21, 22, 20, 23, 18, 21, 1, 27], [4, 11, 16, 7], [26, 16, 18, 13, 3, 17, 24, 19], [21, 2, 1, 3, 17, 5, 15, 14]], ![[18, 2, 5, 20, 8, 26, 12, 20], [4, 12, 5, 23], [4, 21, 15, 11, 5, 14, 13, 1], [23, 26, 3, 1, 13, 11, 15, 7]], ![[4, 13, 14, 8, 26, 12, 15, 11], [8, 16, 14, 1], [21, 11, 9, 21, 0, 6, 4, 3], [15, 13, 18, 13, 27, 13, 26, 11]]]
 h' := ![![[3, 26, 0, 3, 17], [24, 23, 6, 15, 22], [19, 9, 7, 22, 18], [0, 0, 0, 1], [0, 1]], ![[13, 28, 8, 14, 10], [7, 26, 25, 11, 11], [21, 24, 24, 0, 7], [7, 8, 6, 6, 18], [3, 26, 0, 3, 17]], ![[8, 14, 7, 19, 16], [2, 14, 26, 4, 20], [26, 19, 6, 14, 23], [7, 7, 16, 20, 12], [13, 28, 8, 14, 10]], ![[23, 18, 14, 22, 15], [18, 13, 5, 28, 20], [24, 28, 15, 24, 9], [15, 11, 27, 1, 7], [8, 14, 7, 19, 16]], ![[0, 1], [20, 11, 25, 0, 14], [18, 7, 6, 27, 1], [26, 3, 9, 1, 21], [23, 18, 14, 22, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 11, 11, 26], [], [], []]
 b := ![[], [5, 6, 9, 12, 7], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [9, 23, 19, 20, 11, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-353307214919, 121395750498, -192178843198, 39063285186, -805818000516]
  a := ![-17, 4, -15, -20, -68]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12183007411, 4186060362, -6626856662, 1347009834, -27786827604]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-7, -2, -3, -1, -5]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![-7, -2, -3, -1, -5]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![18, 4, 1, 0, 0], ![26, 17, 0, 1, 0], ![4, 7, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-7, -2, -3, -1, -5], ![-3, -9, -4, 1, 3], ![3, -8, -7, -11, 3], ![-15, 8, -13, -27, -72], ![-2, -1, 1, 12, 10]]]
  hmulB := by decide  
  f := ![![![-237559, -764878, -333474, 89980, 271124], ![88660, -2657754, 3906, 0, 0]], ![![-238138, -766744, -334289, 90196, 271786], ![88877, -2664233, 3906, 0, 0]], ![![-168300, -541880, -236251, 63746, 192078], ![62808, -1882892, 2766, 0, 0]], ![![-329838, -1061984, -463009, 124929, 376436], ![123085, -3690115, 5418, 0, 0]], ![![-84427, -271830, -118514, 31977, 96354], ![31504, -944537, 1386, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-18, -4, 31, 0, 0], ![-26, -17, 0, 31, 0], ![-4, -7, 0, 0, 31]], ![![3, 2, -3, -1, -5], ![1, -1, -4, 1, 3], ![13, 6, -7, -11, 3], ![39, 33, -13, -27, -72], ![-12, -9, 1, 12, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [1, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 30], [0, 1]]
 g := ![![[22, 1], [9, 7], [19, 14], [9, 1]], ![[0, 30], [10, 24], [21, 17], [18, 30]]]
 h' := ![![[9, 30], [22, 1], [12, 21], [22, 18], [0, 1]], ![[0, 1], [0, 30], [15, 10], [29, 13], [9, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [13, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [1, 22, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![101155, -142654, 113573, 387542, 924662]
  a := ![-116, -4, -117, -182, -467]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-507029, -440574, 113573, 387542, 924662]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-1, 8, -3, -1, -5]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![-1, 8, -3, -1, -5]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![8, 0, 1, 0, 0], ![0, 20, 0, 1, 0], ![14, 13, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-1, 8, -3, -1, -5], ![-3, -3, 6, 1, 3], ![3, 2, -1, 9, 3], ![15, -2, 7, 9, 48], ![-2, -1, 1, -8, -14]]]
  hmulB := by decide  
  f := ![![![11028, 9333, -21104, -3405, -9887], ![5828, 111941, -62, 0, 0]], ![![126989, 107559, -243063, -39185, -113891], ![66836, 1289104, -837, 0, 0]], ![![2694, 2281, -5156, -832, -2416], ![1420, 27347, -15, 0, 0]], ![![81929, 69388, -156813, -25280, -73475], ![43139, 831680, -540, 0, 0]], ![![58234, 49319, -111460, -17970, -52225], ![30665, 591146, -379, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-8, 0, 31, 0, 0], ![0, -20, 0, 31, 0], ![-14, -13, 0, 0, 31]], ![![3, 3, -3, -1, -5], ![-3, -2, 6, 1, 3], ![-1, -7, -1, 9, 3], ![-23, -26, 7, 9, 48], ![6, 11, 1, -8, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [30, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 30], [0, 1]]
 g := ![![[3, 16], [6, 28], [19, 7], [3, 1]], ![[20, 15], [28, 3], [9, 24], [6, 30]]]
 h' := ![![[3, 30], [6, 4], [19, 11], [3, 10], [0, 1]], ![[0, 1], [18, 27], [21, 20], [2, 21], [3, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [5, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [30, 28, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1319, -1614, 1051, 2880, 8694]
  a := ![-11, 1, -10, -16, -45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4155, -5556, 1051, 2880, 8694]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-4, 1, 0, 0, 0], ![0, -4, 1, 0, 0], ![0, 1, -4, 2, 0], ![3, -1, 2, -1, 12], ![0, 0, 0, -2, -7]]]
  hmulB := by decide  
  f := ![![![14579, -45687, 173495, -86924, 360], ![112282, 10943, 1346857, -930, 0]], ![![14551, -45611, 173219, -86786, 360], ![112066, 10943, 1344718, -930, 0]], ![![14467, -45326, 172118, -86234, 360], ![111418, 10851, 1336162, -930, 0]], ![![7, -19, 85, -43, 0], ![54, 33, 667, 0, 0]], ![![6113, -19159, 72756, -36452, 151], ![47080, 4588, 564811, -390, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-27, 31, 0, 0, 0], ![-15, 0, 31, 0, 0], ![-1, 0, 0, 31, 0], ![-13, 0, 0, 0, 31]], ![![-1, 1, 0, 0, 0], ![3, -4, 1, 0, 0], ![1, 1, -4, 2, 0], ![-5, -1, 2, -1, 12], ![3, 0, 0, -2, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0, 0, 0], ![-7, -2, -3, -1, -5]] ![![31, 0, 0, 0, 0], ![-1, 8, -3, -1, -5]]
  ![![31, 0, 0, 0, 0], ![14, -27, 0, -2, 1]] where
 M := ![![![961, 0, 0, 0, 0], ![-31, 248, -93, -31, -155]], ![![-217, -62, -93, -31, -155], ![-1, -49, 0, 9, 42]]]
 hmul := by decide  
 g := ![![![![17, 27, 0, 2, -1], ![31, 0, 0, 0, 0]], ![![-1, 8, -3, -1, -5], ![0, 0, 0, 0, 0]]], ![![![-7, -2, -3, -1, -5], ![0, 0, 0, 0, 0]], ![![-5, 8, 0, 1, 1], ![11, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![31, 0, 0, 0, 0], ![14, -27, 0, -2, 1]] ![![31, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![961, 0, 0, 0, 0], ![-124, 31, 0, 0, 0]], ![![434, -837, 0, -62, 31], ![-62, 124, -31, 0, -31]]]
 hmul := by decide  
 g := ![![![![31, 0, 0, 0, 0]], ![![-4, 1, 0, 0, 0]]], ![![![14, -27, 0, -2, 1]], ![![-2, 4, -1, 0, -1]]]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 5 2 5 [3, 1, 36, 18, 33, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 13, 21, 11, 35], [27, 32, 19, 3, 7], [20, 12, 21, 1, 4], [34, 16, 13, 22, 28], [0, 1]]
 g := ![![[1, 10, 3, 5, 1], [7, 3, 3, 7], [19, 32, 35, 4, 1], [], []], ![[1, 28, 2, 24, 28, 26, 8, 5], [12, 33, 29, 28], [13, 0, 23, 10, 7, 35, 23, 14], [26, 19, 26, 10], [34, 1, 9, 4]], ![[19, 14, 35, 36, 21, 12, 3, 1], [7, 4, 32, 25], [22, 31, 2, 33, 24, 11, 30, 25], [31, 30, 10, 30], [1, 12, 16, 12]], ![[15, 19, 35, 34, 6, 34, 1, 10], [33, 32, 0, 10], [11, 10, 6, 15, 23, 18, 25, 16], [12, 32, 3, 12], [15, 21, 35, 16]], ![[11, 0, 21, 33, 21, 23, 20, 12], [25, 0, 18, 36], [34, 36, 7, 28, 21, 35, 18, 28], [26, 20, 20, 21], [6, 21, 2, 7]]]
 h' := ![![[34, 13, 21, 11, 35], [9, 33, 32, 18, 36], [17, 33, 30, 13, 9], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[27, 32, 19, 3, 7], [8, 28, 16, 21, 4], [9, 18, 30, 9, 18], [24, 32, 7, 32, 17], [18, 33, 12, 33, 11], [34, 13, 21, 11, 35]], ![[20, 12, 21, 1, 4], [25, 5, 10, 24, 33], [34, 33, 4, 8, 5], [29, 2, 29, 10, 20], [23, 26, 30, 25, 20], [27, 32, 19, 3, 7]], ![[34, 16, 13, 22, 28], [19, 32, 25, 2, 24], [28, 26, 28, 15, 11], [4, 5, 2, 5, 35], [22, 32, 22, 27, 30], [20, 12, 21, 1, 4]], ![[0, 1], [27, 13, 28, 9, 14], [19, 1, 19, 29, 31], [3, 35, 36, 27, 1], [28, 20, 9, 26, 13], [34, 16, 13, 22, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 7, 18], [], [], []]
 b := ![[], [29, 30, 17, 9], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 5
  hpos := by decide
  P := [3, 1, 36, 18, 33, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![154441849470417, -90244189134749, 93315069015692, 75781915410483, 531323135696424]
  a := ![60, -8, 57, 77, 239]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4174104039741, -2439032138777, 2522028892316, 2048159875959, 14360084748552]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [13, 24, 25, 20, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 22, 7, 3, 27], [30, 13, 18, 30, 31], [40, 39, 24, 18, 6], [40, 7, 33, 31, 18], [0, 1]]
 g := ![![[37, 0, 32, 20, 4], [17, 23, 4, 20], [29, 30, 31, 4], [1], []], ![[12, 25, 24, 35, 12, 25, 40, 3], [36, 39, 8, 31], [30, 4, 34, 9], [28, 4, 22, 18, 4, 30, 6, 28], [24, 2, 16, 32]], ![[15, 21, 20, 26, 37, 25, 6, 10], [32, 26, 3, 8], [20, 27, 20, 25], [29, 8, 7, 23, 27, 29, 10, 23], [18, 17, 20, 18]], ![[34, 36, 39, 10, 17, 6, 18, 29], [31, 10, 33, 4], [12, 27, 0, 1], [36, 6, 23, 23, 7, 5, 25, 13], [25, 14, 21, 36]], ![[15, 35, 21, 23, 39, 28, 6, 40], [18, 34, 32, 1], [37, 33, 25, 1], [14, 10, 11, 31, 36, 5, 7, 5], [5, 22, 17, 37]]]
 h' := ![![[11, 22, 7, 3, 27], [34, 15, 36, 7, 2], [38, 30, 34, 4, 26], [28, 17, 16, 21, 39], [0, 0, 1], [0, 1]], ![[30, 13, 18, 30, 31], [24, 23, 30, 20, 14], [0, 17, 39, 29, 21], [29, 3, 10, 5, 38], [14, 5, 28, 28, 11], [11, 22, 7, 3, 27]], ![[40, 39, 24, 18, 6], [40, 2, 21, 17, 9], [28, 11, 28, 25, 34], [40, 30, 19, 7, 5], [10, 4, 8, 31, 16], [30, 13, 18, 30, 31]], ![[40, 7, 33, 31, 18], [25, 32, 13, 17, 11], [31, 8, 39, 0, 2], [8, 2, 23, 1, 1], [4, 1, 34, 14, 3], [40, 39, 24, 18, 6]], ![[0, 1], [16, 10, 23, 21, 5], [2, 16, 24, 24, 40], [27, 30, 14, 7, 40], [18, 31, 11, 9, 11], [40, 7, 33, 31, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 12, 20, 21], [], [], []]
 b := ![[], [22, 31, 4, 15, 22], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [13, 24, 25, 20, 2, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1223587990853, -1956466565028, -72456595476, 6063843928482, 8647045788702]
  a := ![-28, 11, -23, -24, -111]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-29843609533, -47718696708, -1767234036, 147898632402, 210903555822]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 9, -1, 0, -4]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![15, 9, -1, 0, -4]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![4, 9, 1, 0, 0], ![25, 5, 0, 1, 0], ![6, 17, 0, 0, 1]] where
  M :=![![![15, 9, -1, 0, -4], ![0, 14, 9, 6, 12], ![18, 3, 26, 12, 36], ![18, 9, 9, 5, 12], ![-10, -2, -4, -2, -5]]]
  hmulB := by decide  
  f := ![![![-1, -1, -1, 2, -4]], ![![6, -4, 3, 12, 36]], ![![2, -1, 1, 2, 8]], ![![-1, 0, -1, 1, -4]], ![![2, -2, 1, 6, 15]]]
  g := ![![![1, 2, -1, 0, -4], ![-6, -7, 9, 6, 12], ![-14, -21, 26, 12, 36], ![-5, -7, 9, 5, 12], ![2, 3, -4, -2, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [27, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 42], [0, 1]]
 g := ![![[26, 10], [36, 41], [36], [33, 24], [1]], ![[15, 33], [21, 2], [36], [41, 19], [1]]]
 h' := ![![[29, 42], [17, 15], [32, 27], [12, 6], [16, 29], [0, 1]], ![[0, 1], [22, 28], [41, 16], [14, 37], [40, 14], [29, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [36, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [27, 14, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8595, 4084, 2964, -18328, -13968]
  a := ![18, -16, 16, -2, 72]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![12529, 7128, 2964, -18328, -13968]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 15, 23, 12, 31]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![17, 15, 23, 12, 31]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![27, 27, 1, 0, 0], ![1, 15, 0, 1, 0], ![37, 1, 0, 0, 1]] where
  M :=![![![17, 15, 23, 12, 31], ![36, 28, 39, 20, 51], ![60, 55, 68, 36, 87], ![36, 32, 44, 25, 60], ![-14, -14, -18, -10, -23]]]
  hmulB := by decide  
  f := ![![![-11, 9, -3, 2, -1]], ![![6, -16, 13, 2, 27]], ![![-3, -4, 6, 2, 15]], ![![1, -5, 4, 1, 8]], ![![-9, 7, -2, 2, 1]]]
  g := ![![![-41, -19, 23, 12, 31], ![-68, -32, 39, 20, 51], ![-117, -56, 68, 36, 87], ![-79, -37, 44, 25, 60], ![31, 15, -18, -10, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [19, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 42], [0, 1]]
 g := ![![[7, 11], [14, 4], [36], [2, 16], [1]], ![[6, 32], [41, 39], [36], [24, 27], [1]]]
 h' := ![![[39, 42], [35, 21], [29, 2], [5, 6], [24, 39], [0, 1]], ![[0, 1], [37, 22], [21, 41], [24, 37], [40, 4], [39, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [23, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [19, 4, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6797, -2381, 3729, -597, 15670]
  a := ![-10, 8, -6, -9, -53]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15653, -2553, 3729, -597, 15670]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 1, 0, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![1, 1, 1, 0, 0]] 
 ![![43, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![37, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![1, 1, 1, 0, 0], ![0, 2, 1, 2, 0], ![6, -1, 6, 8, 24], ![12, 1, 7, -7, 12], ![-6, 2, -4, -2, -17]]]
  hmulB := by decide  
  f := ![![![133, 55, -83, -38, -144]], ![![19, 11, -14, -6, -24]], ![![115, 44, -69, -32, -120]], ![![123, 50, -76, -35, -132]], ![![125, 53, -79, -36, -137]]]
  g := ![![![-1, 1, 1, 0, 0], ![-3, 2, 1, 2, 0], ![-35, -1, 6, 8, 24], ![-11, 1, 7, -7, 12], ![21, 2, -4, -2, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![15, 9, -1, 0, -4]] ![![17, 15, 23, 12, 31]]
  ![![575, 478, 700, 364, 929]] where
 M := ![![![575, 478, 700, 364, 929]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![575, 478, 700, 364, 929]] ![![1, 1, 1, 0, 0]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![3569, 3053, 4085, 2150, 5375]]]
 hmul := by decide  
 g := ![![![![83, 71, 95, 50, 125]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![-19, -2, -3, -1, -5]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0], ![-19, -2, -3, -1, -5]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![3, 42, 1, 0, 0], ![31, 13, 0, 1, 0], ![24, 29, 0, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![-19, -2, -3, -1, -5], ![-3, -21, -4, 1, 3], ![3, -8, -19, -11, 3], ![-15, 8, -13, -39, -72], ![-2, -1, 1, 12, -2]]]
  hmulB := by decide  
  f := ![![![330514, 3003024, 561471, -146673, -456945], ![-245481, 6741210, 8460, 0, 0]], ![![827531, 7518986, 1405800, -367249, -1144103], ![-614666, 16878687, 21150, 0, 0]], ![![759422, 6900112, 1290092, -337021, -1049933], ![-564065, 15489432, 19410, 0, 0]], ![![446895, 4060438, 759171, -198321, -617842], ![-331915, 9114903, 11430, 0, 0]], ![![679383, 6172834, 1154118, -301497, -939268], ![-504600, 13856829, 17370, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-3, -42, 47, 0, 0], ![-31, -13, 0, 47, 0], ![-24, -29, 0, 0, 47]], ![![3, 6, -3, -1, -5], ![-2, 1, -4, 1, 3], ![7, 18, -19, -11, 3], ![63, 67, -13, -39, -72], ![-7, -3, 1, 12, -2]]]
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
  c := ![202, 213, 17, -940, -1155]
  a := ![2, -4, 1, -3, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1213, 962, 17, -940, -1155]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![-2, -5, -3, -1, -5]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0], ![-2, -5, -3, -1, -5]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![31, 34, 1, 0, 0], ![37, 2, 0, 1, 0], ![12, 46, 0, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![-2, -5, -3, -1, -5], ![-3, -4, -7, 1, 3], ![3, -11, -2, -17, 3], ![-24, 11, -19, -31, -108], ![-2, -1, 1, 18, 24]]]
  hmulB := by decide  
  f := ![![![1908563, 2521635, 4466273, -653649, -1968725], ![-411203, 30166480, -8460, 0, 0]], ![![1143164, 1510373, 2675144, -391516, -1179196], ![-246280, 18068680, -5076, 0, 0]], ![![2081755, 2750460, 4871563, -712966, -2147374], ![-448504, 32903920, -9234, 0, 0]], ![![1551131, 2049388, 3629838, -531235, -1600026], ![-334194, 24516960, -6876, 0, 0]], ![![1606134, 2122059, 3758551, -550075, -1656760], ![-346029, 25386320, -7128, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-31, -34, 47, 0, 0], ![-37, -2, 0, 47, 0], ![-12, -46, 0, 0, 47]], ![![4, 7, -3, -1, -5], ![3, 2, -7, 1, 3], ![14, -1, -2, -17, 3], ![64, 121, -19, -31, -108], ![-21, -25, 1, 18, 24]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [36, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 46], [0, 1]]
 g := ![![[12, 17], [2, 42], [19, 4], [13, 34], [1]], ![[0, 30], [0, 5], [30, 43], [36, 13], [1]]]
 h' := ![![[38, 46], [22, 39], [21, 18], [2, 2], [11, 38], [0, 1]], ![[0, 1], [0, 8], [0, 29], [31, 45], [45, 9], [38, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [27, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [36, 9, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13344, -3043, 7107, -4312, 24369]
  a := ![24, -11, 24, 16, 93]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7231, -28873, 7107, -4312, 24369]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0], ![18, 1, 0, 0, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0], ![18, 1, 0, 0, 0]] 
 ![![47, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![40, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]], ![![18, 1, 0, 0, 0], ![0, 18, 1, 0, 0], ![0, 1, 18, 2, 0], ![3, -1, 2, 21, 12], ![0, 0, 0, -2, 15]]]
  hmulB := by decide  
  f := ![![![134401, -4453, -385353, -35814, 4080], ![-348270, -25991, 1009419, -15980, 0]], ![![53742, -1787, -154163, -14328, 1632], ![-139260, -10387, 403824, -6392, 0]], ![![20140, -666, -57757, -5367, 612], ![-52188, -3900, 151293, -2397, 0]], ![![114215, -3784, -327551, -30442, 3468], ![-295962, -22099, 858009, -13583, 0]], ![![60027, -1991, -172179, -16002, 1823], ![-155546, -11613, 451017, -7140, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-18, 47, 0, 0, 0], ![-5, 0, 47, 0, 0], ![-40, 0, 0, 47, 0], ![-21, 0, 0, 0, 47]], ![![0, 1, 0, 0, 0], ![-7, 18, 1, 0, 0], ![-4, 1, 18, 2, 0], ![-23, -1, 2, 21, 12], ![-5, 0, 0, -2, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0, 0, 0], ![-19, -2, -3, -1, -5]] ![![47, 0, 0, 0, 0], ![-2, -5, -3, -1, -5]]
  ![![47, 0, 0, 0, 0], ![2, 93, -43, -12, -75]] where
 M := ![![![2209, 0, 0, 0, 0], ![-94, -235, -141, -47, -235]], ![![-893, -94, -141, -47, -235], ![69, 130, 91, 9, 68]]]
 hmul := by decide  
 g := ![![![![45, -93, 43, 12, 75], ![47, 0, 0, 0, 0]], ![![-4, -98, 40, 11, 70], ![47, 0, 0, 0, 0]]], ![![![-21, -95, 40, 11, 70], ![47, 0, 0, 0, 0]], ![![1, -19, 12, 3, 19], ![11, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0, 0, 0], ![2, 93, -43, -12, -75]] ![![47, 0, 0, 0, 0], ![18, 1, 0, 0, 0]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![2209, 0, 0, 0, 0], ![846, 47, 0, 0, 0]], ![![94, 4371, -2021, -564, -3525], ![0, 1645, -705, -188, -1269]]]
 hmul := by decide  
 g := ![![![![47, 0, 0, 0, 0]], ![![18, 1, 0, 0, 0]]], ![![![2, 93, -43, -12, -75]], ![![0, 35, -15, -4, -27]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 5 2 5 [34, 5, 11, 32, 40, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 0, 42, 50, 35], [41, 44, 32, 8, 43], [24, 32, 50, 5, 8], [5, 29, 35, 43, 20], [0, 1]]
 g := ![![[50, 7, 41, 42, 42], [27, 6, 4, 36], [17, 25, 27, 11, 7], [13, 1], []], ![[17, 12, 22, 47, 22, 52, 17, 19], [9, 21, 40, 7], [14, 8, 12, 10, 51, 50, 22, 31], [1, 17, 22, 37], [23, 48, 25, 6, 42, 36, 26, 51]], ![[8, 34, 37, 3, 14, 12, 41, 4], [33, 38, 36, 4], [29, 1, 43, 8, 16, 5, 19, 15], [18, 25, 23, 6], [7, 47, 0, 9, 15, 36, 0, 7]], ![[39, 22, 52, 42, 29, 7, 13, 32], [24, 49, 40, 36], [51, 29, 15, 52, 49, 32, 38, 30], [28, 47, 32, 38], [29, 1, 6, 11, 13, 21, 37, 35]], ![[15, 52, 36, 9, 1, 24, 50, 23], [31, 42, 3, 11], [30, 30, 24, 23, 45, 36, 26, 39], [11, 27, 10, 29], [30, 39, 43, 43, 19, 27, 45, 50]]]
 h' := ![![[49, 0, 42, 50, 35], [8, 17, 23, 44, 28], [5, 25, 2, 21, 47], [35, 7, 11, 50, 31], [0, 0, 0, 1], [0, 1]], ![[41, 44, 32, 8, 43], [37, 22, 29, 14, 7], [5, 41, 23, 41, 22], [23, 8, 50, 40, 38], [2, 2, 37, 12, 14], [49, 0, 42, 50, 35]], ![[24, 32, 50, 5, 8], [29, 38, 38, 22, 25], [41, 15, 0, 4, 51], [49, 51, 23, 45, 48], [48, 44, 49, 50, 18], [41, 44, 32, 8, 43]], ![[5, 29, 35, 43, 20], [26, 4, 45, 48, 51], [43, 43, 10, 18, 47], [40, 45, 5, 39, 32], [12, 50, 17, 6, 41], [24, 32, 50, 5, 8]], ![[0, 1], [46, 25, 24, 31, 48], [26, 35, 18, 22, 45], [33, 48, 17, 38, 10], [6, 10, 3, 37, 33], [5, 29, 35, 43, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 2, 51, 15], [], [], []]
 b := ![[], [8, 47, 46, 11, 45], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 5
  hpos := by decide
  P := [34, 5, 11, 32, 40, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![342429976456, 87396221271, 135093868866, -549322864285, -205736465194]
  a := ![18, -6, 15, 17, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6460942952, 1648985307, 2548940922, -10364582345, -3881820098]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 418195493 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0], ![23, 18, -3, -1, -5]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0], ![23, 18, -3, -1, -5]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![49, 41, 1, 0, 0], ![28, 40, 0, 1, 0], ![43, 11, 0, 0, 1]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]], ![![23, 18, -3, -1, -5], ![-3, 21, 16, 1, 3], ![3, 12, 23, 29, 3], ![45, -12, 27, 63, 168], ![-2, -1, 1, -28, -20]]]
  hmulB := by decide  
  f := ![![![2087823, -9706734, -7835604, -482074, -1591382], ![-1605980, 28684266, -63720, 0, 0]], ![![3478455, -16171955, -13054557, -803145, -2651337], ![-2675709, 47789646, -106200, 0, 0]], ![![4150007, -19294181, -15574921, -958212, -3163212], ![-3192264, 57016080, -126684, 0, 0]], ![![3349107, -15570622, -12569139, -773286, -2552749], ![-2576203, 46012632, -102240, 0, 0]], ![![2170160, -10089509, -8144595, -501081, -1654138], ![-1669323, 29815416, -66240, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-49, -41, 59, 0, 0], ![-28, -40, 0, 59, 0], ![-43, -11, 0, 0, 59]], ![![7, 4, -3, -1, -5], ![-16, -12, 16, 1, 3], ![-35, -36, 23, 29, 3], ![-174, -93, 27, 63, 168], ![27, 22, 1, -28, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [31, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 58], [0, 1]]
 g := ![![[19, 51], [37, 7], [3], [46, 15], [1, 1]], ![[11, 8], [44, 52], [3], [2, 44], [2, 58]]]
 h' := ![![[1, 58], [33, 46], [7, 19], [49, 11], [28, 29], [0, 1]], ![[0, 1], [20, 13], [26, 40], [1, 48], [57, 30], [1, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [47, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [31, 58, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24, 239, 24, 47, -480]
  a := ![1, 2, 1, 3, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![308, 45, 24, 47, -480]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0], ![27, -18, -3, -1, -5]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0], ![27, -18, -3, -1, -5]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![44, 37, 1, 0, 0], ![12, 46, 0, 1, 0], ![13, 43, 0, 0, 1]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]], ![![27, -18, -3, -1, -5], ![-3, 25, -20, 1, 3], ![3, -24, 27, -43, 3], ![-63, 24, -45, -41, -264], ![-2, -1, 1, 44, 92]]]
  hmulB := by decide  
  f := ![![![-62819, 11866738, -10448102, 465842, 1267468], ![-3233141, -30324584, 9145, 0, 0]], ![![-591366, 111717273, -98361790, 4385492, 11932358], ![-30437923, -285485542, 85963, 0, 0]], ![![-417494, 78869470, -69440846, 3096050, 8423932], ![-21488363, -201545299, 60698, 0, 0]], ![![-473850, 89515182, -78813890, 3513945, 9560986], ![-24388832, -228749660, 68882, 0, 0]], ![![-444832, 84035765, -73989531, 3298849, 8975736], ![-22895969, -214747422, 64666, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-44, -37, 59, 0, 0], ![-12, -46, 0, 59, 0], ![-13, -43, 0, 0, 59]], ![![4, 6, -3, -1, -5], ![14, 10, -20, 1, 3], ![-12, 14, 27, -43, 3], ![99, 253, -45, -41, -264], ![-30, -102, 1, 44, 92]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [19, 38, 1] where
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
 g := ![![[2, 28], [17, 48], [12], [6, 22], [21, 1]], ![[0, 31], [22, 11], [12], [55, 37], [42, 58]]]
 h' := ![![[21, 58], [31, 21], [24, 15], [4, 22], [14, 9], [0, 1]], ![[0, 1], [0, 38], [44, 44], [53, 37], [26, 50], [21, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [18, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [19, 38, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![76633, -32346, 44130, 13362, 212108]
  a := ![-58, 23, -59, -56, -239]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-81065, -193228, 44130, 13362, 212108]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0], ![-19, 1, 0, 0, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0], ![-19, 1, 0, 0, 0]] 
 ![![59, 0, 0, 0, 0], ![40, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]], ![![-19, 1, 0, 0, 0], ![0, -19, 1, 0, 0], ![0, 1, -19, 2, 0], ![3, -1, 2, -16, 12], ![0, 0, 0, -2, -22]]]
  hmulB := by decide  
  f := ![![![13931001, -2367951, 37896769, -4017192, 19800], ![43244050, 1124245, 117728364, -97350, 0]], ![![9751663, -1657568, 26527640, -2812024, 13860], ![30270718, 786942, 82409548, -68145, 0]], ![![12537831, -2131151, 34106895, -3615452, 17820], ![38919428, 1011792, 105954914, -87615, 0]], ![![464393, -78924, 1263231, -133907, 660], ![1441550, 37504, 3924297, -3245, 0]], ![![7555830, -1284318, 20554180, -2178816, 10739], ![23454502, 609748, 63852672, -52800, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-40, 59, 0, 0, 0], ![-52, 0, 59, 0, 0], ![-2, 0, 0, 59, 0], ![-32, 0, 0, 0, 59]], ![![-1, 1, 0, 0, 0], ![12, -19, 1, 0, 0], ![16, 1, -19, 2, 0], ![-7, -1, 2, -16, 12], ![12, 0, 0, -2, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0, 0, 0], ![23, 18, -3, -1, -5]] ![![59, 0, 0, 0, 0], ![27, -18, -3, -1, -5]]
  ![![59, 0, 0, 0, 0], ![23, 60, 4, 8, -1]] where
 M := ![![![3481, 0, 0, 0, 0], ![1593, -1062, -177, -59, -295]], ![![1357, 1062, -177, -59, -295], ![631, 89, -470, -55, -266]]]
 hmul := by decide  
 g := ![![![![36, -60, -4, -8, 1], ![59, 0, 0, 0, 0]], ![![27, -18, -3, -1, -5], ![0, 0, 0, 0, 0]]], ![![![0, -42, -7, -9, -4], ![59, 0, 0, 0, 0]], ![![-1, -29, -10, -5, -4], ![30, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0, 0, 0], ![23, 60, 4, 8, -1]] ![![59, 0, 0, 0, 0], ![-19, 1, 0, 0, 0]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![3481, 0, 0, 0, 0], ![-1121, 59, 0, 0, 0]], ![![1357, 3540, 236, 472, -59], ![-413, -1121, 0, -118, 118]]]
 hmul := by decide  
 g := ![![![![59, 0, 0, 0, 0]], ![![-19, 1, 0, 0, 0]]], ![![![23, 60, 4, 8, -1]], ![![-7, -19, 0, -2, 2]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [47, 22, 59, 21, 24, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 53, 60, 3, 44], [28, 18, 54, 46, 51], [6, 22, 44, 28, 52], [36, 28, 25, 45, 36], [0, 1]]
 g := ![![[2, 24, 39, 34, 58], [16, 45], [37, 41, 47, 25, 16], [6, 37, 1], []], ![[46, 37, 23, 3, 47, 58, 34, 29], [41, 53, 32, 27], [42, 42, 49, 43, 9, 28, 32, 6], [19, 5, 19, 51, 34, 55, 5, 7], [52, 12, 8, 51, 28, 41, 38, 28]], ![[18, 53, 22, 2, 0, 3, 29, 51], [14, 18, 6, 49], [50, 17, 21, 6, 51, 14, 55, 8], [15, 13, 29, 52, 31, 22, 16, 37], [12, 26, 23, 38, 51, 3, 41, 37]], ![[38, 7, 37, 59, 38, 60, 40, 42], [48, 49, 6, 3], [4, 11, 43, 59, 26, 13, 11, 57], [30, 22, 37, 23, 52, 19, 50, 3], [1, 38, 27, 27, 39, 35, 22, 3]], ![[12, 42, 48, 40, 53, 32, 10, 46], [22, 44, 51, 20], [17, 60, 15, 39, 23, 0, 31, 49], [31, 53, 29, 21, 51, 41, 8, 19], [14, 43, 39, 52, 22, 5, 45, 52]]]
 h' := ![![[28, 53, 60, 3, 44], [26, 50, 12, 49, 27], [30, 45, 18, 44], [23, 20, 5, 48, 57], [0, 0, 0, 1], [0, 1]], ![[28, 18, 54, 46, 51], [10, 25, 32, 54, 24], [31, 2, 54, 4, 24], [28, 53, 47, 21, 21], [49, 33, 48, 38, 22], [28, 53, 60, 3, 44]], ![[6, 22, 44, 28, 52], [14, 1, 7, 39, 60], [60, 2, 9, 55, 54], [16, 59, 57, 43, 32], [38, 41, 34, 23, 51], [28, 18, 54, 46, 51]], ![[36, 28, 25, 45, 36], [43, 56, 46, 29, 6], [46, 59, 50, 18, 53], [10, 36, 15, 55, 21], [47, 19, 15, 47, 52], [6, 22, 44, 28, 52]], ![[0, 1], [6, 51, 25, 12, 5], [8, 14, 52, 1, 52], [34, 15, 59, 16, 52], [4, 29, 25, 13, 58], [36, 28, 25, 45, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 37, 31, 13], [], [], []]
 b := ![[], [25, 1, 27, 22, 51], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [47, 22, 59, 21, 24, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-142898674542, -92983727766, -42272183515, 370201340352, 357809592342]
  a := ![-17, 7, -16, -16, -69]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2342601222, -1524323406, -692986615, 6068874432, 5865731022]
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



lemma PB156I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB156I1 : PrimesBelowBoundCertificateInterval O 23 61 156 where
  m := 9
  g := ![1, 3, 1, 1, 3, 3, 1, 3, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB156I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0]
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
    · exact ![961, 961, 31]
    · exact ![69343957]
    · exact ![115856201]
    · exact ![1849, 1849, 43]
    · exact ![2209, 2209, 47]
    · exact ![418195493]
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
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
  β := ![I31N2, I43N2, I47N2, I59N2]
  Il := ![[], [I31N2], [], [], [I43N2], [I47N2], [], [I59N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
