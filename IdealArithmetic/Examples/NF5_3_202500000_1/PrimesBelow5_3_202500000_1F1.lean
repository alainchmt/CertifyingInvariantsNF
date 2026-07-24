
import IdealArithmetic.Examples.NF5_3_202500000_1.RI5_3_202500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24249, -8423, -1048, 3305, -8178]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![24249, -8423, -1048, 3305, -8178]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![24, 13, 4, 1, 0], ![16, 14, 3, 0, 1]] where
  M :=![![![24249, -8423, -1048, 3305, -8178], ![-58814, 20424, 2540, -8017, 19830], ![142606, -49541, -6167, 19433, -48102], ![-87386, 30329, 3766, -11918, 29442], ![-19736, 6848, 850, -2692, 6647]]]
  hmulB := by decide  
  f := ![![![137, -51, -30, 41, -78]], ![![-542, 130, 102, -127, 246]], ![![1714, -525, -353, 425, -762]], ![![60, -41, -18, 23, -36]], ![![-2, -21, -5, 7, -7]]]
  g := ![![![2613, 2176, 354, 3305, -8178], ![-6334, -5275, -858, -8017, 19830], ![15374, 12802, 2083, 19433, -48102], ![-9394, -7825, -1272, -11918, 29442], ![-2120, -1766, -287, -2692, 6647]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [6, 22, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 1, 7], [14, 27, 22], [0, 1]]
 g := ![![[9, 4, 22], [1, 13], [21, 23, 5], [1]], ![[21, 12, 14, 4], [4, 24], [10, 12, 18, 23], [21, 5, 28, 24]], ![[8, 16, 1, 4], [27, 7], [25, 25, 8, 1], [23, 19, 28, 5]]]
 h' := ![![[4, 1, 7], [7, 15, 14], [19, 16, 19], [23, 7, 18], [0, 1]], ![[14, 27, 22], [21, 9, 19], [4, 12, 16], [25, 20, 13], [4, 1, 7]], ![[0, 1], [7, 5, 25], [16, 1, 23], [25, 2, 27], [14, 27, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 11], []]
 b := ![[], [27, 26, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [6, 22, 11, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-79840994, -31300900, -23001694, -28889776, -42771048]
  a := ![-17, -10, -24, -5, -51]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![44753462, 32519340, 7616226, -28889776, -42771048]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, -51, -30, 41, -78]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![137, -51, -30, 41, -78]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![27, 16, 1, 0, 0], ![10, 6, 0, 1, 0], ![21, 1, 0, 0, 1]] where
  M :=![![![137, -51, -30, 41, -78], ![-542, 130, 102, -127, 246], ![1714, -525, -353, 425, -762], ![-1358, 445, 284, -366, 678], ![196, -38, -34, 50, -113]]]
  hmulB := by decide  
  f := ![![![24249, -8423, -1048, 3305, -8178]], ![![-58814, 20424, 2540, -8017, 19830]], ![![-4955, 1718, 213, -676, 1668]], ![![-6820, 2367, 294, -930, 2298]], ![![14851, -5159, -642, 2024, -5009]]]
  g := ![![![75, 9, -30, 41, -78], ![-248, -34, 102, -127, 246], ![793, 115, -353, 425, -762], ![-676, -89, 284, -366, 678], ![103, 11, -34, 50, -113]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [22, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 28], [0, 1]]
 g := ![![[18, 4], [13], [14, 23], [10, 1]], ![[0, 25], [13], [12, 6], [20, 28]]]
 h' := ![![[10, 28], [9, 2], [11, 10], [12, 20], [0, 1]], ![[0, 1], [0, 27], [24, 19], [9, 9], [10, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [25, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [22, 19, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5084054, 4923044, 3859753, 2243747, 7391628]
  a := ![-240, -181, -361, -1, -723]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9544515, -2678866, 3859753, 2243747, 7391628]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![24249, -8423, -1048, 3305, -8178]] ![![137, -51, -30, 41, -78]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -3, -3, -4, -6]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-9, -3, -3, -4, -6]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![2, 22, 1, 0, 0], ![17, 22, 0, 1, 0], ![15, 11, 0, 0, 1]] where
  M :=![![![-9, -3, -3, -4, -6], ![-56, -16, -12, -19, -24], ![-230, -87, -61, -79, -114], ![-452, -155, -112, -158, -204], ![-122, -44, -34, -46, -61]]]
  hmulB := by decide  
  f := ![![![-281, 97, 11, -38, 96]], ![![692, -234, -28, 91, -228]], ![![420, -141, -17, 55, -138]], ![![369, -124, -15, 48, -120]], ![![117, -39, -5, 15, -37]]]
  g := ![![![5, 7, -3, -4, -6], ![21, 30, -12, -19, -24], ![95, 137, -61, -79, -114], ![178, 259, -112, -158, -204], ![53, 77, -34, -46, -61]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [17, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 30], [0, 1]]
 g := ![![[3, 14], [15, 25], [7, 28], [11, 1]], ![[2, 17], [11, 6], [5, 3], [22, 30]]]
 h' := ![![[11, 30], [24, 13], [5, 5], [30, 11], [0, 1]], ![[0, 1], [12, 18], [29, 26], [27, 20], [11, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [16, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [17, 20, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![31122, 21082, 16035, 12756, 30244]
  a := ![-15, -10, -22, -3, -46]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-21660, -30484, 16035, 12756, 30244]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, -8, -8, 0, 14]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![39, -8, -8, 0, 14]] 
 ![![31, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![39, -8, -8, 0, 14], ![112, 61, 0, -10, 0], ![-20, 102, 31, -10, -60], ![-136, 14, 24, 1, -40], ![-52, -94, -18, 12, 33]]]
  hmulB := by decide  
  f := ![![![-623, 204, 20, -88, 194]], ![![-36, 9, 0, -6, 8]], ![![-427, 134, 11, -62, 126]], ![![-95, 14, -4, -19, 10]], ![![-131, 38, 2, -20, 35]]]
  g := ![![![3, -8, -8, 0, 14], ![-2, 61, 0, -10, 0], ![-13, 102, 31, -10, -60], ![-9, 14, 24, 1, -40], ![9, -94, -18, 12, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-205, 9, 33, 4, -58]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![-205, 9, 33, 4, -58]] 
 ![![31, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![-205, 9, 33, 4, -58], ![-456, -292, -12, 45, 24], ![282, -375, -145, 33, 270], ![684, 21, -96, -18, 164], ![102, 384, 90, -46, -165]]]
  hmulB := by decide  
  f := ![![![1403, -147, 87, 298, -76]], ![![769, -31, 69, 179, 16]], ![![1443, -48, 134, 339, 42]], ![![1772, 117, 240, 472, 256]], ![![1377, -57, 123, 320, 27]]]
  g := ![![![13, 9, 33, 4, -58], ![92, -292, -12, 45, 24], ![48, -375, -145, 33, 270], ![-51, 21, -96, -18, 164], ![-83, 384, 90, -46, -165]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2

def I31N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 60, 42, 56, 80]] i)))

def SI31N3: IdealEqSpanCertificate' Table ![![151, 60, 42, 56, 80]] 
 ![![31, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![151, 60, 42, 56, 80], ![752, 245, 186, 262, 336], ![3212, 1164, 845, 1156, 1572], ![6284, 2168, 1606, 2227, 2948], ![1844, 638, 472, 654, 867]]]
  hmulB := by decide  
  f := ![![![129, -164, -58, 72, -88]], ![![61, -95, -32, 38, -40]], ![![145, -72, -37, 44, -68]], ![![37, -92, -28, 35, -36]], ![![28, -50, -16, 22, -29]]]
  g := ![![![-109, 60, 42, 56, 80], ![-473, 245, 186, 262, 336], ![-2173, 1164, 845, 1156, 1572], ![-4109, 2168, 1606, 2227, 2948], ![-1208, 638, 472, 654, 867]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N3 : Nat.card (O ⧸ I31N3) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N3)

lemma isPrimeI31N3 : Ideal.IsPrime I31N3 := prime_ideal_of_norm_prime hp31.out _ NI31N3
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-9, -3, -3, -4, -6]] ![![39, -8, -8, 0, 14]]
  ![![229, 91, -9, -16, 16]] where
 M := ![![![229, 91, -9, -16, 16]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![229, 91, -9, -16, 16]] ![![-205, 9, 33, 4, -58]]
  ![![-100291, -15328, 10746, 4266, -18792]] where
 M := ![![![-100291, -15328, 10746, 4266, -18792]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N2 : IdealMulLeCertificate' Table 
  ![![-100291, -15328, 10746, 4266, -18792]] ![![151, 60, 42, 56, 80]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![651, -5084, -1488, 558, 2728]]]
 hmul := by decide  
 g := ![![![![21, -164, -48, 18, 88]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2, I31N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
    exact isPrimeI31N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1 ⊙ MulI31N2)
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


def P37P0 : CertificateIrreducibleZModOfList' 37 5 2 5 [3, 9, 18, 0, 12, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 26, 17, 27, 1], [11, 21, 29, 7, 25], [4, 22, 15, 5, 28], [21, 4, 13, 35, 20], [0, 1]]
 g := ![![[16, 15, 36, 25, 7], [19, 20, 21, 3], [32, 30, 33, 25, 1], [], []], ![[18, 9, 6, 9, 3, 25, 15, 1], [18, 31, 8, 9], [3, 33, 27, 9, 34, 3, 33, 11], [7, 11, 28, 26], [27, 0, 5, 1]], ![[32, 4, 28, 7, 12, 2, 23, 33], [24, 17, 23, 12], [14, 36, 22, 36, 13, 9, 6, 11], [2, 10, 26, 3], [4, 16, 28, 33]], ![[19, 0, 29, 24, 19, 36, 27, 34], [21, 34, 0, 1], [10, 12, 16, 33, 16, 24, 17, 34], [16, 8, 21, 34], [8, 30, 11, 7]], ![[7, 29, 30, 25, 7, 13, 4, 5], [24, 36, 34, 36], [5, 0, 2, 36, 15, 36, 29, 6], [6, 20, 35, 7], [35, 32, 4, 30]]]
 h' := ![![[26, 26, 17, 27, 1], [20, 10, 26, 4, 9], [15, 29, 17, 13, 15], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[11, 21, 29, 7, 25], [24, 4, 17, 0, 36], [35, 0, 24, 30, 34], [25, 9, 15, 27, 14], [3, 36, 23, 20, 27], [26, 26, 17, 27, 1]], ![[4, 22, 15, 5, 28], [6, 4, 0, 14, 5], [2, 3, 4, 33, 30], [35, 31, 0, 7, 25], [35, 8, 2, 30, 22], [11, 21, 29, 7, 25]], ![[21, 4, 13, 35, 20], [36, 4, 2, 13, 5], [32, 26, 36, 6, 1], [16, 15, 36, 28, 32], [29, 14, 9, 3, 16], [4, 22, 15, 5, 28]], ![[0, 1], [36, 15, 29, 6, 19], [21, 16, 30, 29, 31], [28, 19, 23, 12, 2], [3, 16, 2, 21, 9], [21, 4, 13, 35, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 24, 32, 10], [], [], []]
 b := ![[], [12, 23, 17, 7, 27], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 5
  hpos := by decide
  P := [3, 9, 18, 0, 12, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![494037936120994305, 176634923240404953, 130076715363381000, 176365141724963887, 240133075201393142]
  a := ![98, 72, 147, -1, 293]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![13352376651918765, 4773916844335269, 3515586901713000, 4766625452026051, 6490083113551166]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![253, -78, -52, 64, -120]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![253, -78, -52, 64, -120]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![16, 4, 1, 0, 0], ![25, 1, 0, 1, 0], ![6, 22, 0, 0, 1]] where
  M :=![![![253, -78, -52, 64, -120], ![-832, 249, 166, -212, 384], ![2648, -826, -553, 670, -1272], ![-2340, 674, 450, -601, 1044], ![312, -106, -72, 78, -163]]]
  hmulB := by decide  
  f := ![![![189, 38, -16, -8, 24]], ![![176, 221, 30, -32, -48]], ![![80, 38, -1, -6, 0]], ![![105, 25, -8, -5, 12]], ![![126, 120, 12, -18, -19]]]
  g := ![![![5, 66, -52, 64, -120], ![-12, -211, 166, -212, 384], ![58, 700, -553, 670, -1272], ![-19, -573, 450, -601, 1044], ![12, 90, -72, 78, -163]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [36, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 40], [0, 1]]
 g := ![![[10, 8], [25], [39], [40, 40], [1]], ![[0, 33], [25], [39], [31, 1], [1]]]
 h' := ![![[9, 40], [22, 34], [15, 36], [36, 11], [5, 9], [0, 1]], ![[0, 1], [0, 7], [11, 5], [12, 30], [4, 32], [9, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [35, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [36, 32, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20214, 78283, 62485, 16126, 121235]
  a := ![-32, -24, -50, 8, -95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-51466, -69633, 62485, 16126, 121235]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4541, -1577, -196, 619, -1532]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![4541, -1577, -196, 619, -1532]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![24, 22, 1, 0, 0], ![37, 4, 0, 1, 0], ![14, 21, 0, 0, 1]] where
  M :=![![![4541, -1577, -196, 619, -1532], ![-11018, 3824, 476, -1501, 3714], ![26710, -9281, -1155, 3641, -9006], ![-16358, 5681, 706, -2230, 5518], ![-3692, 1286, 160, -504, 1245]]]
  hmulB := by decide  
  f := ![![![-183, 47, 34, -45, 80]], ![![550, -182, -122, 137, -270]], ![![142, -57, -37, 35, -78]], ![![-77, 12, 10, -19, 26]], ![![212, -76, -50, 53, -109]]]
  g := ![![![190, 791, -196, 619, -1532], ![-461, -1918, 476, -1501, 3714], ![1117, 4651, -1155, 3641, -9006], ![-684, -2849, 706, -2230, 5518], ![-154, -643, 160, -504, 1245]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [12, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 40], [0, 1]]
 g := ![![[35, 2], [31], [10], [19, 18], [1]], ![[15, 39], [31], [10], [3, 23], [1]]]
 h' := ![![[31, 40], [39, 17], [40, 21], [18, 25], [29, 31], [0, 1]], ![[0, 1], [33, 24], [35, 20], [14, 16], [6, 10], [31, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [14, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [12, 10, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-67396, 21992, 20068, -21908, 38832]
  a := ![14, 18, 30, -26, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6880, -27984, 20068, -21908, 38832]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63, -21, -6, 11, -24]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![63, -21, -6, 11, -24]] 
 ![![41, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![63, -21, -6, 11, -24], ![-170, 56, 18, -31, 66], ![466, -153, -55, 89, -186], ![-338, 109, 44, -68, 138], ![-8, 4, -4, 2, -1]]]
  hmulB := by decide  
  f := ![![![-109, -85, -8, 11, 12]], ![![-37, -33, -4, 4, 6]], ![![-43, -38, -5, 4, 6]], ![![-76, -57, -6, 6, 6]], ![![-19, -9, 0, 1, -1]]]
  g := ![![![6, -21, -6, 11, -24], ![-16, 56, 18, -31, 66], ![44, -153, -55, 89, -186], ![-31, 109, 44, -68, 138], ![-1, 4, -4, 2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![253, -78, -52, 64, -120]] ![![4541, -1577, -196, 619, -1532]]
  ![![15485, -5377, -672, 2113, -5224]] where
 M := ![![![15485, -5377, -672, 2113, -5224]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![15485, -5377, -672, 2113, -5224]] ![![63, -21, -6, 11, -24]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![904091, -314060, -38868, 123082, -304712]]]
 hmul := by decide  
 g := ![![![![22051, -7660, -948, 3002, -7432]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 47, 12, 3, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![53, 47, 12, 3, 0]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![32, 30, 4, 1, 0], ![17, 33, 32, 0, 1]] where
  M :=![![![53, 47, 12, 3, 0], ![6, 44, 44, 39, 18], ![222, 19, 117, 189, 234], ![826, 197, 210, 334, 462], ![460, 170, 60, 80, 137]]]
  hmulB := by decide  
  f := ![![![1907, -579, -394, 489, -900]], ![![-6222, 1890, 1282, -1593, 2934]], ![![20286, -6163, -4171, 5187, -9558]], ![![-1438, 437, 296, -368, 678]], ![![11135, -3383, -2288, 2846, -5245]]]
  g := ![![![-1, -1, 0, 3, 0], ![-36, -40, -16, 39, 18], ![-228, -311, -189, 189, 234], ![-412, -583, -370, 334, 462], ![-103, -157, -108, 80, 137]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [37, 28, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 23, 40], [22, 19, 3], [0, 1]]
 g := ![![[3, 27, 15], [33, 37, 11], [31, 23], [24, 40, 1], []], ![[18, 37, 34, 38], [11, 25, 2, 25], [27, 16], [8, 9, 41, 35], [7, 9]], ![[23, 17, 30, 37], [2, 24, 22, 30], [12, 11], [40, 18, 19, 39], [1, 9]]]
 h' := ![![[18, 23, 40], [26, 3, 12], [24, 27, 22], [15, 41, 18], [0, 0, 1], [0, 1]], ![[22, 19, 3], [0, 2, 4], [5, 18, 36], [31, 4, 4], [22, 41, 19], [18, 23, 40]], ![[0, 1], [38, 38, 27], [3, 41, 28], [19, 41, 21], [17, 2, 23], [22, 19, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 36], []]
 b := ![[], [38, 21, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [37, 28, 3, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12419951, 4462187, 3285828, 4436499, 6064372]
  a := ![12, 6, 10, 5, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5410287, -7645513, -4849304, 4436499, 6064372]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1907, -579, -394, 489, -900]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![1907, -579, -394, 489, -900]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![20, 30, 1, 0, 0], ![36, 3, 0, 1, 0], ![3, 33, 0, 0, 1]] where
  M :=![![![1907, -579, -394, 489, -900], ![-6222, 1890, 1282, -1593, 2934], ![20286, -6163, -4171, 5187, -9558], ![-17342, 5271, 3560, -4430, 8166], ![2560, -780, -520, 650, -1201]]]
  hmulB := by decide  
  f := ![![![53, 47, 12, 3, 0]], ![![6, 44, 44, 39, 18]], ![![34, 53, 39, 33, 18]], ![![64, 47, 18, 13, 12]], ![![19, 41, 36, 32, 17]]]
  g := ![![![-119, 918, -394, 489, -900], ![388, -2991, 1282, -1593, 2934], ![-1264, 9740, -4171, 5187, -9558], ![1080, -8319, 3560, -4430, 8166], ![-159, 1221, -520, 650, -1201]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [19, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 42], [0, 1]]
 g := ![![[27, 41], [16, 4], [10], [42, 9], [1]], ![[21, 2], [28, 39], [10], [26, 34], [1]]]
 h' := ![![[3, 42], [40, 16], [42, 41], [19, 15], [24, 3], [0, 1]], ![[0, 1], [2, 27], [36, 2], [21, 28], [33, 40], [3, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [16, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [19, 40, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6855, 4909, 3543, 2912, 6673]
  a := ![-8, -6, -11, -1, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4392, -7682, 3543, 2912, 6673]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![53, 47, 12, 3, 0]] ![![1907, -579, -394, 489, -900]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26573, -8085, -5434, 6771, -12498]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![26573, -8085, -5434, 6771, -12498]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![8, 23, 6, 1, 0], ![22, 6, 0, 0, 1]] where
  M :=![![![26573, -8085, -5434, 6771, -12498], ![-86442, 26280, 17662, -22029, 40626], ![280950, -85507, -57469, 71583, -132174], ![-239906, 72867, 48968, -61148, 112650], ![34876, -10638, -7150, 8882, -16441]]]
  hmulB := by decide  
  f := ![![![-353, -227, -12, 33, 30]], ![![306, -278, -116, 27, 198]], ![![1638, 647, -81, -123, 162]], ![![320, -77, -68, 1, 120]], ![![-150, -146, -18, 20, 35]]]
  g := ![![![5263, -1890, -980, 6771, -12498], ![-17106, 6153, 3188, -22029, 40626], ![55662, -19976, -10361, 71583, -132174], ![-47426, 17093, 8848, -61148, 112650], ![6926, -2474, -1286, 8882, -16441]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [38, 4, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 6, 6], [36, 40, 41], [0, 1]]
 g := ![![[39, 1, 12], [13, 24, 9], [1, 27, 7], [23, 11, 1], []], ![[10, 22, 28, 1], [2, 0, 19, 24], [18, 43, 17, 3], [19, 9, 41, 12], [45, 36]], ![[41, 34, 5, 11], [4, 23, 13, 41], [34, 0, 8, 40], [17, 17, 5, 19], [10, 36]]]
 h' := ![![[22, 6, 6], [23, 10, 24], [9, 36, 44], [19, 7, 30], [0, 0, 1], [0, 1]], ![[36, 40, 41], [6, 29, 33], [14, 26, 2], [6, 15, 20], [43, 32, 40], [22, 6, 6]], ![[0, 1], [42, 8, 37], [14, 32, 1], [21, 25, 44], [23, 15, 6], [36, 40, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 31], []]
 b := ![[], [15, 5, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [38, 4, 36, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![46819146, 20544868, 15141368, 17250839, 28371753]
  a := ![16, 10, 23, 2, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15220556, -11626701, -1880078, 17250839, 28371753]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![305, -105, -13, 42, -102]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![305, -105, -13, 42, -102]] 
 ![![47, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![45, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![305, -105, -13, 42, -102], ![-732, 258, 34, -99, 252], ![1818, -613, -73, 255, -594], ![-1052, 399, 62, -134, 396], ![-230, 90, 14, -28, 89]]]
  hmulB := by decide  
  f := ![![![-863, -437, 9, 72, -12]], ![![-660, -352, 2, 57, 0]], ![![-290, -169, -3, 27, 6]], ![![-773, -388, 9, 64, -12]], ![![-558, -260, 12, 44, -19]]]
  g := ![![![113, -105, -13, 42, -102], ![-283, 258, 34, -99, 252], ![649, -613, -73, 255, -594], ![-462, 399, 62, -134, 396], ![-106, 90, 14, -28, 89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![735, -367, -80, 65, -378]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![735, -367, -80, 65, -378]] 
 ![![47, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![735, -367, -80, 65, -378], ![-2894, 502, -92, -553, 390], ![2014, -2965, -1065, -439, -3318], ![-9434, -1047, -1458, -2648, -1854], ![-2552, -384, -438, -748, -619]]]
  hmulB := by decide  
  f := ![![![5693, 823, -622, -229, 1062]], ![![4895, 835, -500, -212, 852]], ![![3356, 629, -327, -149, 546]], ![![701, 82, -82, -27, 144]], ![![667, -61, -116, -9, 203]]]
  g := ![![![399, -367, -80, 65, -378], ![-355, 502, -92, -553, 390], ![3620, -2965, -1065, -439, -3318], ![2303, -1047, -1458, -2648, -1854], ![753, -384, -438, -748, -619]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![26573, -8085, -5434, 6771, -12498]] ![![305, -105, -13, 42, -102]]
  ![![-104579, 31756, 21173, -26559, 48924]] where
 M := ![![![-104579, 31756, 21173, -26559, 48924]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-104579, 31756, 21173, -26559, 48924]] ![![735, -367, -80, 65, -378]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![-421449, 564517, 189833, 79430, 620118]]]
 hmul := by decide  
 g := ![![![![-8967, 12011, 4039, 1690, 13194]]]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 5 2 5 [33, 42, 19, 19, 31, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 1, 29, 37, 12], [49, 2, 15, 13, 36], [6, 11, 46, 32, 6], [50, 38, 16, 24, 52], [0, 1]]
 g := ![![[25, 42, 39, 12, 40], [4, 31, 28, 44], [50, 30, 21, 35, 38], [22, 1], []], ![[14, 33, 15, 26, 2, 2, 5, 23], [25, 30, 40, 49], [28, 14, 13, 37, 21, 3, 34, 26], [41, 19, 38, 25], [18, 25, 20, 9, 4, 47, 46, 32]], ![[34, 48, 43, 13, 41, 5, 5, 29], [50, 52, 37, 15], [6, 48, 47, 24, 24, 36, 24, 52], [32, 18, 2, 17], [44, 15, 30, 16, 50, 35, 16, 16]], ![[29, 31, 47, 27, 32, 21, 1, 36], [41, 46, 22, 16], [1, 26, 28, 10, 1, 47, 40, 13], [48, 9, 43, 11], [8, 12, 36, 43, 18, 9, 46, 4]], ![[13, 45, 42, 25, 13, 16, 38, 15], [40, 11, 49, 44], [15, 32, 51, 52, 0, 24, 28, 25], [36, 30, 4, 43], [34, 6, 23, 21, 4, 22, 50, 52]]]
 h' := ![![[23, 1, 29, 37, 12], [23, 7, 29, 33, 27], [46, 28, 22, 17, 16], [16, 50, 17, 40, 41], [0, 0, 0, 1], [0, 1]], ![[49, 2, 15, 13, 36], [38, 30, 48, 4, 17], [11, 17, 46, 6, 46], [15, 52, 6, 34, 8], [19, 6, 50, 30, 48], [23, 1, 29, 37, 12]], ![[6, 11, 46, 32, 6], [47, 14, 2, 4, 32], [52, 46, 19, 18, 11], [21, 42, 32, 35, 5], [21, 32, 18, 24, 32], [49, 2, 15, 13, 36]], ![[50, 38, 16, 24, 52], [0, 26, 29, 6, 18], [9, 46, 22, 28, 49], [31, 21, 31, 28, 8], [5, 32, 2, 29, 45], [6, 11, 46, 32, 6]], ![[0, 1], [4, 29, 51, 6, 12], [23, 22, 50, 37, 37], [2, 47, 20, 22, 44], [17, 36, 36, 22, 34], [50, 38, 16, 24, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 16, 28, 30], [], [], []]
 b := ![[], [43, 38, 25, 14, 24], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 5
  hpos := by decide
  P := [33, 42, 19, 19, 31, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![249190878396213, 93634563623464, 68832349345362, 89651675764692, 127696546937208]
  a := ![24, 18, 37, -5, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4701714686721, 1766689879688, 1298723572554, 1691541052164, 2409368810136]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0, 0, 0]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]] where
  M :=![![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![0, 0, 0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [8, 45, 44, 44, 14, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 49, 43, 5, 38], [16, 27, 53, 1, 58], [26, 57, 14, 25, 27], [1, 43, 8, 28, 54], [0, 1]]
 g := ![![[44, 15, 2, 40, 48], [8, 35, 30, 49, 36], [31, 12, 58, 12], [34, 45, 1], []], ![[10, 55, 10, 0, 43, 55, 15, 33], [50, 54, 42, 37, 33, 20, 5, 6], [8, 19, 9, 41], [28, 19, 40, 27, 56, 52, 18, 37], [54, 1, 17, 4, 39, 1, 38, 2]], ![[52, 41, 1, 6, 9, 17, 1, 58], [20, 38, 38, 9, 8, 15, 25, 52], [8, 37, 52, 5], [8, 20, 51, 17, 42, 55, 25, 52], [8, 27, 27, 10, 5, 21, 17, 58]], ![[24, 11, 32, 56, 25, 21, 43, 48], [32, 2, 25, 17, 16, 47, 45, 29], [39, 11, 39, 4], [49, 41, 16, 54, 34, 11, 2, 41], [39, 54, 15, 44, 54, 1, 9, 36]], ![[39, 42, 47, 35, 36, 40, 9, 39], [21, 29, 35, 45, 52, 6, 26, 34], [31, 51, 0, 29], [24, 13, 53, 39, 35, 23, 1, 40], [31, 30, 44, 3, 44, 30, 15, 52]]]
 h' := ![![[2, 49, 43, 5, 38], [54, 28, 31, 51, 44], [45, 10, 30, 8, 53], [23, 57, 11, 19, 37], [0, 0, 0, 1], [0, 1]], ![[16, 27, 53, 1, 58], [44, 19, 10, 4, 52], [24, 15, 35, 15, 54], [18, 13, 40, 38, 10], [48, 38, 34, 5, 39], [2, 49, 43, 5, 38]], ![[26, 57, 14, 25, 27], [34, 14, 14, 52, 58], [52, 6, 44, 1, 40], [23, 58, 41, 44, 51], [20, 41, 45, 58, 19], [16, 27, 53, 1, 58]], ![[1, 43, 8, 28, 54], [39, 19, 0, 42, 21], [0, 18, 19, 41, 22], [28, 9, 45, 9, 2], [36, 11, 12, 23, 14], [26, 57, 14, 25, 27]], ![[0, 1], [28, 38, 4, 28, 2], [14, 10, 49, 53, 8], [47, 40, 40, 8, 18], [48, 28, 27, 31, 46], [1, 43, 8, 28, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 33, 2, 31], [], [], []]
 b := ![[], [53, 16, 6, 27, 38], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 5
  hpos := by decide
  P := [8, 45, 44, 44, 14, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6089188881744, 2154337990688, 1587121992958, 2170270384554, 2926806663636]
  a := ![11, 7, 14, 1, 29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![103206591216, 36514203232, 26900372762, 36784243806, 49606892604]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39, 8, 4, -2, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-39, 8, 4, -2, 0]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![50, 57, 59, 1, 0], ![42, 36, 29, 0, 1]] where
  M :=![![![-39, 8, 4, -2, 0], ![-4, -45, -2, 10, -12], ![-76, -4, -13, -8, 60], ![128, -20, -10, 5, 0], ![32, 34, 8, -2, -23]]]
  hmulB := by decide  
  f := ![![![5, 0, 0, 2, 0]], ![![4, 7, 6, 2, 12]], ![![100, 12, 7, 32, 12]], ![![106, 19, 13, 35, 24]], ![![54, 10, 7, 18, 13]]]
  g := ![![![1, 2, 2, -2, 0], ![0, -3, -4, 10, -12], ![-36, -28, -21, -8, 60], ![-2, -5, -5, 5, 0], ![18, 16, 13, -2, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [49, 58, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 30, 18], [31, 30, 43], [0, 1]]
 g := ![![[44, 27, 57], [7, 13], [50, 43, 56], [47, 23, 39], [1]], ![[60, 36, 0, 40], [7, 22], [46, 24, 52, 30], [23, 0, 19, 30], [49, 55, 6, 37]], ![[31, 37, 5, 29], [10, 4], [28, 38, 4, 33], [31, 12, 27, 50], [41, 6, 59, 24]]]
 h' := ![![[40, 30, 18], [1, 47, 39], [51, 37, 14], [15, 12, 42], [12, 3, 10], [0, 1]], ![[31, 30, 43], [24, 13, 3], [1, 47, 49], [53, 38, 12], [50, 54, 49], [40, 30, 18]], ![[0, 1], [7, 1, 19], [3, 38, 59], [35, 11, 7], [27, 4, 2], [31, 30, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 18], []]
 b := ![[], [35, 41, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [49, 58, 51, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-130885965, 12701664, 9591150, -39907954, 22997632]
  a := ![10, 24, 24, -50, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14731331, 23926890, 27823428, -39907954, 22997632]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 0, 0, -2, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-5, 0, 0, -2, 0]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![21, 5, 1, 0, 0], ![33, 0, 0, 1, 0], ![25, 54, 0, 0, 1]] where
  M :=![![![-5, 0, 0, -2, 0], ![-4, -7, -6, -2, -12], ![-100, -12, -7, -32, -12], ![-88, -52, -38, -33, -72], ![-40, -10, -8, -14, -13]]]
  hmulB := by decide  
  f := ![![![39, -8, -4, 2, 0]], ![![4, 45, 2, -10, 12]], ![![15, 1, -1, 0, 0]], ![![19, -4, -2, 1, 0]], ![![19, 36, 0, -8, 11]]]
  g := ![![![1, 0, 0, -2, 0], ![8, 11, -6, -2, -12], ![23, 11, -7, -32, -12], ![59, 66, -38, -33, -72], ![15, 12, -8, -14, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [37, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 60], [0, 1]]
 g := ![![[16, 15], [25], [30, 56], [40, 19], [18, 1]], ![[42, 46], [25], [1, 5], [16, 42], [36, 60]]]
 h' := ![![[18, 60], [12, 25], [49, 5], [45, 42], [5, 43], [0, 1]], ![[0, 1], [35, 36], [17, 56], [8, 19], [47, 18], [18, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [41, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [37, 43, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5413, 4706, 3835, -2577, 6764]
  a := ![3, 8, 8, -15, 8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2787, -6225, 3835, -2577, 6764]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-39, 8, 4, -2, 0]] ![![-5, 0, 0, -2, 0]]
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


lemma PB696I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB696I1 : PrimesBelowBoundCertificateInterval O 23 61 696 where
  m := 9
  g := ![2, 4, 1, 3, 2, 3, 1, 1, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB696I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1, I31N2, I31N3]
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0]
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
    · exact ![24389, 841]
    · exact ![961, 31, 31, 31]
    · exact ![69343957]
    · exact ![1681, 1681, 41]
    · exact ![79507, 1849]
    · exact ![103823, 47, 47]
    · exact ![418195493]
    · exact ![714924299]
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
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
      exact NI31N3
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
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
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I31N1, I31N2, I31N3, I41N2, I47N1, I47N2]
  Il := ![[], [I31N1, I31N2, I31N3], [], [I41N2], [], [I47N1, I47N2], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
