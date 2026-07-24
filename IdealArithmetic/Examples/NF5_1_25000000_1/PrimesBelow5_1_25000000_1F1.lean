
import IdealArithmetic.Examples.NF5_1_25000000_1.RI5_1_25000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -3, 3, 2, 5]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-9, -3, 3, 2, 5]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![22, 25, 1, 0, 0], ![11, 11, 0, 1, 0], ![27, 9, 0, 0, 1]] where
  M :=![![![-9, -3, 3, 2, 5], ![-24, -10, -5, -8, 29], ![-100, -13, 12, -38, 31], ![44, 6, 36, 65, -66], ![-16, -14, 6, 16, 17]]]
  hmulB := by decide  
  f := ![![![2295, -2637, -77, -724, 1153]], ![![-3164, 3666, 105, 1006, -1609]], ![![-834, 985, 27, 270, -436]], ![![-431, 507, 14, 139, -224]], ![![1181, -1347, -40, -370, 587]]]
  g := ![![![-8, -5, 3, 2, 5], ![-21, -2, -5, -8, 29], ![-27, -6, 12, -38, 31], ![11, -35, 36, 65, -66], ![-27, -17, 6, 16, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [17, 19, 1] where
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
 g := ![![[25, 23], [23], [12, 16], [10, 1]], ![[23, 6], [23], [27, 13], [20, 28]]]
 h' := ![![[10, 28], [16, 9], [28, 9], [4, 25], [0, 1]], ![[0, 1], [19, 20], [2, 20], [22, 4], [10, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [13, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [17, 19, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-37913, -4647, -25011, -50068, 46823]
  a := ![26, 17, 31, 30, -91]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6936, 25861, -25011, -50068, 46823]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, -13, 3, 0, 22]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-31, -13, 3, 0, 22]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![22, 17, 1, 0, 0], ![26, 12, 0, 1, 0], ![18, 5, 0, 0, 1]] where
  M :=![![![-31, -13, 3, 0, 22], ![-88, -28, -7, -32, 66], ![-200, -31, 86, 0, -26], ![148, -6, -6, 107, -23], ![-60, -44, -20, -6, 91]]]
  hmulB := by decide  
  f := ![![![51621, -59525, -1723, -16340, 26070]], ![![-71600, 82578, 2389, 22668, -36170]], ![![614, -699, -21, -192, 304]], ![![14370, -16564, -480, -4547, 7253]], ![![20278, -23380, -677, -6418, 10239]]]
  g := ![![![-17, -6, 3, 0, 22], ![-10, 5, -7, -32, 66], ![-56, -47, 86, 0, -26], ![-72, -37, -6, 107, -23], ![-38, -3, -20, -6, 91]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [7, 19, 1] where
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
 g := ![![[11, 25], [20], [13, 7], [10, 1]], ![[0, 4], [20], [25, 22], [20, 28]]]
 h' := ![![[10, 28], [21, 24], [25, 22], [17, 6], [0, 1]], ![[0, 1], [0, 5], [13, 7], [19, 23], [10, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [9, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal' SI29N1 29 where
  n := 2
  hpos := by decide
  P := [7, 19, 1]
  hirr := P29P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2308823, -826117, -2911741, -3899474, 5401507]
  a := ![239, 117, 236, 172, -835]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2272713, 2360677, -2911741, -3899474, 5401507]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N1 B_one_repr
lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 37, -29, 10, -96]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![151, 37, -29, 10, -96]] 
 ![![29, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![151, 37, -29, 10, -96], ![364, 102, -61, 26, -218], ![820, 251, -124, 62, -472], ![-60, -8, 16, -3, 45], ![548, 172, -80, 42, -311]]]
  hmulB := by decide  
  f := ![![![-13, 33, 17, 34, -40]], ![![-4, 16, 7, 18, -18]], ![![-17, 8, -1, -8, 0]], ![![-1, 21, 25, 37, -47]], ![![-6, 30, 18, 38, -41]]]
  g := ![![![70, 37, -29, 10, -96], ![147, 102, -61, 26, -218], ![298, 251, -124, 62, -472], ![-39, -8, 16, -3, 45], ![192, 172, -80, 42, -311]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-9, -3, 3, 2, 5]] ![![-31, -13, 3, 0, 22]]
  ![![-61, -124, 140, 280, -65]] where
 M := ![![![-61, -124, 140, 280, -65]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-61, -124, 140, 280, -65]] ![![151, 37, -29, 10, -96]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![8033, 6815, 1653, 1276, -377]]]
 hmul := by decide  
 g := ![![![![277, 235, 57, 44, -13]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, 5, 27, 40, -45]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![21, 5, 27, 40, -45]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![5, 29, 1, 0, 0], ![0, 17, 0, 1, 0], ![17, 20, 0, 0, 1]] where
  M :=![![![21, 5, 27, 40, -45], ![100, -32, -101, -2, 145], ![-576, 3, -226, -684, 421], ![184, 148, 710, 761, -1128], ![264, 10, 146, 348, -259]]]
  hmulB := by decide  
  f := ![![![-5209, 6013, 177, 1650, -2627]], ![![7208, -8332, -233, -2288, 3669]], ![![5577, -6452, -178, -1772, 2847]], ![![4168, -4818, -135, -1323, 2121]], ![![1737, -2015, -51, -554, 900]]]
  g := ![![![21, -18, 27, 40, -45], ![-60, 1, -101, -2, 145], ![-213, 315, -226, -684, 421], ![510, -349, 710, 761, -1128], ![127, -160, 146, 348, -259]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [19, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 30], [0, 1]]
 g := ![![[25, 18], [20, 2], [14, 20], [21, 1]], ![[0, 13], [0, 29], [0, 11], [11, 30]]]
 h' := ![![[21, 30], [23, 24], [13, 23], [4, 19], [0, 1]], ![[0, 1], [0, 7], [0, 8], [0, 12], [21, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [28, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [19, 10, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17382, -3708, -15938, -25992, 29304]
  a := ![19, 11, 21, 18, -66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14060, 10138, -15938, -25992, 29304]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, -36, 4, -8, 34]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-79, -36, 4, -8, 34]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![26, 8, 1, 0, 0], ![28, 10, 0, 1, 0], ![24, 4, 0, 0, 1]] where
  M :=![![![-79, -36, 4, -8, 34], ![-120, -59, 4, -12, 46], ![-160, -92, -3, -16, 54], ![64, 28, -8, 1, -26], ![-88, -52, -4, -12, 25]]]
  hmulB := by decide  
  f := ![![![607, -700, -20, -192, 306]], ![![-840, 971, 28, 268, -426]], ![![330, -380, -11, -104, 166]], ![![252, -290, -8, -79, 126]], ![![368, -424, -12, -116, 185]]]
  g := ![![![-25, -4, 4, -8, 34], ![-32, -5, 4, -12, 46], ![-30, -4, -3, -16, 54], ![28, 6, -8, 1, -26], ![-8, 0, -4, -12, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [12, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 30], [0, 1]]
 g := ![![[21, 9], [15, 25], [10, 16], [27, 1]], ![[16, 22], [8, 6], [8, 15], [23, 30]]]
 h' := ![![[27, 30], [6, 28], [4, 26], [17, 4], [0, 1]], ![[0, 1], [18, 3], [24, 5], [1, 27], [27, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [4, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [12, 4, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-576701, -121597, -509042, -838551, 954246]
  a := ![-107, -61, -118, -103, 375]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![426965, 274815, -509042, -838551, 954246]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-487, -118, 94, -32, 310]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![-487, -118, 94, -32, 310]] 
 ![![31, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![-487, -118, 94, -32, 310], ![-1176, -329, 198, -84, 706], ![-2656, -810, 403, -200, 1530], ![192, 24, -52, 9, -144], ![-1776, -556, 260, -136, 1009]]]
  hmulB := by decide  
  f := ![![![-1145, 1314, 46, 360, -586]], ![![-871, 1001, 36, 276, -448]], ![![-1030, 1182, 35, 320, -518]], ![![-404, 456, 20, 121, -208]], ![![-530, 608, 24, 168, -275]]]
  g := ![![![-127, -118, 94, -32, 310], ![-225, -329, 198, -84, 706], ![-384, -810, 403, -200, 1530], ![92, 24, -52, 9, -144], ![-230, -556, 260, -136, 1009]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![21, 5, 27, 40, -45]] ![![-79, -36, 4, -8, 34]]
  ![![-59, -75, -117, -80, 237]] where
 M := ![![![-59, -75, -117, -80, 237]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-59, -75, -117, -80, 237]] ![![-487, -118, 94, -32, 310]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-8587, -7285, -1767, -1364, 403]]]
 hmul := by decide  
 g := ![![![![-277, -235, -57, -44, 13]]]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 6, -12, 2, -34]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![53, 6, -12, 2, -34]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![36, 34, 1, 0, 0], ![9, 27, 0, 1, 0], ![20, 9, 0, 0, 1]] where
  M :=![![![53, 6, -12, 2, -34], ![132, 37, -26, 10, -88], ![332, 86, -55, 22, -194], ![-16, 6, 6, 1, 12], ![224, 64, -36, 16, -131]]]
  hmulB := by decide  
  f := ![![![9, -2, 4, 10, -6]], ![![4, -7, -34, -22, 52]], ![![8, -8, -27, -14, 42]], ![![9, -5, -20, -7, 30]], ![![8, -3, -6, 2, 9]]]
  g := ![![![31, 18, -12, 2, -34], ![74, 39, -26, 10, -88], ![162, 84, -55, 22, -194], ![-13, -9, 6, 1, 12], ![108, 55, -36, 16, -131]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [25, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 36], [0, 1]]
 g := ![![[21, 3], [10], [26, 12], [12], [1]], ![[0, 34], [10], [16, 25], [12], [1]]]
 h' := ![![[30, 36], [6, 22], [16, 26], [29, 7], [12, 30], [0, 1]], ![[0, 1], [0, 15], [19, 11], [17, 30], [24, 7], [30, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [19, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [25, 7, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-94285, 2746, -18526, -93670, 42529]
  a := ![35, 28, 52, 60, -123]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![15273, 75107, -18526, -93670, 42529]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, -212, -8, -62, 96]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![181, -212, -8, -62, 96]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![20, 0, 1, 0, 0], ![27, 33, 0, 1, 0], ![26, 6, 0, 0, 1]] where
  M :=![![![181, -212, -8, -62, 96], ![-260, 297, 20, 86, -146], ![412, -412, -7, -58, 164], ![-276, 262, -50, -9, -24], ![32, -68, -8, -48, 43]]]
  hmulB := by decide  
  f := ![![![-1559, -792, 28, -166, 592]], ![![-2036, -1199, -72, -242, 614]], ![![-896, -472, 5, -98, 324]], ![![-2913, -1629, -46, -333, 962]], ![![-1446, -774, 0, -160, 511]]]
  g := ![![![-13, 34, -8, -62, 96], ![22, -45, 20, 86, -146], ![-58, 14, -7, -58, 164], ![43, 19, -50, -9, -24], ![10, 34, -8, -48, 43]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P1 : CertificateIrreducibleZModOfList' 37 2 2 5 [16, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 36], [0, 1]]
 g := ![![[2, 7], [34], [36, 4], [25], [1]], ![[0, 30], [34], [19, 33], [25], [1]]]
 h' := ![![[5, 36], [8, 28], [16, 21], [4, 2], [21, 5], [0, 1]], ![[0, 1], [0, 9], [10, 16], [14, 35], [9, 32], [5, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [16, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N1 : CertifiedPrimeIdeal' SI37N1 37 where
  n := 2
  hpos := by decide
  P := [16, 32, 1]
  hirr := P37P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-83000, 16132, 39832, -37636, -51632]
  a := ![-28, -30, -56, -78, 98]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![39972, 42376, 39832, -37636, -51632]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N1 B_one_repr
lemma NI37N1 : Nat.card (O ⧸ I37N1) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45, -18, 4, -4, 22]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-45, -18, 4, -4, 22]] 
 ![![37, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-45, -18, 4, -4, 22], ![-80, -33, 6, -8, 38], ![-136, -58, 11, -12, 58], ![36, 12, -4, 5, -16], ![-80, -36, 4, -8, 37]]]
  hmulB := by decide  
  f := ![![![-1449, 1674, 48, 460, -734]], ![![-63, 73, 2, 20, -32]], ![![-1172, 1354, 39, 372, -594]], ![![-1085, 1254, 36, 345, -550]], ![![-365, 422, 12, 116, -185]]]
  g := ![![![-5, -18, 4, -4, 22], ![-7, -33, 6, -8, 38], ![-12, -58, 11, -12, 58], ![3, 12, -4, 5, -16], ![-5, -36, 4, -8, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![53, 6, -12, 2, -34]] ![![181, -212, -8, -62, 96]]
  ![![1449, -1674, -48, -460, 734]] where
 M := ![![![1449, -1674, -48, -460, 734]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![1449, -1674, -48, -460, 734]] ![![-45, -18, 4, -4, 22]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [5, 29, 13, 5, 10, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 16, 23, 19, 38], [3, 21, 26, 27, 25], [37, 19, 5, 1, 3], [26, 25, 28, 35, 16], [0, 1]]
 g := ![![[7, 26, 25], [7, 37, 36, 16], [28, 11, 2, 18], [1], []], ![[0, 32, 25, 0, 35, 14, 39, 6], [5, 12, 29, 4], [25, 29, 40, 1], [37, 34, 14, 5, 40, 27, 40, 12], [1, 4, 1, 9]], ![[33, 12, 26, 35, 3, 23, 22, 23], [8, 38, 4, 2], [4, 18, 11, 36], [4, 22, 17, 25, 40, 1, 21, 25], [14, 16, 20, 10]], ![[5, 37, 39, 1, 25, 17, 28, 29], [14, 36, 18, 33], [37, 22, 28, 33], [14, 14, 15, 3, 39, 36, 29, 3], [39, 6, 39, 9]], ![[26, 19, 35, 4, 28, 13, 25, 37], [17, 18], [12, 35, 28, 16], [25, 18, 8, 10, 31, 34, 37, 18], [18, 30, 36, 10]]]
 h' := ![![[6, 16, 23, 19, 38], [29, 15, 38, 36], [8, 38, 32, 4, 4], [36, 12, 28, 36, 31], [0, 0, 1], [0, 1]], ![[3, 21, 26, 27, 25], [12, 18, 3, 6, 11], [23, 20, 24, 34, 39], [5, 7, 7, 25, 1], [31, 20, 29, 13, 18], [6, 16, 23, 19, 38]], ![[37, 19, 5, 1, 3], [32, 7, 10, 16, 23], [20, 22, 27, 20, 17], [32, 1, 16, 34, 35], [21, 9, 15, 18, 1], [3, 21, 26, 27, 25]], ![[26, 25, 28, 35, 16], [10, 27, 18, 16, 23], [11, 26, 15, 34, 22], [14, 30, 28, 31, 19], [26, 40, 19, 4, 40], [37, 19, 5, 1, 3]], ![[0, 1], [28, 15, 13, 8, 25], [20, 17, 25, 31], [11, 32, 3, 38, 37], [12, 13, 18, 6, 23], [26, 25, 28, 35, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 8, 20, 32], [], [], []]
 b := ![[], [37, 27, 32, 26, 38], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [5, 29, 13, 5, 10, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54439037734601, -6511396816090, -5879498382944, 41334981930180, 2649265660789]
  a := ![17, 23, 43, 61, -53]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1327781408161, -158814556490, -143402399584, 1008170290980, 64616235629]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 5 2 5 [6, 0, 4, 0, 41, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 40, 3, 11, 21], [4, 17, 17, 18, 3], [6, 32, 20, 8, 41], [20, 39, 3, 6, 21], [0, 1]]
 g := ![![[19, 32, 12, 14, 40], [4, 18, 2, 21, 24], [27, 0, 8, 4], [1], []], ![[42, 9, 38, 0, 5, 30, 41, 41], [31, 33, 35, 10, 3, 11, 12, 31], [35, 2, 20, 25], [28, 31, 17, 36, 6, 6, 39, 16], [4, 11, 11, 11]], ![[3, 5, 14, 21, 8, 11, 29, 30], [23, 31, 1, 17, 22, 28, 34, 28], [21, 27, 7, 38], [17, 9, 35, 9, 21, 34, 32, 7], [13, 33, 40, 9]], ![[9, 9, 13, 30, 31, 7, 41, 16], [34, 42, 4, 9, 21, 12, 32, 14], [13, 11, 42, 41], [8, 32, 41, 2, 16, 3, 18, 36], [5, 22, 19, 4]], ![[30, 0, 31, 14, 20, 41, 32, 41], [16, 20, 31, 30, 7, 5, 33, 14], [25, 1, 26, 10], [16, 27, 21, 21, 0, 13], [40, 22, 16, 11]]]
 h' := ![![[15, 40, 3, 11, 21], [19, 30, 15, 14, 13], [3, 0, 21, 19, 14], [37, 0, 39, 0, 2], [0, 0, 1], [0, 1]], ![[4, 17, 17, 18, 3], [30, 8, 29, 21, 2], [18, 24, 29, 4, 14], [20, 31, 9, 3, 38], [29, 16, 17, 30, 21], [15, 40, 3, 11, 21]], ![[6, 32, 20, 8, 41], [7, 30, 25, 1, 15], [41, 23, 23, 14, 9], [9, 27, 6, 11, 34], [24, 24, 4, 20, 17], [4, 17, 17, 18, 3]], ![[20, 39, 3, 6, 21], [27, 33, 16, 13, 11], [24, 10, 33, 24, 37], [39, 12, 35, 12, 27], [6, 37, 12, 17, 5], [6, 32, 20, 8, 41]], ![[0, 1], [40, 28, 1, 37, 2], [14, 29, 23, 25, 12], [32, 16, 40, 17, 28], [31, 9, 9, 19], [20, 39, 3, 6, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 12, 35, 33], [], [], []]
 b := ![[], [38, 34, 29, 14, 23], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 5
  hpos := by decide
  P := [6, 0, 4, 0, 41, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![39011701152, 2162545164, 25031628528, 54494416688, -43667281697]
  a := ![-1, -5, -8, -15, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![907248864, 50291748, 582130896, 1267312016, -1015518179]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2581, 2980, 86, 818, -1306]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-2581, 2980, 86, 818, -1306]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![36, 41, 1, 0, 0], ![36, 15, 0, 1, 0], ![36, 25, 0, 0, 1]] where
  M :=![![![-2581, 2980, 86, 818, -1306], ![3588, -4131, -120, -1134, 1808], ![-4964, 5736, 165, 1574, -2514], ![3312, -3822, -110, -1049, 1674], ![-840, 976, 28, 268, -429]]]
  hmulB := by decide  
  f := ![![![-59, -16, 6, -10, 38]], ![![-132, -33, 36, -2, 44]], ![![-164, -43, 37, -8, 70]], ![![-88, -23, 14, -11, 46]], ![![-120, -31, 24, -10, 55]]]
  g := ![![![253, 422, 86, 818, -1306], ![-348, -583, -120, -1134, 1808], ![488, 813, 165, 1574, -2514], ![-324, -541, -110, -1049, 1674], ![84, 139, 28, 268, -429]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [4, 31, 1] where
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
 g := ![![[43, 12], [2, 3], [24, 7], [20, 21], [1]], ![[0, 35], [3, 44], [42, 40], [27, 26], [1]]]
 h' := ![![[16, 46], [39, 24], [45, 35], [14, 17], [43, 16], [0, 1]], ![[0, 1], [0, 23], [41, 12], [4, 30], [17, 31], [16, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [22, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [4, 31, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-133714, -8596, -59046, -153708, 120369]
  a := ![-45, -32, -57, -62, 159]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![67918, 36355, -59046, -153708, 120369]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-999, 166, 308, -588, -360]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-999, 166, 308, -588, -360]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![29, 16, 1, 0, 0], ![34, 6, 0, 1, 0], ![9, 11, 0, 0, 1]] where
  M :=![![![-999, 166, 308, -588, -360], ![2616, 485, 3134, 4892, -5196], ![11000, -4034, -12815, -1532, 18656], ![-24044, 2208, -260, -20685, 3282], ![-6392, 1896, 5536, -732, -7861]]]
  hmulB := by decide  
  f := ![![![604647, -696962, -20192, -191324, 305192]], ![![-838120, 967103, 27950, 265468, -423692]], ![![112525, -129348, -3771, -35512, 56568]], ![![313910, -361702, -10488, -99293, 158358]], ![![-76159, 88037, 2534, 24164, -38601]]]
  g := ![![![283, 58, 308, -588, -360], ![-4422, -465, 3134, 4892, -5196], ![5677, 106, -12815, -1532, 18656], ![13984, 2008, -260, -20685, 3282], ![-1517, 89, 5536, -732, -7861]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [29, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 46], [0, 1]]
 g := ![![[9, 12], [10, 36], [17, 14], [6, 18], [1]], ![[26, 35], [14, 11], [29, 33], [8, 29], [1]]]
 h' := ![![[21, 46], [39, 24], [24, 6], [14, 22], [18, 21], [0, 1]], ![[0, 1], [26, 23], [9, 41], [6, 25], [36, 26], [21, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [30, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [29, 26, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-38198, -1143, -13858, -42341, 28668]
  a := ![-23, -17, -32, -35, 81]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![32878, 3389, -13858, -42341, 28668]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, -118, -6, -30, 50]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![27, -118, -6, -30, 50]] 
 ![![47, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![41, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![27, -118, -6, -30, 50], ![-140, 81, -10, 26, -60], ![188, -202, -43, -50, 2], ![-36, 142, 2, 37, -72], ![80, -40, -28, -8, -47]]]
  hmulB := by decide  
  f := ![![![-59, 102, 414, 302, -638]], ![![-5, 75, 320, 268, -498]], ![![-129, 64, 223, 80, -332]], ![![-122, 82, 302, 153, -456]], ![![14, 36, 160, 148, -251]]]
  g := ![![![97, -118, -6, -30, 50], ![-53, 81, -10, 26, -60], ![215, -202, -43, -50, 2], ![-110, 142, 2, 37, -72], ![70, -40, -28, -8, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-2581, 2980, 86, 818, -1306]] ![![-999, 166, 308, -588, -360]]
  ![![59, -102, -414, -302, 638]] where
 M := ![![![59, -102, -414, -302, 638]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![59, -102, -414, -302, 638]] ![![27, -118, -6, -30, 50]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, 17, 63, 28, -94]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-31, 17, 63, 28, -94]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![3, 29, 1, 0, 0], ![43, 28, 0, 1, 0], ![5, 40, 0, 0, 1]] where
  M :=![![![-31, 17, 63, 28, -94], ![320, -24, 31, 300, -86], ![-256, -249, -1162, -1204, 1842], ![-1192, 378, 1134, -51, -1625], ![28, 132, 580, 518, -907]]]
  hmulB := by decide  
  f := ![![![10173, -11719, -347, -3216, 5114]], ![![-14024, 16258, 451, 4464, -7170]], ![![-6725, 7808, 214, 2144, -3450]], ![![599, -635, -35, -173, 237]], ![![-9559, 11093, 305, 3046, -4899]]]
  g := ![![![-18, 22, 63, 28, -94], ![-231, -111, 31, 300, -86], ![864, -123, -1162, -1204, 1842], ![108, 640, 1134, -51, -1625], ![-367, 96, 580, 518, -907]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [27, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 52], [0, 1]]
 g := ![![[41, 52], [13], [39, 11], [28], [6, 1]], ![[35, 1], [13], [52, 42], [28], [12, 52]]]
 h' := ![![[6, 52], [16, 23], [7, 15], [48, 8], [50, 9], [0, 1]], ![[0, 1], [48, 30], [44, 38], [43, 45], [51, 44], [6, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [22, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [27, 47, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-213, 664, 3278, 3218, -4117]
  a := ![2, 5, 9, 15, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2412, -374, 3278, 3218, -4117]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-125, -29, 25, -8, 81]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-125, -29, 25, -8, 81]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![21, 47, 1, 0, 0], ![21, 26, 0, 1, 0], ![32, 25, 0, 0, 1]] where
  M :=![![![-125, -29, 25, -8, 81], ![-308, -84, 53, -22, 187], ![-704, -211, 110, -52, 407], ![48, 4, -14, 3, -36], ![-472, -146, 70, -36, 271]]]
  hmulB := by decide  
  f := ![![![203, -231, -7, -62, 101]], ![![-280, 320, 3, 80, -131]], ![![-161, 184, 0, 44, -73]], ![![-61, 71, -1, 17, -27]], ![![-8, 10, -3, 0, 0]]]
  g := ![![![-58, -57, 25, -8, 81], ![-131, -126, 53, -22, 187], ![-282, -268, 110, -52, 407], ![27, 28, -14, 3, -36], ![-186, -175, 70, -36, 271]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [23, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 52], [0, 1]]
 g := ![![[27, 38], [36], [51, 40], [47], [15, 1]], ![[14, 15], [36], [15, 13], [47], [30, 52]]]
 h' := ![![[15, 52], [16, 41], [46, 47], [19, 26], [26, 43], [0, 1]], ![[0, 1], [48, 12], [9, 6], [38, 27], [35, 10], [15, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [30, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [23, 38, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-971330, -72586, -487118, -1168234, 948808]
  a := ![127, 90, 156, 164, -441]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![64702, 556148, -487118, -1168234, 948808]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![461, 227, -13, 48, -182]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![461, 227, -13, 48, -182]] 
 ![![53, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![461, 227, -13, 48, -182], ![632, 352, 9, 72, -210], ![696, 497, 82, 96, -126], ![-428, -190, 26, -41, 189], ![308, 268, 68, 50, -9]]]
  hmulB := by decide  
  f := ![![![5169, -5957, -179, -1636, 2618]], ![![2790, -3216, -97, -884, 1414]], ![![285, -328, -7, -88, 140]], ![![951, -1093, -35, -299, 483]], ![![1495, -1723, -53, -474, 759]]]
  g := ![![![-78, 227, -13, 48, -182], ![-143, 352, 9, 72, -210], ![-254, 497, 82, 96, -126], ![54, -190, 26, -41, 189], ![-155, 268, 68, 50, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-31, 17, 63, 28, -94]] ![![-125, -29, 25, -8, 81]]
  ![![-1, 14, 84, 66, -173]] where
 M := ![![![-1, 14, 84, 66, -173]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![-1, 14, 84, 66, -173]] ![![461, 227, -13, 48, -182]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-14681, -12455, -3021, -2332, 689]]]
 hmul := by decide  
 g := ![![![![-277, -235, -57, -44, 13]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 5 2 5 [44, 9, 46, 8, 43, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 26, 56, 11, 52], [15, 35, 19, 33, 29], [53, 58, 7, 15, 10], [16, 57, 36, 0, 27], [0, 1]]
 g := ![![[23, 35, 41, 26, 3], [44, 4, 42, 25, 1], [26, 44, 42, 29], [12, 16, 1], []], ![[49, 48, 41, 1, 41, 19, 0, 13], [27, 20, 2, 0, 56, 36, 41, 44], [45, 29, 15, 51], [49, 26, 25, 13, 23, 24, 42, 44], [35, 3, 57, 19, 23, 12, 23, 11]], ![[13, 41, 51, 50, 9, 37, 25, 27], [9, 16, 21, 5, 45, 14, 35, 22], [44, 16, 46, 28], [2, 22, 21, 29, 37, 18, 33, 57], [1, 7, 34, 16, 32, 29, 8, 22]], ![[28, 9, 4, 34, 25, 12, 34, 39], [38, 51, 29, 34, 32, 16, 50, 56], [55, 42, 30, 45], [37, 50, 44, 33, 31, 29, 27, 33], [43, 43, 44, 36, 14, 43, 27, 56]], ![[11, 6, 38, 0, 49, 55, 56, 7], [3, 26, 22, 13, 26, 8, 13, 19], [1, 1, 47, 19], [6, 48, 13, 52, 12, 52, 31, 22], [31, 38, 51, 2, 53, 45, 45, 36]]]
 h' := ![![[50, 26, 56, 11, 52], [11, 37, 43, 58, 11], [45, 38, 45, 25, 58], [3, 14, 27, 44, 18], [0, 0, 0, 1], [0, 1]], ![[15, 35, 19, 33, 29], [32, 11, 3, 28, 30], [15, 45, 45, 10, 45], [15, 30, 24, 35, 13], [32, 30, 2, 38, 45], [50, 26, 56, 11, 52]], ![[53, 58, 7, 15, 10], [9, 13, 22, 17, 51], [33, 34, 24, 28, 29], [50, 55, 42, 18, 38], [27, 3, 29, 55, 57], [15, 35, 19, 33, 29]], ![[16, 57, 36, 0, 27], [21, 39, 4, 27, 23], [11, 23, 29, 43, 49], [22, 35, 26, 7, 35], [16, 32, 36, 47, 27], [53, 58, 7, 15, 10]], ![[0, 1], [35, 18, 46, 47, 3], [13, 37, 34, 12, 55], [23, 43, 58, 14, 14], [18, 53, 51, 36, 48], [16, 57, 36, 0, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 41, 23, 56], [], [], []]
 b := ![[], [30, 52, 5, 48, 8], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 5
  hpos := by decide
  P := [44, 9, 46, 8, 43, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-80117562255469, 2141087531266, -23184787345538, -87900305810772, 45717388360440]
  a := ![31, 23, 39, 42, -108]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1357924783991, 36289619174, -392962497382, -1489835691708, 774870989160]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-987, -233, -1395, -2026, 2292]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-987, -233, -1395, -2026, 2292]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![25, 44, 1, 0, 0], ![48, 19, 0, 1, 0], ![24, 13, 0, 0, 1]] where
  M :=![![![-987, -233, -1395, -2026, 2292], ![-5116, 1670, 5081, -34, -7306], ![29292, 33, 11968, 35106, -22156], ![-8764, -7672, -36368, -38381, 57723], ![-13284, -532, -7640, -17802, 13495]]]
  hmulB := by decide  
  f := ![![![848689, -978949, -28329, -268722, 428780]], ![![-1177676, 1357804, 39281, 372734, -594714]], ![![-474871, 547308, 15829, 150248, -239720]], ![![283156, -326812, -9461, -89705, 143145]], ![![87480, -101040, -2927, -27732, 44255]]]
  g := ![![![1248, 1145, -1395, -2026, 2292], ![735, -2070, 5081, -34, -7306], ![-23332, -14845, 11968, 35106, -22156], ![22252, 25760, -36368, -38381, 57723], ![11612, 8171, -7640, -17802, 13495]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [23, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 60], [0, 1]]
 g := ![![[10, 1], [56], [24, 41], [32, 39], [14, 1]], ![[24, 60], [56], [49, 20], [29, 22], [28, 60]]]
 h' := ![![[14, 60], [2, 60], [58, 19], [57, 23], [44, 51], [0, 1]], ![[0, 1], [49, 1], [19, 42], [13, 38], [26, 10], [14, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [6, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [23, 47, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-83, -8979, -18193, -7618, 38235]
  a := ![-17, -5, -8, 4, 61]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1594, 7200, -18193, -7618, 38235]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -9, 1, 0, 2]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![9, -9, 1, 0, 2]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![34, 39, 1, 0, 0], ![48, 36, 0, 1, 0], ![18, 37, 0, 0, 1]] where
  M :=![![![9, -9, 1, 0, 2], ![-8, 10, -7, 0, 6], ![-24, -15, -4, -40, 18], ![16, 18, 38, 57, -67], ![20, -4, 4, 18, -7]]]
  hmulB := by decide  
  f := ![![![109, 7, -33, 4, -86]], ![![336, 68, -75, 20, -230]], ![![290, 51, -69, 16, -204]], ![![284, 46, -70, 15, -203]], ![![246, 46, -57, 14, -171]]]
  g := ![![![-1, -2, 1, 0, 2], ![2, 1, -7, 0, 6], ![28, 15, -4, -40, 18], ![-46, -17, 38, 57, -67], ![-14, -9, 4, 18, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P1 : CertificateIrreducibleZModOfList' 61 2 2 5 [3, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 60], [0, 1]]
 g := ![![[3, 41], [49], [18, 9], [25, 45], [52, 1]], ![[0, 20], [49], [59, 52], [47, 16], [43, 60]]]
 h' := ![![[52, 60], [24, 23], [7, 7], [47, 3], [27, 17], [0, 1]], ![[0, 1], [0, 38], [5, 54], [20, 58], [57, 44], [52, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [37, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N1 : CertifiedPrimeIdeal' SI61N1 61 where
  n := 2
  hpos := by decide
  P := [3, 9, 1]
  hirr := P61P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-525029, 19068, -88624, -510342, 213451]
  a := ![83, 68, 123, 144, -289]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![379385, 228689, -88624, -510342, 213451]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N1 B_one_repr
lemma NI61N1 : Nat.card (O ⧸ I61N1) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-239, 276, 8, 76, -121]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-239, 276, 8, 76, -121]] 
 ![![61, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![56, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![-239, 276, 8, 76, -121], ![332, -383, -12, -106, 169], ![-464, 532, 17, 144, -235], ![312, -354, -8, -91, 151], ![-76, 90, 2, 26, -39]]]
  hmulB := by decide  
  f := ![![![-2087, -798, 210, -182, 1047]], ![![-1397, -535, 140, -122, 700]], ![![-248, -98, 23, -22, 121]], ![![-1892, -724, 190, -165, 949]], ![![-752, -290, 74, -66, 375]]]
  g := ![![![-211, 276, 8, 76, -121], ![293, -383, -12, -106, 169], ![-404, 532, 17, 144, -235], ![266, -354, -8, -91, 151], ![-70, 90, 2, 26, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-987, -233, -1395, -2026, 2292]] ![![9, -9, 1, 0, 2]]
  ![![39885, -18158, -61596, -18426, 91216]] where
 M := ![![![39885, -18158, -61596, -18426, 91216]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![39885, -18158, -61596, -18426, 91216]] ![![-239, 276, 8, 76, -121]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![338245, -74054, -180316, 134566, 240523]]]
 hmul := by decide  
 g := ![![![![5545, -1214, -2956, 2206, 3943]]]]
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


lemma PB312I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB312I1 : PrimesBelowBoundCertificateInterval O 23 61 312 where
  m := 9
  g := ![3, 3, 3, 1, 1, 3, 3, 1, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB312I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1, I47N2]
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
    · exact ![841, 841, 29]
    · exact ![961, 961, 31]
    · exact ![1369, 1369, 37]
    · exact ![115856201]
    · exact ![147008443]
    · exact ![2209, 2209, 47]
    · exact ![2809, 2809, 53]
    · exact ![714924299]
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
      exact NI31N1
      exact NI31N2
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
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
  β := ![I29N2, I31N2, I37N2, I47N2, I53N2, I61N2]
  Il := ![[I29N2], [I31N2], [I37N2], [], [], [I47N2], [I53N2], [], [I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
