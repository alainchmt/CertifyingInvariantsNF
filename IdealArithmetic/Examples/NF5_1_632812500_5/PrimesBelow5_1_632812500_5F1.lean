
import IdealArithmetic.Examples.NF5_1_632812500_5.RI5_1_632812500_5
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


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [20, 18, 13, 28, 26, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 3, 21, 25, 27], [20, 3, 7, 5, 5], [6, 22, 8, 7, 2], [24, 0, 22, 21, 24], [0, 1]]
 g := ![![[27, 1, 25, 16, 28], [5, 7, 16, 23], [10, 3, 1], []], ![[17, 26, 16, 1, 22, 25, 23, 19], [20, 11, 17, 22], [19, 22, 22, 4, 24, 28, 16, 18], [18, 9, 21, 15, 25, 19, 15, 21]], ![[16, 12, 5, 26, 5, 20, 14, 4], [16, 10, 5, 28], [19, 3, 20, 20, 27, 25, 2, 24], [3, 9, 26, 15, 26, 27, 25, 9]], ![[15, 8, 28, 7, 0, 8, 20, 15], [2, 18, 23, 22], [1, 25, 10, 10, 21, 13, 15, 26], [13, 21, 21, 9, 27, 26, 21, 8]], ![[16, 3, 20, 23, 13, 23, 23, 9], [7, 0, 14, 6], [22, 22, 8, 21, 24, 22, 19, 20], [24, 17, 7, 21, 20, 18, 11, 20]]]
 h' := ![![[11, 3, 21, 25, 27], [25, 12, 11, 2, 12], [3, 21, 28, 11, 20], [0, 0, 0, 1], [0, 1]], ![[20, 3, 7, 5, 5], [26, 23, 14, 1, 18], [7, 12, 27, 20, 14], [14, 5, 28, 13, 7], [11, 3, 21, 25, 27]], ![[6, 22, 8, 7, 2], [5, 6, 7, 25, 16], [21, 9, 14, 19, 17], [23, 2, 12, 9, 17], [20, 3, 7, 5, 5]], ![[24, 0, 22, 21, 24], [5, 27, 3, 17, 14], [25, 16, 21, 15, 15], [14, 11, 25, 15, 10], [6, 22, 8, 7, 2]], ![[0, 1], [9, 19, 23, 13, 27], [2, 0, 26, 22, 21], [4, 11, 22, 20, 24], [24, 0, 22, 21, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 6, 28, 1], [], [], []]
 b := ![[], [10, 7, 8, 26, 15], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [20, 18, 13, 28, 26, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1364868776704, 2610297382762, -2083433163114, 145062261376, 561589607578]
  a := ![-5, -2, 2, -8, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![47064440576, 90010254578, -71842522866, 5002146944, 19365158882]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1014964, -547132, -9751, 14683, 43416]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![1014964, -547132, -9751, 14683, 43416]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![2, 1, 1, 0, 0], ![30, 1, 0, 1, 0], ![1, 30, 0, 0, 1]] where
  M :=![![![1014964, -547132, -9751, 14683, 43416], ![-332645, 180309, 2593, -4819, -14050], ![107581, -63102, 2478, 367, 4412], ![148858, -77039, -4353, 5071, 5186], ![-546329, 303520, 945, -11511, -19617]]]
  hmulB := by decide  
  f := ![![![-5224134, -16956957, 2261656, 3316217, 1968220]], ![![-12429543, -40358658, 5313686, 7839529, 4664214]], ![![-1688774, -5484145, 718503, 1062544, 632758]], ![![-6379507, -20711221, 2741987, 4034720, 2398006]], ![![-13211749, -42902014, 5630746, 8319860, 4952931]]]
  g := ![![![17760, -59824, -9751, 14683, 43416], ![-5781, 19485, 2593, -4819, -14050], ![2813, -6397, 2478, 367, 4412], ![8, -7527, -4353, 5071, 5186], ![-5912, 29116, 945, -11511, -19617]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [15, 28, 1] where
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
 g := ![![[6, 4], [3, 20], [28, 5], [3, 1]], ![[18, 27], [1, 11], [12, 26], [6, 30]]]
 h' := ![![[3, 30], [17, 29], [14, 19], [17, 25], [0, 1]], ![[0, 1], [11, 2], [9, 12], [30, 6], [3, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [20, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [15, 28, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11620, 24578, -59086, 102898, -21221]
  a := ![6, -62, -1, -57, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-95457, 19916, -59086, 102898, -21221]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11673, 37819, -5401, -7676, -4496]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![11673, 37819, -5401, -7676, -4496]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![7, 19, 1, 0, 0], ![11, 25, 0, 1, 0], ![4, 13, 0, 0, 1]] where
  M :=![![![11673, 37819, -5401, -7676, -4496], ![28292, 91696, -12953, -18478, -10856], ![68370, 221603, -30954, -44384, -26100], ![68062, 220810, -30180, -43907, -25906], ![75988, 246535, -33717, -48534, -28803]]]
  hmulB := by decide  
  f := ![![![55522671793, -29932899551, -530334557, 798601826, 2377348824]], ![![-18220188766, 9822709580, 174033335, -262067288, -780145172]], ![![1563039035, -842652000, -14929642, 22481732, 66925616]], ![![5270120073, -2841181263, -50338478, 75801963, 225654014]], ![![-1449738280, 781570283, 13847430, -20852088, -62074347]]]
  g := ![![![4900, 12606, -5401, -7676, -4496], ![11795, 30351, -12953, -18478, -10856], ![28312, 72859, -30954, -44384, -26100], ![27933, 71893, -30180, -43907, -25906], ![31003, 79837, -33717, -48534, -28803]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [17, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 30], [0, 1]]
 g := ![![[15, 1], [28, 9], [14, 1], [24, 1]], ![[8, 30], [27, 22], [7, 30], [17, 30]]]
 h' := ![![[24, 30], [20, 30], [10, 3], [26, 1], [0, 1]], ![[0, 1], [27, 1], [20, 28], [19, 30], [24, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [2, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal' SI31N1 31 where
  n := 2
  hpos := by decide
  P := [17, 7, 1]
  hirr := P31P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-678, -2369, 1092, -13, 350]
  a := ![-1, -3, 1, -5, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-309, -882, 1092, -13, 350]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N1 B_one_repr
lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47438, -25338, -517, 613, 1994]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![47438, -25338, -517, 613, 1994]] 
 ![![31, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![47438, -25338, -517, 613, 1994], ![-15339, 9035, -29, -421, -768], ![5723, -776, -528, -479, -74], ![7726, -1217, -615, -557, -58], ![-24767, 16996, -405, -1161, -1533]]]
  hmulB := by decide  
  f := ![![![-10288, -26419, 22474, -8809, -898]], ![![-3703, -8431, 7030, -1960, -858]], ![![4485, 6694, -5059, -1576, 2784]], ![![-14806, -36292, 30645, -10736, -2150]], ![![8965, 34939, -31292, 21059, -5129]]]
  g := ![![![9750, -25338, -517, 613, 1994], ![-3328, 9035, -29, -421, -768], ![674, -776, -528, -479, -74], ![921, -1217, -615, -557, -58], ![-5959, 16996, -405, -1161, -1533]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![1014964, -547132, -9751, 14683, 43416]] ![![11673, 37819, -5401, -7676, -4496]]
  ![![-10288, -26419, 22474, -8809, -898]] where
 M := ![![![-10288, -26419, 22474, -8809, -898]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-10288, -26419, 22474, -8809, -898]] ![![47438, -25338, -517, 613, 1994]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26, 98, 5, -21, -16]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![26, 98, 5, -21, -16]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![3, 17, 2, 36, 1]] where
  M :=![![![26, 98, 5, -21, -16], ![107, 335, -89, -11, -26], ![197, 512, 8, -189, 4], ![-164, -103, 421, -81, -178], ![839, 2078, -1377, 337, 107]]]
  hmulB := by decide  
  f := ![![![-21768, 11735, 208, -313, -932]], ![![7143, -3852, -68, 103, 306]], ![![-2345, 1261, 23, -33, -100]], ![![-3188, 1715, 31, -45, -136]], ![![-1392, 746, 14, -19, -59]]]
  g := ![![![2, 10, 1, 15, -16], ![5, 21, -1, 25, -26], ![5, 12, 0, -9, 4], ![10, 79, 21, 171, -178], ![14, 7, -43, -95, 107]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 4 2 5 [12, 0, 7, 26, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 4, 6, 11], [13, 21, 24, 25], [19, 11, 7, 1], [0, 1]]
 g := ![![[11, 2, 3, 11], [28, 24, 34], [2, 13, 30, 10], [1], []], ![[29, 5, 17, 36, 24, 36], [4, 13, 33], [0, 31, 4, 20, 0, 26], [6, 29, 28], [15, 20, 10]], ![[28, 22, 9, 6, 13, 10], [35, 33, 11], [22, 19, 22, 10, 16, 4], [34, 14, 26], [14, 9, 33]], ![[13, 14, 32, 21, 21, 25], [28, 5, 28], [5, 28, 20, 0, 29, 26], [36, 3, 7], [6, 25, 1]]]
 h' := ![![[16, 4, 6, 11], [18, 29, 28, 23], [13, 25, 33, 16], [25, 0, 30, 11], [0, 0, 1], [0, 1]], ![[13, 21, 24, 25], [23, 0, 29, 26], [21, 9, 30, 25], [6, 18, 36, 6], [2, 36, 20, 18], [16, 4, 6, 11]], ![[19, 11, 7, 1], [12, 34, 34, 20], [32, 31, 18, 14], [0, 5, 36, 30], [1, 31, 16, 10], [13, 21, 24, 25]], ![[0, 1], [33, 11, 20, 5], [6, 9, 30, 19], [24, 14, 9, 27], [30, 7, 0, 9], [19, 11, 7, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [15, 0, 25], []]
 b := ![[], [], [9, 26, 9, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 4
  hpos := by decide
  P := [12, 0, 7, 26, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1895490036, 5134609946, -11581292610, 9461806396, 641661726]
  a := ![8, 19, -3, 26, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-797166, -156044308, -347692326, -368595020, 641661726]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1874161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21768, -11735, -208, 313, 932]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![21768, -11735, -208, 313, 932]] 
 ![![37, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![21768, -11735, -208, 313, 932], ![-7143, 3852, 68, -103, -306], ![2345, -1261, -23, 33, 100], ![3188, -1715, -31, 45, 136], ![-11827, 6381, 112, -171, -507]]]
  hmulB := by decide  
  f := ![![![-26, -98, -5, 21, 16]], ![![-5, -17, 2, 2, 2]], ![![-25, -88, -4, 21, 12]], ![![-4, -29, -13, 9, 10]], ![![-29, -80, 36, -4, 1]]]
  g := ![![![1369, -11735, -208, 313, 932], ![-449, 3852, 68, -103, -306], ![148, -1261, -23, 33, 100], ![201, -1715, -31, 45, 136], ![-743, 6381, 112, -171, -507]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![26, 98, 5, -21, -16]] ![![21768, -11735, -208, 313, 932]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 5 2 5 [2, 2, 25, 2, 30, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 2, 36, 37, 9], [5, 30, 32, 38, 37], [13, 15, 17, 24, 13], [8, 34, 38, 24, 23], [0, 1]]
 g := ![![[28, 11, 10, 11, 8], [7, 1, 13, 39], [25, 3, 16, 39], [1], []], ![[1, 25, 39, 17, 39, 31], [24, 35, 11, 20], [24, 8, 29, 2], [11, 3, 28, 6, 8, 28, 7, 9], [10, 40, 40, 40]], ![[24, 9, 12, 38, 39, 37, 17, 32], [31, 28, 12, 36], [27, 7, 38, 18], [8, 18, 9, 10, 27, 22, 23, 5], [14, 35, 36, 16]], ![[37, 28, 37, 6, 14, 20, 36, 19], [8, 26, 21, 21], [0, 0, 19, 10], [9, 33, 11, 36, 3, 22, 3, 29], [23, 31, 23, 5]], ![[5, 26, 12, 30, 9, 1, 23, 20], [25, 5, 18, 40], [8, 27, 21, 31], [28, 3, 8, 5, 8, 1, 38, 37], [13, 11, 35, 37]]]
 h' := ![![[26, 2, 36, 37, 9], [11, 13, 24, 15, 7], [36, 34, 15, 37, 11], [39, 39, 16, 39, 11], [0, 0, 1], [0, 1]], ![[5, 30, 32, 38, 37], [13, 20, 33, 7], [26, 20, 37, 19, 15], [19, 13, 38, 1, 24], [0, 4, 31, 27, 1], [26, 2, 36, 37, 9]], ![[13, 15, 17, 24, 13], [2, 37, 24, 6, 22], [8, 2, 6, 32, 35], [29, 21, 17, 33, 10], [38, 38, 31, 22, 38], [5, 30, 32, 38, 37]], ![[8, 34, 38, 24, 23], [0, 12, 8, 30, 19], [37, 31, 26, 22, 12], [23, 39, 12, 1, 16], [0, 36, 25, 11, 10], [13, 15, 17, 24, 13]], ![[0, 1], [27, 0, 34, 24, 34], [35, 36, 39, 13, 9], [16, 11, 40, 8, 21], [38, 4, 35, 22, 33], [8, 34, 38, 24, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 30, 37, 27], [], [], []]
 b := ![[], [2, 39, 8, 23, 38], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 5
  hpos := by decide
  P := [2, 2, 25, 2, 30, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26876253296239, 18976806266899, -9470640621634, -33257982725129, 27162592966270]
  a := ![-10, 1, 5, -7, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![655518373079, 462848933339, -230991234674, -811170310369, 662502267470]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![677715699, -365364161, -6473341, 9747830, 29018174]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![677715699, -365364161, -6473341, 9747830, 29018174]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![42, 2, 30, 1, 0], ![31, 18, 10, 0, 1]] where
  M :=![![![677715699, -365364161, -6473341, 9747830, 29018174], ![-222397562, 119897052, 2124271, -3198852, -9522514], ![72981260, -39345525, -696778, 1049690, 3124810], ![99224386, -53491980, -948478, 1427493, 4248542], ![-368259834, 198532113, 3518307, -5297548, -15767731]]]
  hmulB := by decide  
  f := ![![![-580425, -1923843, 55987, 221780, 164522]], ![![-1094396, -3650356, -6837, 333754, 279038]], ![![-1898550, -6402955, -356616, 320080, 388470]], ![![-1962088, -6585666, -213808, 447005, 444382]], ![![-1326525, -4437864, -73186, 355806, 320227]]]
  g := ![![![-14680385, -21097371, -13699767, 9747830, 29018174], ![4817492, 6923256, 4495697, -3198852, -9522514], ![-1580810, -2271895, -1475246, 1049690, 3124810], ![-2149654, -3088854, -2006016, 1427493, 4248542], ![7977601, 11463869, 7444699, -5297548, -15767731]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [32, 34, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 13, 30], [23, 29, 13], [0, 1]]
 g := ![![[41, 37, 38], [41, 9, 4], [37, 40], [10, 1, 1], []], ![[18, 13, 27, 39], [23, 19, 8, 20], [29, 40], [16, 32, 7, 32], [3, 40]], ![[7, 12, 23, 36], [1, 35, 27, 10], [3, 31], [15, 19, 18, 4], [20, 40]]]
 h' := ![![[21, 13, 30], [21, 31, 9], [37, 31, 41], [24, 15, 30], [0, 0, 1], [0, 1]], ![[23, 29, 13], [36, 17, 30], [41, 11, 12], [25, 12, 30], [1, 24, 29], [21, 13, 30]], ![[0, 1], [36, 38, 4], [26, 1, 33], [6, 16, 26], [18, 19, 13], [23, 29, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 37], []]
 b := ![[], [41, 41, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [32, 34, 42, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![32038820, 53479860, -41696660, -4903812, 17079576]
  a := ![6, -10, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6778324, -5677788, -1520420, -4903812, 17079576]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![580425, 1923843, -55987, -221780, -164522]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![580425, 1923843, -55987, -221780, -164522]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![28, 26, 1, 0, 0], ![23, 42, 0, 1, 0], ![17, 38, 0, 0, 1]] where
  M :=![![![580425, 1923843, -55987, -221780, -164522], ![1094396, 3650356, 6837, -333754, -279038], ![1898550, 6402955, 356616, -320080, -388470], ![846642, 2992870, 833044, 363453, 13674], ![362772, 1453061, 1193369, 783894, 237805]]]
  hmulB := by decide  
  f := ![![![-677715699, 365364161, 6473341, -9747830, -29018174]], ![![222397562, -119897052, -2124271, 3198852, 9522514]], ![![-308527540, 166330667, 2946960, -4437646, -13210426]], ![![-147581113, 79562593, 1409673, -2122693, -6319092]], ![![-62832551, 33873736, 600144, -903702, -2690365]]]
  g := ![![![233625, 440607, -55987, -221780, -164522], ![309836, 653342, 6837, -333754, -279038], ![136724, 589213, 356616, -320080, -388470], ![-722569, -801184, 833044, 363453, 13674], ![-1281949, -1663597, 1193369, 783894, 237805]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [42, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 42], [0, 1]]
 g := ![![[18, 31], [17, 1], [9], [20, 23], [1]], ![[17, 12], [35, 42], [9], [4, 20], [1]]]
 h' := ![![[18, 42], [17, 17], [22, 42], [20, 40], [1, 18], [0, 1]], ![[0, 1], [22, 26], [4, 1], [9, 3], [24, 25], [18, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [15, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [42, 25, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2512, -2936, -3304, 11504, -800]
  a := ![6, 13, 4, 20, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3744, -8600, -3304, 11504, -800]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![677715699, -365364161, -6473341, 9747830, 29018174]] ![![580425, 1923843, -55987, -221780, -164522]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2480525, -7009277, 632351, 1146140, 723732]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-2480525, -7009277, 632351, 1146140, 723732]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![7, 46, 24, 18, 1]] where
  M :=![![![-2480525, -7009277, 632351, 1146140, 723732], ![-4643716, -15599082, 1253099, 2410842, 1568548], ![-10137542, -33193029, 2381200, 4917040, 3253136], ![-8232166, -26983422, 1463800, 3634299, 2506198], ![-7920068, -26793229, 1123951, 3349250, 2392803]]]
  hmulB := by decide  
  f := ![![![1459, -869899, 855107, -979818, 433492]], ![![-4447754, -7379782, 5745315, 730396, -2393128]], ![![19875420, 46766993, -39220842, 12221026, 3853920]], ![![-7081290, -42595060, 39450806, -33475527, 11490630]], ![![2036973, -802612, 1477670, -5031152, 3170639]]]
  g := ![![![-160567, -857467, -356111, -252788, 723732], ![-332416, -1867070, -774299, -549426, 1568548], ![-700202, -3890155, -1610512, -1141264, 3253136], ![-548416, -3026990, -1248616, -882495, 2506198], ![-524887, -2911961, -1197943, -845132, 2392803]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [22, 15, 28, 4, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 43, 1, 28], [37, 46, 15, 15], [39, 4, 31, 4], [0, 1]]
 g := ![![[25, 16, 8, 12], [14, 12, 19, 24], [19, 7, 10, 3], [43, 1], []], ![[0, 30, 10, 1, 19, 32], [26, 7, 27, 5, 32, 1], [42, 42, 29, 18, 22, 1], [30, 23, 11, 35, 10, 25], [15, 22, 32]], ![[41, 43, 9, 7, 0, 11], [38, 20, 43, 30, 16, 11], [45, 7, 15, 26, 9, 35], [17, 6, 25, 26, 29, 11], [19, 20, 37]], ![[4, 24, 30, 4, 13, 2], [16, 13, 3, 7, 24, 34], [22, 31, 5, 8, 22, 42], [35, 39, 36, 36, 24, 25], [44, 43, 16]]]
 h' := ![![[14, 43, 1, 28], [21, 21, 9, 24], [5, 20, 3, 27], [41, 38, 3, 35], [0, 0, 1], [0, 1]], ![[37, 46, 15, 15], [10, 11, 44, 13], [33, 25, 40, 18], [26, 35, 3, 29], [7, 25, 0, 43], [14, 43, 1, 28]], ![[39, 4, 31, 4], [22, 26, 45, 30], [11, 27, 7, 30], [14, 9, 6, 21], [11, 0, 29, 30], [37, 46, 15, 15]], ![[0, 1], [6, 36, 43, 27], [25, 22, 44, 19], [1, 12, 35, 9], [36, 22, 17, 21], [39, 4, 31, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [11, 3, 5], []]
 b := ![[], [], [10, 7, 27, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [22, 15, 28, 4, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-921357858, -1897397878, 1552342452, -262698834, -312865670]
  a := ![2, -5, -1, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![26993656, 265838786, 192789756, 114231558, -312865670]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1459, 869899, -855107, 979818, -433492]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-1459, 869899, -855107, 979818, -433492]] 
 ![![47, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![44, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![-1459, 869899, -855107, 979818, -433492], ![4447754, 7379782, -5745315, -730396, 2393128], ![-19875420, -46766993, 39220842, -12221026, -3853920], ![7081290, 42595060, -39450806, 33475527, -11490630], ![49222658, 47860251, -30365951, -46051228, 43255943]]]
  hmulB := by decide  
  f := ![![![2480525, 7009277, -632351, -1146140, -723732]], ![![732128, 2121498, -188113, -343926, -218156]], ![![2537886, 7268111, -642652, -1177600, -746752]], ![![808478, 2363718, -192596, -369957, -238106]], ![![960169, 2807072, -225728, -437050, -281889]]]
  g := ![![![466575, 869899, -855107, 979818, -433492], ![3011746, 7379782, -5745315, -730396, 2393128], ![-20849520, -46766993, 39220842, -12221026, -3853920], ![21328280, 42595060, -39450806, 33475527, -11490630], ![15208023, 47860251, -30365951, -46051228, 43255943]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-2480525, -7009277, 632351, 1146140, 723732]] ![![-1459, 869899, -855107, 979818, -433492]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16430622383, -8858166947, -156843035, 236421750, 703566792]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![16430622383, -8858166947, -156843035, 236421750, 703566792]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![22, 31, 40, 1, 0], ![37, 21, 38, 0, 1]] where
  M :=![![![16430622383, -8858166947, -156843035, 236421750, 703566792], ![-5392112586, 2906010300, 51779599, -77264320, -230723292], ![1768522016, -956590439, -16128176, 26294878, 76194652], ![2404425124, -1300657424, -22067220, 35651423, 103559198], ![-8929673826, 4808483537, 86371403, -127130656, -381593845]]]
  hmulB := by decide  
  f := ![![![-350144103, -718590003, 587500231, -97048104, -120128144]], ![![863977048, 2519790864, -2183207771, 1077952358, -73968064]], ![![1669696870, 86162493, 480253674, -3288463184, 2229872780]], ![![1412684562, 837402356, -344739605, -1923773899, 1507408802]], ![![1731294877, 1609590976, -995565339, -1702603756, 1558029375]]]
  g := ![![![-279294857, -584191393, -685834927, 236421750, 703566792], ![91404986, 191441384, 224713915, -77264320, -230723292], ![-30739008, -63619233, -74779624, 26294878, 76194652], ![-41728236, -86426315, -101573088, 35651423, 103559198], ![150682507, 316283106, 371172901, -127130656, -381593845]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [5, 10, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 15, 46], [21, 37, 7], [0, 1]]
 g := ![![[15, 41, 4], [1, 36], [30, 44, 42], [19, 1], [1]], ![[27, 38, 13, 11], [5, 44], [20, 27, 13, 37], [19, 29], [17, 25, 4, 28]], ![[10, 9, 7, 43], [39, 47], [24, 0, 41, 44], [40, 17], [41, 43, 8, 25]]]
 h' := ![![[31, 15, 46], [23, 51, 2], [9, 34, 6], [36, 11, 28], [48, 43, 52], [0, 1]], ![[21, 37, 7], [21, 1, 35], [24, 20, 37], [51, 16, 5], [26, 20, 33], [31, 15, 46]], ![[0, 1], [42, 1, 16], [5, 52, 10], [8, 26, 20], [46, 43, 21], [21, 37, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 52], []]
 b := ![[], [1, 29, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [5, 10, 1, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26899555, 61725153, -54267915, 17714822, 6245290]
  a := ![10, -1, 0, 5, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11205703, -11671423, -18871355, 17714822, 6245290]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-350144103, -718590003, 587500231, -97048104, -120128144]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-350144103, -718590003, 587500231, -97048104, -120128144]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![32, 26, 1, 0, 0], ![8, 23, 0, 1, 0], ![42, 51, 0, 0, 1]] where
  M :=![![![-350144103, -718590003, 587500231, -97048104, -120128144], ![863977048, 2519790864, -2183207771, 1077952358, -73968064], ![1669696870, 86162493, 480253674, -3288463184, 2229872780], ![-10995711236, -21368711570, 17273089794, -1702954097, -4366415542], ![23121961224, 55706368961, -46904747935, 15677382254, 3838461907]]]
  hmulB := by decide  
  f := ![![![16430622383, -8858166947, -156843035, 236421750, 703566792]], ![![-5392112586, 2906010300, 51779599, -77264320, -230723292]], ![![7308556812, -3940786131, -69600674, 105338086, 313047668]], ![![185487070, -100523700, -1620391, 2829171, 8027506]], ![![7663372158, -4132603829, -72835406, 110605708, 328326859]]]
  g := ![![![-251478955, -144055741, 587500231, -97048104, -120128144], ![1230371048, 721936980, -2183207771, 1077952358, -73968064], ![-1529157962, -952628143, 480253674, -3288463184, 2229872780], ![-6919273568, -3936111497, 17273089794, -1702954097, -4366415542], ![23347913906, 13563933324, -46904747935, 15677382254, 3838461907]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [43, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 52], [0, 1]]
 g := ![![[4, 37], [7], [28, 38], [29], [40, 1]], ![[0, 16], [7], [11, 15], [29], [27, 52]]]
 h' := ![![[40, 52], [30, 39], [15, 22], [18, 41], [29, 20], [0, 1]], ![[0, 1], [0, 14], [47, 31], [15, 12], [34, 33], [40, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [22, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [43, 13, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12333, -29002, 19620, -1704, -1838]
  a := ![6, 1, -3, 6, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10365, -7664, 19620, -1704, -1838]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![16430622383, -8858166947, -156843035, 236421750, 703566792]] ![![-350144103, -718590003, 587500231, -97048104, -120128144]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-793648304, 427864779, 7580664, -11415321, -33982130]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-793648304, 427864779, 7580664, -11415321, -33982130]] 
 ![![59, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![-793648304, 427864779, 7580664, -11415321, -33982130], ![260441719, -140407170, -2487590, 3746007, 11151488], ![-85465897, 46075857, 816167, -1229173, -3659474], ![-116197550, 62643723, 1109729, -1671423, -4975180], ![431254987, -232496023, -4118210, 6202803, 18465085]]]
  hmulB := by decide  
  f := ![![![29204290, 93221756, -20348103, -24324931, -13139478]], ![![3844277, 12281611, -2627238, -3163488, -1715386]], ![![20542505, 65623074, -14066832, -16925455, -9174138]], ![![4765412, 15296589, -2903122, -3655916, -2028348]], ![![26853987, 85833766, -18150297, -21946571, -11926683]]]
  g := ![![![-28543826, 427864779, 7580664, -11415321, -33982130], ![9366850, -140407170, -2487590, 3746007, 11151488], ![-3073709, 46075857, 816167, -1229173, -3659474], ![-4179112, 62643723, 1109729, -1671423, -4975180], ![15509961, -232496023, -4118210, 6202803, 18465085]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17227829, -9287673, -164583, 247798, 737660]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![17227829, -9287673, -164583, 247798, 737660]] 
 ![![59, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![17227829, -9287673, -164583, 247798, 737660], ![-5653482, 3047706, 54109, -81368, -242064], ![1855144, -1000157, -17758, 26850, 79328], ![2522854, -1358776, -24926, 36351, 108218], ![-9362466, 5044039, 91729, -135400, -401033]]]
  hmulB := by decide  
  f := ![![![-20496183, -66243979, 10266873, 14057312, 8108492]], ![![-6072091, -19626277, 3035800, 4160182, 2400568]], ![![-5947729, -19228844, 2951417, 4058300, 2345244]], ![![-11911646, -38508270, 5919460, 8134099, 4699254]], ![![-8723466, -28207331, 4306237, 5935310, 3433483]]]
  g := ![![![2341307, -9287673, -164583, 247798, 737660], ![-768285, 3047706, 54109, -81368, -242064], ![252087, -1000157, -17758, 26850, 79328], ![342592, -1358776, -24926, 36351, 108218], ![-1271564, 5044039, 91729, -135400, -401033]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-311148362, 167750480, 2971151, -4476587, -13323416]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-311148362, 167750480, 2971151, -4476587, -13323416]] 
 ![![59, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-311148362, 167750480, 2971151, -4476587, -13323416], ![102110741, -55032307, -977341, 1465715, 4370242], ![-33496221, 18098802, 315124, -488967, -1438812], ![-45544606, 24594319, 430277, -662217, -1954682], ![169085993, -91110684, -1620317, 2424087, 7234767]]]
  hmulB := by decide  
  f := ![![![5078280, 7719795, -5866030, -1626933, 3082672]], ![![1706249, 2265023, -1647954, -915802, 1198818]], ![![2698509, 5572923, -4562021, 787077, 908520]], ![![3361886, 4583389, -3365437, -1669089, 2302288]], ![![-7917179, -15669395, 12715468, -1544419, -3003345]]]
  g := ![![![-75749242, 167750480, 2971151, -4476587, -13323416], ![24852628, -55032307, -977341, 1465715, 4370242], ![-8167905, 18098802, 315124, -488967, -1438812], ![-11101083, 24594319, 430277, -662217, -1954682], ![41147671, -91110684, -1620317, 2424087, 7234767]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2

def I59N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![763, 1009, -733, -414, 538]] i)))

def SI59N3: IdealEqSpanCertificate' Table ![![763, 1009, -733, -414, 538]] 
 ![![59, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![763, 1009, -733, -414, 538], ![-4718, -10192, 8417, -1880, -1366], ![9048, 29653, -26070, 14954, -2394], ![19412, 19328, -12420, -17653, 16834], ![-81726, -151769, 121453, -4736, -35953]]]
  hmulB := by decide  
  f := ![![![11607827, -6260805, -110545, 167460, 497342]], ![![7018144, -3785444, -66821, 101270, 300710]], ![![414600, -223893, -3918, 6028, 17794]], ![![1012449, -546341, -9613, 14651, 43408]], ![![5205063, -2807734, -49534, 75146, 223049]]]
  g := ![![![-789, 1009, -733, -414, 538], ![6638, -10192, 8417, -1880, -1366], ![-17228, 29653, -26070, 14954, -2394], ![-17251, 19328, -12420, -17653, 16834], ![103957, -151769, 121453, -4736, -35953]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N3 : Nat.card (O ⧸ I59N3) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N3)

lemma isPrimeI59N3 : Ideal.IsPrime I59N3 := prime_ideal_of_norm_prime hp59.out _ NI59N3

def I59N4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-327071552, 176327972, 3124079, -4704383, -14004426]] i)))

def SI59N4: IdealEqSpanCertificate' Table ![![-327071552, 176327972, 3124079, -4704383, -14004426]] 
 ![![59, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![47, 0, 1, 0, 0], ![56, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![-327071552, 176327972, 3124079, -4704383, -14004426], ![107331025, -57863379, -1025183, 1543775, 4595660], ![-35221505, 18988302, 336426, -506591, -1508110], ![-47886368, 25816195, 457323, -688757, -2050366], ![177725293, -95813978, -1697391, 2556219, 7609767]]]
  hmulB := by decide  
  f := ![![![6956034, 22471035, -3538174, -4811189, -2766790]], ![![4655871, 15040935, -2366076, -3218670, -1851302]], ![![6269335, 20254778, -3178685, -4328568, -2490824]], ![![7354652, 23762273, -3723643, -5073913, -2920548]], ![![3446801, 11139413, -1729994, -2366569, -1364541]]]
  g := ![![![-108923651, 176327972, 3124079, -4704383, -14004426], ![35744131, -57863379, -1025183, 1543775, 4595660], ![-11729715, 18988302, 336426, -506591, -1508110], ![-15947480, 25816195, 457323, -688757, -2050366], ![59187402, -95813978, -1697391, 2556219, 7609767]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N4 : Nat.card (O ⧸ I59N4) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N4)

lemma isPrimeI59N4 : Ideal.IsPrime I59N4 := prime_ideal_of_norm_prime hp59.out _ NI59N4
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-793648304, 427864779, 7580664, -11415321, -33982130]] ![![17227829, -9287673, -164583, 247798, 737660]]
  ![![-15788342522140432, 8511673799723344, 150805128201307, -227089200875535, -676019296546392]] where
 M := ![![![-15788342522140432, 8511673799723344, 150805128201307, -227089200875535, -676019296546392]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-15788342522140432, 8511673799723344, 150805128201307, -227089200875535, -676019296546392]] ![![-311148362, 167750480, 2971151, -4476587, -13323416]]
  ![![5672636125533839024576395, -3058182213710046980181291, -54183180842439133085399, 81591490859230303153666, 242888794550027895051882]] where
 M := ![![![5672636125533839024576395, -3058182213710046980181291, -54183180842439133085399, 81591490859230303153666, 242888794550027895051882]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N2 : IdealMulLeCertificate' Table 
  ![![5672636125533839024576395, -3058182213710046980181291, -54183180842439133085399, 81591490859230303153666, 242888794550027895051882]] ![![763, 1009, -733, -414, 538]]
  ![![24967730445899286231, -13460385520351058930, -238483665096379126, 359119517869763854, 1069058867244689120]] where
 M := ![![![24967730445899286231, -13460385520351058930, -238483665096379126, 359119517869763854, 1069058867244689120]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N3 : IdealMulLeCertificate' Table 
  ![![24967730445899286231, -13460385520351058930, -238483665096379126, 359119517869763854, 1069058867244689120]] ![![-327071552, 176327972, 3124079, -4704383, -14004426]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-9429749697023142266629229244, 5083684580678089731624990120, 90069911382630365337363685, -135631357129766211024243955, -403759466698192144677025870]]]
 hmul := by decide  
 g := ![![![![-159826266051239699434393716, 86164145435221859858050680, 1526608667502209581989215, -2298836561521461203800745, -6843380791494782113169930]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2, I59N3, I59N4] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
    exact isPrimeI59N3
    exact isPrimeI59N4
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1 ⊙ MulI59N2 ⊙ MulI59N3)
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


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [51, 15, 1, 31, 28, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 46, 12, 35, 18], [39, 7, 29, 42, 3], [13, 33, 45, 58, 42], [6, 35, 36, 48, 59], [0, 1]]
 g := ![![[28, 43, 52, 57, 58], [54, 32, 0, 45], [48, 21, 36, 35, 5], [21, 33, 1], []], ![[33, 58, 58, 33, 33, 36, 32, 50], [2, 48, 49, 36], [14, 56, 46, 10, 16, 5, 46, 2], [42, 23, 33, 14, 9, 50, 48, 40], [33, 24, 37, 24, 36, 39, 44, 37]], ![[50, 48, 7, 13, 5, 43, 60, 25], [4, 6, 56, 1], [39, 42, 23, 33, 43, 2, 10, 4], [53, 30, 21, 12, 58, 44, 15, 3], [39, 59, 55, 42, 12, 53, 12, 27]], ![[56, 30, 12, 13, 38, 56, 19, 39], [50, 23, 38, 47], [38, 6, 40, 6, 34, 57, 57, 58], [18, 8, 46, 23, 8, 23, 12, 48], [0, 55, 40, 53, 3, 35, 8, 34]], ![[16, 27, 18, 42, 7, 55, 13, 37], [50, 3, 20, 1], [45, 25, 41, 10, 12, 8, 19, 40], [40, 53, 19, 50, 8, 48, 8, 44], [19, 18, 32, 36, 48, 19, 7, 53]]]
 h' := ![![[36, 46, 12, 35, 18], [55, 32, 50, 31, 34], [53, 36, 14, 55, 17], [27, 15, 43, 33, 35], [0, 0, 0, 1], [0, 1]], ![[39, 7, 29, 42, 3], [34, 38, 12, 47, 39], [40, 4, 12, 39, 55], [59, 13, 24, 50, 20], [16, 46, 51, 48, 3], [36, 46, 12, 35, 18]], ![[13, 33, 45, 58, 42], [6, 31, 0, 28, 54], [37, 54, 12, 42, 1], [38, 32, 7, 17, 15], [51, 43, 9, 40, 1], [39, 7, 29, 42, 3]], ![[6, 35, 36, 48, 59], [3, 2, 50, 11, 40], [33, 19, 14, 23, 48], [10, 6, 13, 33, 14], [1, 18, 18, 0, 6], [13, 33, 45, 58, 42]], ![[0, 1], [21, 19, 10, 5, 16], [58, 9, 9, 24, 1], [57, 56, 35, 50, 38], [40, 15, 44, 33, 51], [6, 35, 36, 48, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 31, 32, 30], [], [], []]
 b := ![[], [17, 39, 40, 35, 39], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [51, 15, 1, 31, 28, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5377463418, -18923040946, 11578422993, -5000225937, 2478995958]
  a := ![3, 5, 0, 9, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-88155138, -310213786, 189810213, -81970917, 40639278]
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



lemma PB1567I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB1567I1 : PrimesBelowBoundCertificateInterval O 23 61 1567 where
  m := 9
  g := ![1, 3, 2, 1, 2, 2, 2, 5, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB1567I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2, I59N3, I59N4]
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
    · exact ![1874161, 37]
    · exact ![115856201]
    · exact ![79507, 1849]
    · exact ![4879681, 47]
    · exact ![148877, 2809]
    · exact ![59, 59, 59, 59, 59]
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
      exact NI59N3
      exact NI59N4
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
  β := ![I31N0, I31N1, I31N2, I37N1, I47N1, I59N0, I59N1, I59N2, I59N3, I59N4]
  Il := ![[], [I31N0, I31N1, I31N2], [I37N1], [], [], [I47N1], [], [I59N0, I59N1, I59N2, I59N3, I59N4], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
