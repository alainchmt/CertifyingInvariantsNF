
import IdealArithmetic.Examples.NF3_1_946979_1.RI3_1_946979_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-138, -7, 18]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-138, -7, 18]] 
 ![![83, 0, 0], ![29, 1, 0], ![82, 0, 1]] where
  M :=![![![-138, -7, 18], ![3366, -210, -77], ![-1309, 334, -210]]]
  hmulB := by decide  
  f := ![![![-69818, -4542, -4319]], ![![-34125, -2220, -2111]], ![![-79210, -5153, -4900]]]
  g := ![![![-17, -7, 18], ![190, -210, -77], ![75, 334, -210]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-298, 51, -24]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-298, 51, -24]] 
 ![![83, 0, 0], ![60, 1, 0], ![50, 0, 1]] where
  M :=![![![-298, 51, -24], ![-4488, -202, 561], ![9537, -612, -202]]]
  hmulB := by decide  
  f := ![![![384136, 24990, 23763]], ![![331227, 21548, 20490]], ![![287710, 18717, 17798]]]
  g := ![![![-26, 51, -24], ![-246, -202, 561], ![679, -612, -202]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-809470540, -52660179, -50074570]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![-809470540, -52660179, -50074570]] 
 ![![83, 0, 0], ![77, 1, 0], ![42, 0, 1]] where
  M :=![![![-809470540, -52660179, -50074570], ![-9363944590, -609172260, -579261969], ![-9847453473, -640626974, -609172260]]]
  hmulB := by decide  
  f := ![![![244206, -16640, -4251]], ![![216975, -12290, -6149]], ![![86084, -8489, 996]]]
  g := ![![![64439701, -52660179, -50074570], ![745437616, -609172260, -579261969], ![783928415, -640626974, -609172260]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-138, -7, 18]] ![![-298, 51, -24]]
  ![![244206, -16640, -4251]] where
 M := ![![![244206, -16640, -4251]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![244206, -16640, -4251]] ![![-809470540, -52660179, -50074570]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![105583879364207314, 6868768796493397, 6531513003664214]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![105583879364207314, 6868768796493397, 6531513003664214]] 
 ![![89, 0, 0], ![0, 89, 0], ![76, 74, 1]] where
  M :=![![![105583879364207314, 6868768796493397, 6531513003664214], ![1221392931685208018, 79457827349550458, 75556456761427367], ![1284459764944265239, 83560645876318050, 79457827349550458]]]
  hmulB := by decide  
  f := ![![![-64922074, 24179066, -17655217]], ![![-3301525579, 5698794, 265969726]], ![![-2749724552, 20926571, 206131034]]]
  g := ![![![-4391136055216550, -5353519027805151, 6531513003664214], ![-50796604294194066, -61929437898832300, 75556456761427367], ![-53419495658669321, -65127175033600178, 79457827349550458]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [17, 85, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 88], [0, 1]]
 g := ![![[5, 21], [47], [47], [62, 16], [17, 16], [1]], ![[0, 68], [47], [47], [37, 73], [81, 73], [1]]]
 h' := ![![[4, 88], [46, 33], [20, 74], [14, 15], [67, 85], [72, 4], [0, 1]], ![[0, 1], [0, 56], [49, 15], [74, 74], [51, 4], [88, 85], [4, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [41, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [17, 85, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![391, -76, -78]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![71, 64, -78]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-64922074, 24179066, -17655217]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-64922074, 24179066, -17655217]] 
 ![![89, 0, 0], ![76, 1, 0], ![17, 0, 1]] where
  M :=![![![-64922074, 24179066, -17655217], ![-3301525579, 5698794, 265969726], ![4521485342, -396854953, 5698794]]]
  hmulB := by decide  
  f := ![![![105583879364207314, 6868768796493397, 6531513003664214]], ![![103885031049044538, 6758250066101670, 6426420730785479]], ![![34599839484671793, 2250895678839391, 2140376948447664]]]
  g := ![![![-18004409, 24179066, -17655217], ![-92765385, 5698794, 265969726], ![388602048, -396854953, 5698794]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![105583879364207314, 6868768796493397, 6531513003664214]] ![![-64922074, 24179066, -17655217]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [81, 51, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 12, 75], [29, 84, 22], [0, 1]]
 g := ![![[45, 26, 64], [10, 73], [86, 32], [27, 33], [46, 50], [1]], ![[89, 47, 29, 50], [90, 72], [90, 85], [66, 70], [87, 33], [39, 53, 49, 22]], ![[23, 19, 75, 66], [65, 61], [28, 16], [76, 1], [85, 81], [34, 45, 51, 75]]]
 h' := ![![[41, 12, 75], [57, 48, 89], [24, 56, 48], [43, 66, 41], [22, 23, 79], [16, 46, 70], [0, 1]], ![[29, 84, 22], [34, 78, 18], [7, 71, 84], [64, 22, 52], [50, 77, 19], [93, 11, 18], [41, 12, 75]], ![[0, 1], [73, 68, 87], [10, 67, 62], [85, 9, 4], [18, 94, 96], [4, 40, 9], [29, 84, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74, 10], []]
 b := ![[], [36, 82, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [81, 51, 27, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![55969, 7372, -11058]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![577, 76, -114]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2832112, 245796, -925]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![-2832112, 245796, -925]] 
 ![![101, 0, 0], ![0, 101, 0], ![55, 15, 1]] where
  M :=![![![-2832112, 245796, -925], ![-172975, -2828412, 2703756], ![45963852, -998909, -2828412]]]
  hmulB := by decide  
  f := ![![![105947729148, 6892439077, 6554021076]], ![![1225601941212, 79731644844, 75816829847]], ![![252475646819, 16424825979, 15618368829]]]
  g := ![![![-27537, 2571, -925], ![-1474055, -429552, 2703756], ![1995312, 410171, -2828412]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [52, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [69, 100], [0, 1]]
 g := ![![[55, 68], [77], [15, 45], [30], [30], [69, 1]], ![[0, 33], [77], [90, 56], [30], [30], [37, 100]]]
 h' := ![![[69, 100], [12, 13], [28, 28], [11, 34], [37, 38], [48, 63], [0, 1]], ![[0, 1], [0, 88], [41, 73], [34, 67], [33, 63], [52, 38], [69, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [97, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [52, 32, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1726, -71, 103]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-39, -16, 103]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-105947729148, -6892439077, -6554021076]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-105947729148, -6892439077, -6554021076]] 
 ![![101, 0, 0], ![37, 1, 0], ![50, 0, 1]] where
  M :=![![![-105947729148, -6892439077, -6554021076], ![-1225601941212, -79731644844, -75816829847], ![-1288886107399, -83848601984, -79731644844]]]
  hmulB := by decide  
  f := ![![![2832112, -245796, 925]], ![![1039219, -62040, -26431]], ![![946948, -111791, 28462]]]
  g := ![![![4720530401, -6892439077, -6554021076], ![54607033766, -79731644844, -75816829847], ![57426677309, -83848601984, -79731644844]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![-2832112, 245796, -925]] ![![-105947729148, -6892439077, -6554021076]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-121170817, -20127388, 29099498]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-121170817, -20127388, 29099498]] 
 ![![103, 0, 0], ![0, 103, 0], ![51, 69, 1]] where
  M :=![![![-121170817, -20127388, 29099498], ![5441606126, -237568809, -221401268], ![-3763821556, 575201018, -237568809]]]
  hmulB := by decide  
  f := ![![![-1784360910191935, -116081759975224, -110382158321222]], ![![-20641463606068514, -1342832276907047, -1276899359727464]], ![![-14922045479163913, -970755014727015, -923091050218295]]]
  g := ![![![-15584905, -19689250, 29099498], ![162456998, 146010861, -221401268], ![81089201, 164732513, -237568809]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [42, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 102], [0, 1]]
 g := ![![[19, 100], [39, 1], [82, 46], [30], [50], [26, 1]], ![[44, 3], [65, 102], [42, 57], [30], [50], [52, 102]]]
 h' := ![![[26, 102], [10, 10], [58, 1], [25, 56], [96, 37], [41, 16], [0, 1]], ![[0, 1], [64, 93], [84, 102], [39, 47], [28, 66], [45, 87], [26, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [11, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [42, 77, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1002, 256, -262]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![120, 178, -262]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1784360910191935, -116081759975224, -110382158321222]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-1784360910191935, -116081759975224, -110382158321222]] 
 ![![103, 0, 0], ![65, 1, 0], ![56, 0, 1]] where
  M :=![![![-1784360910191935, -116081759975224, -110382158321222], ![-20641463606068514, -1342832276907047, -1276899359727464], ![-21707289115366888, -1412169651559878, -1342832276907047]]]
  hmulB := by decide  
  f := ![![![-121170817, -20127388, 29099498]], ![![-23635893, -15008243, 16214234]], ![![-102421236, -5358570, 13514593]]]
  g := ![![![115945187904719, -116081759975224, -110382158321222], ![1341252412986675, -1342832276907047, -1276899359727464], ![1410508211095338, -1412169651559878, -1342832276907047]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-121170817, -20127388, 29099498]] ![![-1784360910191935, -116081759975224, -110382158321222]]
  ![![103, 0, 0]] where
 M := ![![![103, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-256, -17, -16]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-256, -17, -16]] 
 ![![107, 0, 0], ![0, 107, 0], ![16, 88, 1]] where
  M :=![![![-256, -17, -16], ![-2992, -192, -187], ![-3179, -204, -192]]]
  hmulB := by decide  
  f := ![![![12, 0, -1]], ![![-187, 16, 0]], ![![-152, 13, 0]]]
  g := ![![![0, 13, -16], ![0, 152, -187], ![-1, 156, -192]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [31, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 106], [0, 1]]
 g := ![![[13, 19], [55, 42], [34], [32, 53], [57], [25, 1]], ![[60, 88], [35, 65], [34], [73, 54], [57], [50, 106]]]
 h' := ![![[25, 106], [7, 74], [1, 91], [78, 26], [86, 69], [81, 59], [0, 1]], ![[0, 1], [38, 33], [29, 16], [86, 81], [99, 38], [58, 48], [25, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [15, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [31, 82, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![405, -73, -75]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15, 61, -75]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12, 0, -1]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![12, 0, -1]] 
 ![![107, 0, 0], ![102, 1, 0], ![95, 0, 1]] where
  M :=![![![12, 0, -1], ![-187, 16, 0], ![0, -17, 16]]]
  hmulB := by decide  
  f := ![![![-256, -17, -16]], ![![-272, -18, -17]], ![![-257, -17, -16]]]
  g := ![![![1, 0, -1], ![-17, 16, 0], ![2, -17, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-256, -17, -16]] ![![12, 0, -1]]
  ![![107, 0, 0]] where
 M := ![![![107, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![218117377111286, 14189645643792, 13492935602539]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![218117377111286, 14189645643792, 13492935602539]] 
 ![![109, 0, 0], ![0, 109, 0], ![34, 55, 1]] where
  M :=![![![218117377111286, 14189645643792, 13492935602539], ![2523178957674793, 164145634701130, 156086102081712], ![2653463735389104, 172621322667995, 164145634701130]]]
  hmulB := by decide  
  f := ![![![9963940, 148205, -959974]], ![![-179515138, 13803836, 1630255]], ![![-87218755, 6856308, 649805]]]
  g := ![![![-2207728746560, -6678181766017, 13492935602539], ![-25538977184435, -77253119080670, 156086102081712], ![-26857686646324, -81242097118295, 164145634701130]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [95, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 108], [0, 1]]
 g := ![![[25, 81], [80], [71, 45], [39, 9], [4], [23, 1]], ![[35, 28], [80], [16, 64], [28, 100], [4], [46, 108]]]
 h' := ![![[23, 108], [90, 100], [13, 84], [1, 63], [81, 3], [104, 107], [0, 1]], ![[0, 1], [101, 9], [92, 25], [33, 46], [41, 106], [58, 2], [23, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [36, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [95, 86, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7288, 1537, 4055]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1198, -2032, 4055]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9963940, -148205, 959974]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-9963940, -148205, 959974]] 
 ![![109, 0, 0], ![49, 1, 0], ![79, 0, 1]] where
  M :=![![![-9963940, -148205, 959974], ![179515138, -13803836, -1630255], ![-27714335, 16912378, -13803836]]]
  hmulB := by decide  
  f := ![![![-218117377111286, -14189645643792, -13492935602539]], ![![-121201196661723, -7884754782082, -7497614189047]], ![![-182428775478722, -11867920445207, -11285206855979]]]
  g := ![![![-720549, -148205, 959974], ![9033883, -13803836, -1630255], ![2147543, 16912378, -13803836]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![218117377111286, 14189645643792, 13492935602539]] ![![-9963940, -148205, 959974]]
  ![![109, 0, 0]] where
 M := ![![![-109, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-81750712112334, -5318299950993, -5057172008036]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-81750712112334, -5318299950993, -5057172008036]] 
 ![![113, 0, 0], ![0, 113, 0], ![48, 111, 1]] where
  M :=![![![-81750712112334, -5318299950993, -5057172008036], ![-945691165502732, -61522024080190, -58501299460923], ![-994522090835691, -64698724332640, -61522024080190]]]
  hmulB := by decide  
  f := ![![![-5460260, 752510, -266723]], ![![-49877201, -4393368, 8277610]], ![![-50068517, -4062723, 7978926]]]
  g := ![![![1424721630738, 4920599937531, -5057172008036], ![16481161138244, 56921435540551, -58501299460923], ![17332168716933, 59860583615650, -61522024080190]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [42, 110, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 112], [0, 1]]
 g := ![![[8, 30], [62], [82], [106], [57, 72], [3, 1]], ![[98, 83], [62], [82], [106], [47, 41], [6, 112]]]
 h' := ![![[3, 112], [52, 97], [31, 66], [57, 46], [92, 28], [100, 80], [0, 1]], ![[0, 1], [4, 16], [3, 47], [82, 67], [63, 85], [1, 33], [3, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [81, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [42, 110, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1189, 365, -13]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5, 16, -13]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5460260, 752510, -266723]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-5460260, 752510, -266723]] 
 ![![113, 0, 0], ![22, 1, 0], ![69, 0, 1]] where
  M :=![![![-5460260, 752510, -266723], ![-49877201, -4393368, 8277610], ![140719370, -7544331, -4393368]]]
  hmulB := by decide  
  f := ![![![-81750712112334, -5318299950993, -5057172008036]], ![![-24285016212160, -1579863920372, -1502292775555]], ![![-58719656872449, -3820012574789, -3632450377298]]]
  g := ![![![-31961, 752510, -266723], ![-4640515, -4393368, 8277610], ![5396788, -7544331, -4393368]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-81750712112334, -5318299950993, -5057172008036]] ![![-5460260, 752510, -266723]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101580122, 6608304, 6283837]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![101580122, 6608304, 6283837]] 
 ![![127, 0, 0], ![8, 1, 0], ![75, 0, 1]] where
  M :=![![![101580122, 6608304, 6283837], ![1175077519, 76444774, 72691344], ![1235752848, 80392013, 76444774]]]
  hmulB := by decide  
  f := ![![![75604, -9415, 2738]], ![![8794, -84, -643]], ![![30785, -4897, 2126]]]
  g := ![![![-3327355, 6608304, 6283837], ![-38490799, 76444774, 72691344], ![-40478278, 80392013, 76444774]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-382560214685124285567782, -24887489276130791698526, -23665516288535947333617]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-382560214685124285567782, -24887489276130791698526, -23665516288535947333617]] 
 ![![127, 0, 0], ![13, 1, 0], ![77, 0, 1]] where
  M :=![![![-382560214685124285567782, -24887489276130791698526, -23665516288535947333617], ![-4425451545956222151386379, -287898149530980496233314, -273762382037438708683786], ![-4653960494636458047624362, -302763819800587937877385, -287898149530980496233314]]]
  hmulB := by decide  
  f := ![![![-2433917842986, 553811343619, -326548782698]], ![![-729964994672, 47809643739, 14541658305]], ![![-660227973647, 274621250223, -206865976220]]]
  g := ![![![13883637008833416938595, -24887489276130791698526, -23665516288535947333617], ![160605730825427597388175, -287898149530980496233314, -273762382037438708683786], ![168898635249265223265723, -302763819800587937877385, -287898149530980496233314]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1087119685236888882480101074, -70722669189404875256115158, -67250193906695495597941753]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![-1087119685236888882480101074, -70722669189404875256115158, -67250193906695495597941753]] 
 ![![127, 0, 0], ![106, 1, 0], ![110, 0, 1]] where
  M :=![![![-1087119685236888882480101074, -70722669189404875256115158, -67250193906695495597941753], ![-12575786260552057676815107811, -818118909610106900088334062, -777949361083453627817266738], ![-13225139138418711672893534546, -860362619656203924140549169, -818118909610106900088334062]]]
  hmulB := by decide  
  f := ![![![-226470632179122, -6501248641461, 24798150876082]], ![![-152508919662674, -7990516469908, 20134568959123]], ![![-205728370359501, -2106801504736, 18914435910910]]]
  g := ![![![108716571484854585908989752, -70722669189404875256115158, -67250193906695495597941753], ![1257631873049599785767304283, -818118909610106900088334062, -777949361083453627817266738], ![1322569910253942230674971844, -860362619656203924140549169, -818118909610106900088334062]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![101580122, 6608304, 6283837]] ![![-382560214685124285567782, -24887489276130791698526, -23665516288535947333617]]
  ![![-97349971585744679809643076757614, -6333111183205501151661065465873, -6022156120304310988393546466036]] where
 M := ![![![-97349971585744679809643076757614, -6333111183205501151661065465873, -6022156120304310988393546466036]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![-97349971585744679809643076757614, -6333111183205501151661065465873, -6022156120304310988393546466036]] ![![-1087119685236888882480101074, -70722669189404875256115158, -67250193906695495597941753]]
  ![![127, 0, 0]] where
 M := ![![![265118775676723486356072913521407497475407921515557736991095, 17247325867343902446863624987337560300982600805209168303222, 16400484063243015811760203527771636539048553258291453207848]]]
 hmul := by decide  
 g := ![![![![2087549414777350286268290657648877932877227728468958558985, 135805715490896869660343503837303624417185833111883214986, 129137669789315085131970106517886901882272072899932702424]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [42, 34, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 68, 3], [33, 62, 128], [0, 1]]
 g := ![![[23, 55, 28], [50, 77, 43], [116, 80], [20, 21], [2, 28], [115, 1], []], ![[53, 36, 61, 102], [32, 85, 94, 20], [29, 5], [50, 100], [119, 105], [56, 45], [2, 9]], ![[32, 40, 73, 67], [0, 40, 52, 26], [0, 45], [23, 125], [42, 108], [80, 39], [8, 9]]]
 h' := ![![[82, 68, 3], [127, 15, 91], [87, 84, 49], [51, 75, 39], [74, 104, 105], [17, 109, 91], [0, 0, 1], [0, 1]], ![[33, 62, 128], [115, 102, 54], [119, 18, 15], [17, 28, 23], [105, 17, 10], [115, 75, 74], [90, 95, 62], [82, 68, 3]], ![[0, 1], [108, 14, 117], [63, 29, 67], [60, 28, 69], [41, 10, 16], [87, 78, 97], [98, 36, 68], [33, 62, 128]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118, 122], []]
 b := ![[], [53, 29, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [42, 34, 16, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![30523, 1048, 2096]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![233, 8, 16]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-422412241987129, 329479496018398, -278579379547688]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-422412241987129, 329479496018398, -278579379547688]] 
 ![![137, 0, 0], ![0, 137, 0], ![65, 93, 1]] where
  M :=![![![-422412241987129, 329479496018398, -278579379547688], ![-52094343975417656, 691905276203623, 3624274456202378], ![61612665755440426, -6053767436384288, 691905276203623]]]
  hmulB := by decide  
  f := ![![![-163644143027122198368315808489, -10645884486553960316861223870, -10123172728558320939344716964]], ![![-1893033300240406015657462072268, -123151452112888914610936940633, -117104729352093563485473462570]], ![![-1377224427869388999484215687127, -89595459390977752511784892871, -85196332184042928319834858119]]]
  g := ![![![129089397289143, 191513589736886, -278579379547688], ![-2099796960792498, -2455223497449763, 3624274456202378], ![121451261329963, -513875606739571, 691905276203623]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [125, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [95, 136], [0, 1]]
 g := ![![[65, 119], [18], [130], [83, 88], [126], [120], [1]], ![[136, 18], [18], [130], [86, 49], [126], [120], [1]]]
 h' := ![![[95, 136], [43, 121], [52, 44], [37, 104], [43, 122], [77, 117], [12, 95], [0, 1]], ![[0, 1], [30, 16], [122, 93], [53, 33], [125, 15], [95, 20], [132, 42], [95, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [34, 106]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [125, 42, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7267, -232, 1176]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-611, -800, 1176]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-163644143027122198368315808489, -10645884486553960316861223870, -10123172728558320939344716964]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-163644143027122198368315808489, -10645884486553960316861223870, -10123172728558320939344716964]] 
 ![![137, 0, 0], ![73, 1, 0], ![76, 0, 1]] where
  M :=![![![-163644143027122198368315808489, -10645884486553960316861223870, -10123172728558320939344716964], ![-1893033300240406015657462072268, -123151452112888914610936940633, -117104729352093563485473462570], ![-1990780398985590579253048863690, -129510398439275614701415292908, -123151452112888914610936940633]]]
  hmulB := by decide  
  f := ![![![-422412241987129, 329479496018398, -278579379547688]], ![![-605331661609329, 180612470697421, -121985549275758]], ![![215396608499406, 138588863219080, -149489982258545]]]
  g := ![![![10093916436947075154399649805, -10645884486553960316861223870, -10123172728558320939344716964], ![116766292954449602743335166053, -123151452112888914610936940633, -117104729352093563485473462570], ![122795540493876546017383029246, -129510398439275614701415292908, -123151452112888914610936940633]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-422412241987129, 329479496018398, -278579379547688]] ![![-163644143027122198368315808489, -10645884486553960316861223870, -10123172728558320939344716964]]
  ![![137, 0, 0]] where
 M := ![![![137, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB276I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB276I2 : PrimesBelowBoundCertificateInterval O 79 137 276 where
  m := 11
  g := ![3, 2, 1, 2, 2, 2, 2, 2, 3, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB276I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0]
    · exact ![I137N0, I137N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![83, 83, 83]
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![127, 127, 127]
    · exact ![2248091]
    · exact ![18769, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N0, I83N1, I83N2, I89N1, I101N1, I103N1, I107N1, I109N1, I113N1, I127N0, I127N1, I127N2, I137N1]
  Il := ![[I83N0, I83N1, I83N2], [I89N1], [], [I101N1], [I103N1], [I107N1], [I109N1], [I113N1], [I127N0, I127N1, I127N2], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
