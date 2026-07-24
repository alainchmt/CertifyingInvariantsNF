
import IdealArithmetic.Examples.NF3_1_551980_3.RI3_1_551980_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![13, -45, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![13, -45, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![13, 94, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![13, -45, 1], ![-155, 34, -44], ![6820, -1079, -10]]]
  hmulB := by decide  
  f := ![![![-12, 45, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -94, 139]], ![![0, -1, 1], ![3, 30, -44], ![50, -1, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [72, 98, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 138], [0, 1]]
 g := ![![[67, 11], [101, 80], [77], [70, 47], [137], [13], [1]], ![[101, 128], [45, 59], [77], [51, 92], [137], [13], [1]]]
 h' := ![![[41, 138], [95, 17], [61, 48], [103, 76], [112, 73], [78, 50], [67, 41], [0, 1]], ![[0, 1], [97, 122], [83, 91], [22, 63], [47, 66], [43, 89], [80, 98], [41, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [60, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [72, 98, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-393, -190, -73]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, 48, -73]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![44, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![44, 1, 0]] 
 ![![139, 0, 0], ![44, 1, 0], ![10, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![44, 1, 0], ![0, 44, 1], ![-155, 21, 45]]]
  hmulB := by decide  
  f := ![![![2333, 53, 0], ![-7367, 0, 0]], ![![660, 15, 0], ![-2084, 0, 0]], ![![102, 2, 0], ![-322, 1, 0]]]
  g := ![![![1, 0, 0], ![-44, 139, 0], ![-10, 0, 139]], ![![0, 1, 0], ![-14, 44, 1], ![-11, 21, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![13, -45, 1]] ![![139, 0, 0], ![44, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![6116, 139, 0]], ![![1807, -6255, 139], ![417, -1946, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![44, 1, 0]]], ![![![13, -45, 1]], ![![3, -14, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![47, -36, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![47, -36, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![47, 113, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![47, -36, 1], ![-155, 68, -35], ![5425, -890, 33]]]
  hmulB := by decide  
  f := ![![![-46, 36, -1], ![149, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -113, 149]], ![![0, -1, 1], ![10, 27, -35], ![26, -31, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [126, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [105, 148], [0, 1]]
 g := ![![[24, 64], [1], [109, 1], [110], [139, 61], [148], [1]], ![[39, 85], [1], [65, 148], [110], [137, 88], [148], [1]]]
 h' := ![![[105, 148], [103, 8], [123, 148], [2, 1], [68, 109], [59, 106], [23, 105], [0, 1]], ![[0, 1], [49, 141], [18, 1], [107, 148], [40, 40], [14, 43], [22, 44], [105, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [47, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [126, 44, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![548, -1542, 316]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-96, -250, 316]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![35, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![35, 1, 0]] 
 ![![149, 0, 0], ![35, 1, 0], ![116, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![35, 1, 0], ![0, 35, 1], ![-155, 21, 36]]]
  hmulB := by decide  
  f := ![![![2731, 78, 0], ![-11622, 0, 0]], ![![595, 17, 0], ![-2532, 0, 0]], ![![2144, 61, 0], ![-9124, 1, 0]]]
  g := ![![![1, 0, 0], ![-35, 149, 0], ![-116, 0, 149]], ![![0, 1, 0], ![-9, 35, 1], ![-34, 21, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![47, -36, 1]] ![![149, 0, 0], ![35, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![5215, 149, 0]], ![![7003, -5364, 149], ![1490, -1192, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![35, 1, 0]]], ![![![47, -36, 1]], ![![10, -8, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![244459239622996, -72059986746053, 9901217116316]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![244459239622996, -72059986746053, 9901217116316]] 
 ![![151, 0, 0], ![24, 1, 0], ![28, 0, 1]] where
  M :=![![![244459239622996, -72059986746053, 9901217116316], ![-1534688653028980, 452384799065632, -62158769629737], ![9634609292609235, -2840022815253457, 390226029435895]]]
  hmulB := by decide  
  f := ![![![342409831, 17668023, -5873651]], ![![60451999, 4258912, -855452]], ![![51386408, 10945711, 439704]]]
  g := ![![![11236191008420, -72059986746053, 9901217116316], ![-70539591264712, 452384799065632, -62158769629737], ![442839920758193, -2840022815253457, 390226029435895]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-474, 94, 27]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-474, 94, 27]] 
 ![![151, 0, 0], ![133, 1, 0], ![129, 0, 1]] where
  M :=![![![-474, 94, 27], ![-4185, 93, 121], ![-18755, -1644, 214]]]
  hmulB := by decide  
  f := ![![![218826, -64504, 8863]], ![![183643, -54133, 7438]], ![![244059, -71942, 9885]]]
  g := ![![![-109, 94, 27], ![-213, 93, 121], ![1141, -1644, 214]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-70806, 47721, 9398]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![-70806, 47721, 9398]] 
 ![![151, 0, 0], ![144, 1, 0], ![102, 0, 1]] where
  M :=![![![-70806, 47721, 9398], ![-1456690, 126552, 57119], ![-8853445, -257191, 183671]]]
  hmulB := by decide  
  f := ![![![-37934425121, 11182044809, -1536440103]], ![![-34598735109, 10198773412, -1401336226]], ![![-35525695972, 10472016459, -1438880484]]]
  g := ![![![-52326, 47721, 9398], ![-168916, 126552, 57119], ![62567, -257191, 183671]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![244459239622996, -72059986746053, 9901217116316]] ![![-474, 94, 27]]
  ![![37934425121, -11182044809, 1536440103]] where
 M := ![![![37934425121, -11182044809, 1536440103]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![37934425121, -11182044809, 1536440103]] ![![-70806, 47721, 9398]]
  ![![151, 0, 0]] where
 M := ![![![-151, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-30, -22, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-30, -22, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![127, 135, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-30, -22, 1], ![-155, -9, -21], ![3255, -596, -30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-127, -135, 157]], ![![-1, -1, 1], ![16, 18, -21], ![45, 22, -30]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [98, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [135, 156], [0, 1]]
 g := ![![[138, 33], [100], [123, 82], [25, 121], [22, 153], [13], [1]], ![[40, 124], [100], [46, 75], [32, 36], [110, 4], [13], [1]]]
 h' := ![![[135, 156], [60, 70], [35, 10], [62, 32], [42, 146], [9, 101], [59, 135], [0, 1]], ![[0, 1], [90, 87], [129, 147], [143, 125], [127, 11], [142, 56], [72, 22], [135, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [116]]
 b := ![[], [10, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [98, 22, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2941, -282, 127]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-84, -111, 127]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![21, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![21, 1, 0]] 
 ![![157, 0, 0], ![21, 1, 0], ![30, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![21, 1, 0], ![0, 21, 1], ![-155, 21, 22]]]
  hmulB := by decide  
  f := ![![![274, 13, 0], ![-2041, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![24, 1, 0], ![-178, 1, 0]]]
  g := ![![![1, 0, 0], ![-21, 157, 0], ![-30, 0, 157]], ![![0, 1, 0], ![-3, 21, 1], ![-8, 21, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-30, -22, 1]] ![![157, 0, 0], ![21, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![3297, 157, 0]], ![![-4710, -3454, 157], ![-785, -471, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![21, 1, 0]]], ![![![-30, -22, 1]], ![![-5, -3, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-564, 268, 57]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-564, 268, 57]] 
 ![![163, 0, 0], ![0, 163, 0], ![33, 19, 1]] where
  M :=![![![-564, 268, 57], ![-8835, 633, 325], ![-50375, -2010, 958]]]
  hmulB := by decide  
  f := ![![![7728, -2278, 313]], ![![-48515, 14301, -1965]], ![![-2222, 655, -90]]]
  g := ![![![-15, -5, 57], ![-120, -34, 325], ![-503, -124, 958]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [54, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 162], [0, 1]]
 g := ![![[65, 160], [107, 1], [61], [10], [51], [122, 71], [1]], ![[0, 3], [20, 162], [61], [10], [51], [139, 92], [1]]]
 h' := ![![[76, 162], [90, 46], [66, 162], [10, 86], [77, 93], [95, 41], [109, 76], [0, 1]], ![[0, 1], [0, 117], [153, 1], [26, 77], [136, 70], [114, 122], [17, 87], [76, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [131, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [54, 87, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-323, -1243, -74]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![13, 1, -74]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7728, -2278, 313]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![7728, -2278, 313]] 
 ![![163, 0, 0], ![143, 1, 0], ![89, 0, 1]] where
  M :=![![![7728, -2278, 313], ![-48515, 14301, -1965], ![304575, -89780, 12336]]]
  hmulB := by decide  
  f := ![![![-564, 268, 57]], ![![-549, 239, 52]], ![![-617, 134, 37]]]
  g := ![![![1875, -2278, 313], ![-11771, 14301, -1965], ![73897, -89780, 12336]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-564, 268, 57]] ![![7728, -2278, 313]]
  ![![163, 0, 0]] where
 M := ![![![163, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [83, 5, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [117, 141, 39], [6, 25, 128], [0, 1]]
 g := ![![[67, 143, 47], [99, 109, 124], [54, 54, 63], [38, 84], [105, 81], [94, 123, 1], []], ![[23, 83, 113, 134], [119, 67, 61, 163], [70, 154, 34, 156], [34, 114], [90, 114], [131, 137, 105, 160], [19, 18]], ![[156, 117, 120, 18], [81, 159, 40, 57], [102, 131, 19, 21], [122, 58], [12, 42], [41, 29, 18, 22], [97, 18]]]
 h' := ![![[117, 141, 39], [133, 38, 106], [27, 39, 142], [68, 70, 118], [7, 111, 77], [47, 9, 9], [0, 0, 1], [0, 1]], ![[6, 25, 128], [46, 133, 124], [52, 97, 61], [105, 77, 2], [64, 145, 75], [55, 14, 75], [88, 9, 25], [117, 141, 39]], ![[0, 1], [133, 163, 104], [69, 31, 131], [105, 20, 47], [82, 78, 15], [110, 144, 83], [1, 158, 141], [6, 25, 128]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120, 59], []]
 b := ![[], [109, 11, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [83, 5, 44, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26887, 1169, 1169]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-161, 7, 7]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def PBC167 : ContainsPrimesAboveP 167 ![I167N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![167, 0, 0]]) timesTableT_eq_Table B_one_repr 167 (by decide) 𝕀

instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23569566, 6947672, -954627]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-23569566, 6947672, -954627]] 
 ![![173, 0, 0], ![0, 173, 0], ![110, 147, 1]] where
  M :=![![![-23569566, 6947672, -954627], ![147967185, -43616733, 5993045], ![-928921975, 273821130, -37623688]]]
  hmulB := by decide  
  f := ![![![402, 1238, 187]], ![![-28985, 4329, 1425]], ![![-25650, 4471, 1363]]]
  g := ![![![470748, 851317, -954627], ![-2955305, -5344476, 5993045], ![18553085, 33552042, -37623688]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [14, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 172], [0, 1]]
 g := ![![[105, 136], [135], [47, 149], [25, 83], [122], [51, 130], [1]], ![[0, 37], [135], [35, 24], [153, 90], [122], [116, 43], [1]]]
 h' := ![![[87, 172], [131, 84], [34, 116], [169, 144], [160, 157], [151, 45], [159, 87], [0, 1]], ![[0, 1], [0, 89], [92, 57], [68, 29], [152, 16], [87, 128], [116, 86], [87, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [83, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [14, 86, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5944, 2336, 509]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-358, -419, 509]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![402, 1238, 187]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![402, 1238, 187]] 
 ![![173, 0, 0], ![25, 1, 0], ![67, 0, 1]] where
  M :=![![![402, 1238, 187], ![-28985, 4329, 1425], ![-220875, 940, 5754]]]
  hmulB := by decide  
  f := ![![![-23569566, 6947672, -954627]], ![![-2550705, 751879, -103310]], ![![-14497589, 4273498, -587189]]]
  g := ![![![-249, 1238, 187], ![-1345, 4329, 1425], ![-3641, 940, 5754]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-23569566, 6947672, -954627]] ![![402, 1238, 187]]
  ![![173, 0, 0]] where
 M := ![![![173, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-57279314, 16884396, -2319957]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-57279314, 16884396, -2319957]] 
 ![![179, 0, 0], ![27, 1, 0], ![166, 0, 1]] where
  M :=![![![-57279314, 16884396, -2319957], ![359593335, -105998411, 14564439], ![-2257488045, 665446554, -91433972]]]
  hmulB := by decide  
  f := ![![![74714, -22734, -5517]], ![![16047, -3659, -990]], ![![93751, -19620, -5504]]]
  g := ![![![-715336, 16884396, -2319957], ![4490802, -105998411, 14564439], ![-28192769, 665446554, -91433972]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![64, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![64, 1, 0]] 
 ![![179, 0, 0], ![64, 1, 0], ![21, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![64, 1, 0], ![0, 64, 1], ![-155, 21, 65]]]
  hmulB := by decide  
  f := ![![![769, 12, 0], ![-2148, 0, 0]], ![![192, 3, 0], ![-536, 0, 0]], ![![23, 0, 0], ![-64, 1, 0]]]
  g := ![![![1, 0, 0], ![-64, 179, 0], ![-21, 0, 179]], ![![0, 1, 0], ![-23, 64, 1], ![-16, 21, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![87, 1, 0]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![179, 0, 0], ![87, 1, 0]] 
 ![![179, 0, 0], ![87, 1, 0], ![128, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![87, 1, 0], ![0, 87, 1], ![-155, 21, 88]]]
  hmulB := by decide  
  f := ![![![4786, 55, 0], ![-9845, 0, 0]], ![![2262, 26, 0], ![-4653, 0, 0]], ![![3436, 39, 0], ![-7068, 1, 0]]]
  g := ![![![1, 0, 0], ![-87, 179, 0], ![-128, 0, 179]], ![![0, 1, 0], ![-43, 87, 1], ![-74, 21, 88]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-57279314, 16884396, -2319957]] ![![179, 0, 0], ![64, 1, 0]]
  ![![179, 0, 0], ![-62, -88, 1]] where
 M := ![![![-10252997206, 3022306884, -415272303], ![-3306282761, 974602933, -133912809]]]
 hmul := by decide  
 g := ![![![![-54347458, 21045740, -2367245], ![8464552, 0, 0]], ![![-17525369, 6786687, -763366], ![2729705, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-62, -88, 1]] ![![179, 0, 0], ![87, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![15573, 179, 0]], ![![-11098, -15752, 179], ![-5549, -7697, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![87, 1, 0]]], ![![![-62, -88, 1]], ![![-31, -43, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1, I179N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
    exact isPrimeI179N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0 ⊙ MulI179N1)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [31, 37, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 105, 74], [137, 75, 107], [0, 1]]
 g := ![![[35, 100, 44], [132, 94], [53, 55, 81], [7, 94], [152, 19, 133], [2, 138, 1], []], ![[119, 4, 68, 171], [1, 60], [37, 20, 174, 98], [136, 136], [47, 81, 117, 109], [94, 83, 75, 131], [168, 46]], ![[174, 163, 136, 85], [64, 45], [179, 86, 14, 141], [132, 102], [128, 83, 83, 71], [106, 138, 121, 98], [135, 46]]]
 h' := ![![[1, 105, 74], [86, 6, 166], [167, 135, 53], [0, 96, 9], [175, 165, 128], [119, 173, 26], [0, 0, 1], [0, 1]], ![[137, 75, 107], [5, 71, 43], [175, 17, 28], [112, 26, 177], [105, 170, 90], [117, 141, 91], [42, 170, 75], [1, 105, 74]], ![[0, 1], [72, 104, 153], [101, 29, 100], [151, 59, 176], [73, 27, 144], [98, 48, 64], [104, 11, 105], [137, 75, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129, 129], []]
 b := ![[], [165, 132, 123], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [31, 37, 43, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17014, 2172, -724]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-94, 12, -4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def PBC181 : ContainsPrimesAboveP 181 ![I181N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![181, 0, 0]]) timesTableT_eq_Table B_one_repr 181 (by decide) 𝕀

instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![67, 1, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![67, 1, 0]] 
 ![![191, 0, 0], ![67, 1, 0], ![95, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![67, 1, 0], ![0, 67, 1], ![-155, 21, 68]]]
  hmulB := by decide  
  f := ![![![4959, 74, 0], ![-14134, 0, 0]], ![![1675, 25, 0], ![-4774, 0, 0]], ![![2503, 37, 0], ![-7134, 1, 0]]]
  g := ![![![1, 0, 0], ![-67, 191, 0], ![-95, 0, 191]], ![![0, 1, 0], ![-24, 67, 1], ![-42, 21, 68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N0 : Nat.card (O ⧸ I191N0) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N0)

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := prime_ideal_of_norm_prime hp191.out _ NI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13436199, 439001, -270989]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![13436199, 439001, -270989]] 
 ![![191, 0, 0], ![136, 1, 0], ![31, 0, 1]] where
  M :=![![![13436199, 439001, -270989], ![42003295, 7745430, 168012], ![-26041860, 45531547, 7913442]]]
  hmulB := by decide  
  f := ![![![-53643164795496, 15812557341425, -2172683766282]], ![![-36433007478606, 10739467406002, -1475628893399]], ![![-19775489595851, 5829280661968, -800957314487]]]
  g := ![![![-198258, 439001, -270989], ![-5322427, 7745430, 168012], ![-33841094, 45531547, 7913442]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-13, 1, 0]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-13, 1, 0]] 
 ![![191, 0, 0], ![178, 1, 0], ![22, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-13, 1, 0], ![0, -13, 1], ![-155, 21, -12]]]
  hmulB := by decide  
  f := ![![![1990, -153, 0], ![29223, 0, 0]], ![![1860, -143, 0], ![27314, 0, 0]], ![![248, -19, 0], ![3642, 1, 0]]]
  g := ![![![1, 0, 0], ![-178, 191, 0], ![-22, 0, 191]], ![![-1, 1, 0], ![12, -13, 1], ![-19, 21, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![67, 1, 0]] ![![13436199, 439001, -270989]]
  ![![191, 0, 0], ![-56, 12, 1]] where
 M := ![![![2566314009, 83849191, -51758899]], ![![942228628, 37158497, -17988251]]]
 hmul := by decide  
 g := ![![![![12383567, 664565, -252192], ![-3590227, 0, 0]]], ![![![4547220, 277243, -87288], ![-1316243, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-56, 12, 1]] ![![191, 0, 0], ![-13, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-2483, 191, 0]], ![![-10696, 2292, 191], ![573, -191, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-13, 1, 0]]], ![![![-56, 12, 1]], ![![3, -1, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1)

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-70, 1, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-70, 1, 0]] 
 ![![193, 0, 0], ![123, 1, 0], ![118, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-70, 1, 0], ![0, -70, 1], ![-155, 21, -69]]]
  hmulB := by decide  
  f := ![![![8611, -123, 0], ![23739, 0, 0]], ![![5461, -78, 0], ![15055, 0, 0]], ![![5346, -76, 0], ![14738, 1, 0]]]
  g := ![![![1, 0, 0], ![-123, 193, 0], ![-118, 0, 193]], ![![-1, 1, 0], ![44, -70, 1], ![28, 21, -69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N0 : Nat.card (O ⧸ I193N0) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N0)

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := prime_ideal_of_norm_prime hp193.out _ NI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-62, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-62, 1, 0]] 
 ![![193, 0, 0], ![131, 1, 0], ![16, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-62, 1, 0], ![0, -62, 1], ![-155, 21, -61]]]
  hmulB := by decide  
  f := ![![![11099, -179, 0], ![34547, 0, 0]], ![![7565, -122, 0], ![23547, 0, 0]], ![![1012, -16, 0], ![3150, 1, 0]]]
  g := ![![![1, 0, 0], ![-131, 193, 0], ![-16, 0, 193]], ![![-1, 1, 0], ![42, -62, 1], ![-10, 21, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-70, 1, 0]] ![![193, 0, 0], ![-62, 1, 0]]
  ![![193, 0, 0], ![-99, 61, 1]] where
 M := ![![![37249, 0, 0], ![-11966, 193, 0]], ![![-13510, 193, 0], ![4340, -132, 1]]]
 hmul := by decide  
 g := ![![![![193, 0, 0], ![0, 0, 0]], ![![37, -60, -1], ![193, 0, 0]]], ![![![29, -60, -1], ![193, 0, 0]], ![![23, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-99, 61, 1]] ![![193, 0, 0], ![-62, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-11966, 193, 0]], ![![-19107, 11773, 193], ![5983, -3860, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-62, 1, 0]]], ![![![-99, 61, 1]], ![![31, -20, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0 ⊙ MulI193N1)


lemma PB211I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB211I3 : PrimesBelowBoundCertificateInterval O 137 193 211 where
  m := 11
  g := ![2, 2, 3, 2, 2, 1, 2, 3, 1, 3, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB211I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0]
    · exact ![I191N0, I191N1, I191N2]
    · exact ![I193N0, I193N1, I193N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![29929, 173]
    · exact ![179, 179, 179]
    · exact ![5929741]
    · exact ![191, 191, 191]
    · exact ![193, 193, 193]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
      exact NI179N2
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N1
  β := ![I139N1, I149N1, I151N0, I151N1, I151N2, I157N1, I163N1, I173N1, I179N0, I179N1, I179N2, I191N0, I191N1, I191N2, I193N0, I193N1]
  Il := ![[I139N1], [I149N1], [I151N0, I151N1, I151N2], [I157N1], [I163N1], [], [I173N1], [I179N0, I179N1, I179N2], [], [I191N0, I191N1, I191N2], [I193N0, I193N1, I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
