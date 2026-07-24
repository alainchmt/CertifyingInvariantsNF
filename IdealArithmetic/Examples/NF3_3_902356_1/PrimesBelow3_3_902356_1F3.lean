
import IdealArithmetic.Examples.NF3_3_902356_1.RI3_3_902356_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27355, 154, 777]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-27355, 154, 777]] 
 ![![139, 0, 0], ![70, 1, 0], ![35, 0, 1]] where
  M :=![![![-27355, 154, 777], ![308, -6, -7], ![10878, -49, -314]]]
  hmulB := by decide  
  f := ![![![-1541, -10283, -3584]], ![![-924, -6166, -2149]], ![![-749, -4998, -1742]]]
  g := ![![![-470, 154, 777], ![7, -6, -7], ![182, -49, -314]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, 0, 1]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-37, 0, 1]] 
 ![![139, 0, 0], ![88, 1, 0], ![102, 0, 1]] where
  M :=![![![-37, 0, 1], ![0, -2, -1], ![14, -7, -2]]]
  hmulB := by decide  
  f := ![![![-3, -7, 2]], ![![-2, -4, 1]], ![![-2, -7, 2]]]
  g := ![![![-1, 0, 1], ![2, -2, -1], ![6, -7, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-187, 3, 6]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![-187, 3, 6]] 
 ![![139, 0, 0], ![120, 1, 0], ![71, 0, 1]] where
  M :=![![![-187, 3, 6], ![6, 26, 9], ![84, 63, 20]]]
  hmulB := by decide  
  f := ![![![47, -318, 129]], ![![36, -244, 99]], ![![37, -249, 101]]]
  g := ![![![-7, 3, 6], ![-27, 26, 9], ![-64, 63, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-27355, 154, 777]] ![![-37, 0, 1]]
  ![![1023013, -5747, -29063]] where
 M := ![![![1023013, -5747, -29063]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![1023013, -5747, -29063]] ![![-187, 3, 6]]
  ![![139, 0, 0]] where
 M := ![![![-193779205, 1088648, 5505095]]]
 hmul := by decide  
 g := ![![![![-1394095, 7832, 39605]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2747, 19085, -7739]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-2747, 19085, -7739]] 
 ![![149, 0, 0], ![0, 149, 0], ![59, 18, 1]] where
  M :=![![![-2747, 19085, -7739], ![38170, -254527, 103164], ![-108346, 722148, -292697]]]
  hmulB := by decide  
  f := ![![![2597, 17323, 6037]], ![![34646, 231215, 80578]], ![![5781, 38577, 13444]]]
  g := ![![![3046, 1063, -7739], ![-40594, -14171, 103164], ![115173, 40206, -292697]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [18, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 148], [0, 1]]
 g := ![![[88, 102], [116], [136, 9], [88], [51, 69], [45], [1]], ![[36, 47], [116], [35, 140], [88], [121, 80], [45], [1]]]
 h' := ![![[55, 148], [71, 129], [85, 50], [35, 146], [125, 104], [110, 48], [131, 55], [0, 1]], ![[0, 1], [14, 20], [4, 99], [19, 3], [34, 45], [68, 101], [27, 94], [55, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105]]
 b := ![[], [9, 127]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [18, 94, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![192, 349, 425]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-167, -49, 425]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2597, 17323, 6037]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![2597, 17323, 6037]] 
 ![![149, 0, 0], ![60, 1, 0], ![73, 0, 1]] where
  M :=![![![2597, 17323, 6037], ![34646, 231215, 80578], ![84518, 564046, 196569]]]
  hmulB := by decide  
  f := ![![![-2747, 19085, -7739]], ![![-850, 5977, -2424]], ![![-2073, 14197, -5756]]]
  g := ![![![-9916, 17323, 6037], ![-132352, 231215, 80578], ![-322871, 564046, 196569]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-2747, 19085, -7739]] ![![2597, 17323, 6037]]
  ![![149, 0, 0]] where
 M := ![![![149, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-68663, -458232, -159693]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-68663, -458232, -159693]] 
 ![![151, 0, 0], ![0, 151, 0], ![147, 110, 1]] where
  M :=![![![-68663, -458232, -159693], ![-916464, -6116150, -2131467], ![-2235702, -14920269, -5199686]]]
  hmulB := by decide  
  f := ![![![-9773, 15, 294]], ![![30, 532, -219]], ![![-9465, 392, 130]]]
  g := ![![![155008, 113298, -159693], ![2068935, 1512220, -2131467], ![5047140, 3689041, -5199686]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [150, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [135, 150], [0, 1]]
 g := ![![[135, 78], [32, 21], [47, 84], [144], [120, 34], [105], [1]], ![[95, 73], [149, 130], [62, 67], [144], [29, 117], [105], [1]]]
 h' := ![![[135, 150], [32, 57], [47, 126], [48, 101], [120, 139], [106, 100], [1, 135], [0, 1]], ![[0, 1], [26, 94], [145, 25], [93, 50], [10, 12], [16, 51], [106, 16], [135, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [137, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [150, 16, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2621, -1183, 6253]
  a := ![5, 0, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6070, -4563, 6253]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9773, 15, 294]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-9773, 15, 294]] 
 ![![151, 0, 0], ![55, 1, 0], ![79, 0, 1]] where
  M :=![![![-9773, 15, 294], ![30, 532, -219], ![4116, -1533, 502]]]
  hmulB := by decide  
  f := ![![![-68663, -458232, -159693]], ![![-31079, -207410, -72282]], ![![-50729, -338547, -117983]]]
  g := ![![![-224, 15, 294], ![-79, 532, -219], ![323, -1533, 502]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-68663, -458232, -159693]] ![![-9773, 15, 294]]
  ![![151, 0, 0]] where
 M := ![![![151, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2975, -279, 23]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![2975, -279, 23]] 
 ![![157, 0, 0], ![0, 157, 0], ![143, 22, 1]] where
  M :=![![![2975, -279, 23], ![-558, 3501, -1418], ![322, -9926, 4059]]]
  hmulB := by decide  
  f := ![![![863, 5759, 2007]], ![![11518, 76867, 26788]], ![![2579, 17211, 5998]]]
  g := ![![![-2, -5, 23], ![1288, 221, -1418], ![-3695, -632, 4059]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [111, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 156], [0, 1]]
 g := ![![[22, 58], [36], [6, 67], [13, 143], [30, 37], [33], [1]], ![[0, 99], [36], [143, 90], [132, 14], [108, 120], [33], [1]]]
 h' := ![![[70, 156], [117, 23], [119, 6], [127, 99], [124, 92], [23, 115], [46, 70], [0, 1]], ![[0, 1], [0, 134], [68, 151], [149, 58], [127, 65], [66, 42], [79, 87], [70, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136]]
 b := ![[], [132, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [111, 87, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![254563, 478993, 628556]
  a := ![-66, -64, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-570885, -85027, 628556]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-863, -5759, -2007]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-863, -5759, -2007]] 
 ![![157, 0, 0], ![48, 1, 0], ![1, 0, 1]] where
  M :=![![![-863, -5759, -2007], ![-11518, -76867, -26788], ![-28098, -187516, -65349]]]
  hmulB := by decide  
  f := ![![![-2975, 279, -23]], ![![-906, 63, 2]], ![![-21, 65, -26]]]
  g := ![![![1768, -5759, -2007], ![23598, -76867, -26788], ![57567, -187516, -65349]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![2975, -279, 23]] ![![-863, -5759, -2007]]
  ![![157, 0, 0]] where
 M := ![![![-157, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [156, 16, 110, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [111, 41, 53], [105, 121, 110], [0, 1]]
 g := ![![[109, 24, 77], [14, 15, 16], [48, 10], [5, 126], [15, 1], [22, 53, 1], []], ![[69, 52, 41, 46], [90, 112, 8, 49], [93, 10], [115, 39], [77, 151], [98, 66, 142, 93], [3, 38]], ![[3, 140, 30, 94], [3, 143, 12, 114], [119, 40], [14, 54], [121, 10], [117, 124, 30, 68], [109, 38]]]
 h' := ![![[111, 41, 53], [98, 54, 136], [93, 43, 159], [75, 106, 70], [23, 77, 17], [154, 19, 162], [0, 0, 1], [0, 1]], ![[105, 121, 110], [162, 127, 84], [160, 17, 2], [145, 19, 70], [127, 64, 107], [27, 98, 71], [117, 29, 121], [111, 41, 53]], ![[0, 1], [126, 145, 106], [162, 103, 2], [12, 38, 23], [27, 22, 39], [141, 46, 93], [52, 134, 41], [105, 121, 110]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120, 124], []]
 b := ![[], [81, 70, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [156, 16, 110, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-844503, 426897, -2135789]
  a := ![-5, -1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5181, 2619, -13103]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀

instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18147, -148, 618]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-18147, -148, 618]] 
 ![![167, 0, 0], ![0, 167, 0], ![59, 23, 1]] where
  M :=![![![-18147, -148, 618], ![-296, 3335, -1358], ![8652, -9506, 3631]]]
  hmulB := by decide  
  f := ![![![-4789, -31960, -11138]], ![![-63920, -426579, -148662]], ![![-11429, -76273, -26581]]]
  g := ![![![-327, -86, 618], ![478, 207, -1358], ![-1231, -557, 3631]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [135, 105, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 166], [0, 1]]
 g := ![![[75, 157], [77, 54], [157, 42], [94], [58], [146, 3], [1]], ![[123, 10], [85, 113], [89, 125], [94], [58], [165, 164], [1]]]
 h' := ![![[62, 166], [126, 18], [14, 80], [58, 84], [35, 42], [163, 152], [32, 62], [0, 1]], ![[0, 1], [73, 149], [131, 87], [89, 83], [134, 125], [68, 15], [35, 105], [62, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [130]]
 b := ![[], [156, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [135, 105, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![287, 327, 370]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-129, -49, 370]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4789, 31960, 11138]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![4789, 31960, 11138]] 
 ![![167, 0, 0], ![53, 1, 0], ![96, 0, 1]] where
  M :=![![![4789, 31960, 11138], ![63920, 426579, 148662], ![155932, 1040634, 362659]]]
  hmulB := by decide  
  f := ![![![18147, 148, -618]], ![![5761, 27, -188]], ![![10380, 142, -377]]]
  g := ![![![-16517, 31960, 11138], ![-220457, 426579, 148662], ![-537802, 1040634, 362659]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-18147, -148, 618]] ![![4789, 31960, 11138]]
  ![![167, 0, 0]] where
 M := ![![![-167, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, -5]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-1, 1, -5]] 
 ![![173, 0, 0], ![0, 173, 0], ![104, 69, 1]] where
  M :=![![![-1, 1, -5], ![2, -175, 10], ![-70, 70, -177]]]
  hmulB := by decide  
  f := ![![![175, -1, -5]], ![![-2, -1, 0]], ![![104, -1, -3]]]
  g := ![![![3, 2, -5], ![-6, -5, 10], ![106, 71, -177]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [133, 125, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 172], [0, 1]]
 g := ![![[105, 160], [109], [136, 148], [148, 140], [54], [79, 55], [1]], ![[0, 13], [109], [147, 25], [121, 33], [54], [124, 118], [1]]]
 h' := ![![[48, 172], [82, 92], [77, 52], [38, 54], [124, 60], [46, 153], [40, 48], [0, 1]], ![[0, 1], [0, 81], [151, 121], [35, 119], [63, 113], [124, 20], [95, 125], [48, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [100, 140]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [133, 125, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2085, 13139, 4543]
  a := ![3, 21, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2719, -1736, 4543]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![175, -1, -5]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![175, -1, -5]] 
 ![![173, 0, 0], ![2, 1, 0], ![103, 0, 1]] where
  M :=![![![175, -1, -5], ![-2, -1, 0], ![-70, 0, 1]]]
  hmulB := by decide  
  f := ![![![-1, 1, -5]], ![![0, -1, 0]], ![![-1, 1, -4]]]
  g := ![![![4, -1, -5], ![0, -1, 0], ![-1, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-1, 1, -5]] ![![175, -1, -5]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -18, -7]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-3, -18, -7]] 
 ![![179, 0, 0], ![54, 1, 0], ![15, 0, 1]] where
  M :=![![![-3, -18, -7], ![-36, -266, -83], ![-98, -581, -230]]]
  hmulB := by decide  
  f := ![![![-12957, 73, 368]], ![![-3908, 22, 111]], ![![-1057, 6, 30]]]
  g := ![![![6, -18, -7], ![87, -266, -83], ![194, -581, -230]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -17, 8]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![3, -17, 8]] 
 ![![179, 0, 0], ![126, 1, 0], ![22, 0, 1]] where
  M :=![![![3, -17, 8], ![-34, 266, -93], ![112, -651, 300]]]
  hmulB := by decide  
  f := ![![![19257, -108, -547]], ![![13554, -76, -385]], ![![2324, -13, -66]]]
  g := ![![![11, -17, 8], ![-176, 266, -93], ![422, -651, 300]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, 0]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![-1, 1, 0]] 
 ![![179, 0, 0], ![178, 1, 0], ![72, 0, 1]] where
  M :=![![![-1, 1, 0], ![2, 0, 5], ![0, 35, -2]]]
  hmulB := by decide  
  f := ![![![-175, 2, 5]], ![![-174, 2, 5]], ![![-70, 1, 2]]]
  g := ![![![-1, 1, 0], ![-2, 0, 5], ![-34, 35, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-3, -18, -7]] ![![3, -17, 8]]
  ![![-181, -180, -450]] where
 M := ![![![-181, -180, -450]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![-181, -180, -450]] ![![-1, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![-179, -15931, 0]]]
 hmul := by decide  
 g := ![![![![-1, -89, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1279, -42, 19]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-1279, -42, 19]] 
 ![![181, 0, 0], ![0, 181, 0], ![47, 74, 1]] where
  M :=![![![-1279, -42, 19], ![-84, -656, -229], ![266, -1603, -572]]]
  hmulB := by decide  
  f := ![![![45, -301, 122]], ![![-602, 4014, -1627]], ![![-225, 1500, -608]]]
  g := ![![![-12, -8, 19], ![59, 90, -229], ![150, 225, -572]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [41, 85, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [96, 180], [0, 1]]
 g := ![![[161, 55], [133], [40, 60], [4], [29, 147], [100, 166], [1]], ![[11, 126], [133], [8, 121], [4], [23, 34], [108, 15], [1]]]
 h' := ![![[96, 180], [98, 69], [170, 26], [128, 153], [78, 2], [63, 131], [140, 96], [0, 1]], ![[0, 1], [25, 112], [132, 155], [155, 28], [89, 179], [150, 50], [125, 85], [96, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [179]]
 b := ![[], [48, 180]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [41, 85, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![483, -753, 1181]
  a := ![-3, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-304, -487, 1181]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![45, -301, 122]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![45, -301, 122]] 
 ![![181, 0, 0], ![174, 1, 0], ![173, 0, 1]] where
  M :=![![![45, -301, 122], ![-602, 4014, -1627], ![1708, -11389, 4616]]]
  hmulB := by decide  
  f := ![![![-1279, -42, 19]], ![![-1230, -44, 17]], ![![-1221, -49, 15]]]
  g := ![![![173, -301, 122], ![-2307, 4014, -1627], ![6546, -11389, 4616]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-1279, -42, 19]] ![![45, -301, 122]]
  ![![181, 0, 0]] where
 M := ![![![181, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-54019, 205, 1575]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-54019, 205, 1575]] 
 ![![191, 0, 0], ![86, 1, 0], ![32, 0, 1]] where
  M :=![![![-54019, 205, 1575], ![410, 1311, -550], ![22050, -3850, 901]]]
  hmulB := by decide  
  f := ![![![-936289, -6248455, -2177575]], ![![-487004, -3250089, -1132650]], ![![-316478, -2112060, -736049]]]
  g := ![![![-639, 205, 1575], ![-496, 1311, -550], ![1698, -3850, 901]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N0 : Nat.card (O ⧸ I191N0) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N0)

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := prime_ideal_of_norm_prime hp191.out _ NI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-115, -769, -268]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-115, -769, -268]] 
 ![![191, 0, 0], ![129, 1, 0], ![8, 0, 1]] where
  M :=![![![-115, -769, -268], ![-1538, -10264, -3577], ![-3752, -25039, -8726]]]
  hmulB := by decide  
  f := ![![![839, -158, 39]], ![![565, -96, 22]], ![![38, -37, 14]]]
  g := ![![![530, -769, -268], ![7074, -10264, -3577], ![17257, -25039, -8726]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49, 327, 114]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![49, 327, 114]] 
 ![![191, 0, 0], ![167, 1, 0], ![81, 0, 1]] where
  M :=![![![49, 327, 114], ![654, 4366, 1521], ![1596, 10647, 3712]]]
  hmulB := by decide  
  f := ![![![-12505, 66, 357]], ![![-10933, 58, 312]], ![![-5277, 27, 151]]]
  g := ![![![-334, 327, 114], ![-4459, 4366, 1521], ![-10875, 10647, 3712]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-54019, 205, 1575]] ![![-115, -769, -268]]
  ![![-12505, 66, 357]] where
 M := ![![![-12505, 66, 357]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![-12505, 66, 357]] ![![49, 327, 114]]
  ![![191, 0, 0]] where
 M := ![![![191, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0]] 
 ![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [39, 131, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 37, 15], [84, 155, 178], [0, 1]]
 g := ![![[167, 107, 6], [74, 4], [84, 9], [32, 108], [163, 12], [54, 126], [1]], ![[186, 69, 30, 178], [148, 56], [89, 147], [145, 72], [53, 100], [44, 23], [189, 171, 35, 94]], ![[132, 86, 80, 120], [11, 27], [146, 147], [56, 100], [89, 93], [114, 177], [93, 121, 62, 99]]]
 h' := ![![[49, 37, 15], [178, 104, 44], [180, 18, 191], [91, 89, 190], [48, 191, 109], [187, 160, 165], [154, 62, 133], [0, 1]], ![[84, 155, 178], [110, 184, 81], [51, 43, 153], [137, 139, 98], [141, 8, 74], [49, 93, 183], [75, 9, 122], [49, 37, 15]], ![[0, 1], [181, 98, 68], [80, 132, 42], [131, 158, 98], [112, 187, 10], [130, 133, 38], [41, 122, 131], [84, 155, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 94], []]
 b := ![[], [137, 189, 161], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [39, 131, 60, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![600037, 727031, 1488030]
  a := ![4, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3109, 3767, 7710]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def PBC193 : ContainsPrimesAboveP 193 ![I193N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![193, 0, 0]]) timesTableT_eq_Table B_one_repr 193 (by decide) 𝕀



lemma PB212I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB212I3 : PrimesBelowBoundCertificateInterval O 137 193 212 where
  m := 11
  g := ![3, 2, 2, 2, 1, 2, 2, 3, 2, 3, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB212I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1, I191N2]
    · exact ![I193N0]
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
    · exact ![139, 139, 139]
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![4330747]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![179, 179, 179]
    · exact ![32761, 181]
    · exact ![191, 191, 191]
    · exact ![7189057]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
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
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I139N0, I139N1, I139N2, I149N1, I151N1, I157N1, I167N1, I173N1, I179N0, I179N1, I179N2, I181N1, I191N0, I191N1, I191N2]
  Il := ![[I139N0, I139N1, I139N2], [I149N1], [I151N1], [I157N1], [], [I167N1], [I173N1], [I179N0, I179N1, I179N2], [I181N1], [I191N0, I191N1, I191N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
