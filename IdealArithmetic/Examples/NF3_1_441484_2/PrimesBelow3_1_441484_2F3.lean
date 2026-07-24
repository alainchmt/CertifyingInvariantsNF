
import IdealArithmetic.Examples.NF3_1_441484_2.RI3_1_441484_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![136142, -7130, 11349]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![136142, -7130, 11349]] 
 ![![139, 0, 0], ![0, 139, 0], ![64, 137, 1]] where
  M :=![![![136142, -7130, 11349], ![-1485411, 77794, -123826], ![2111415, -110579, 176011]]]
  hmulB := by decide  
  f := ![![![320, -19, -34]], ![![4329, 293, -73]], ![![4406, 283, -85]]]
  g := ![![![-4246, -11237, 11349], ![46327, 122604, -123826], ![-65851, -174274, 176011]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [65, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 138], [0, 1]]
 g := ![![[20, 77], [9, 125], [1], [43, 36], [125], [38], [1]], ![[0, 62], [0, 14], [1], [86, 103], [125], [38], [1]]]
 h' := ![![[90, 138], [110, 76], [21, 60], [124, 1], [0, 6], [87, 60], [74, 90], [0, 1]], ![[0, 1], [0, 63], [0, 79], [75, 138], [123, 133], [66, 79], [112, 49], [90, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129]]
 b := ![[], [86, 134]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [65, 49, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4288, -1673, -484]
  a := ![-3, -6, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![192, 465, -484]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-320, 19, 34]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-320, 19, 34]] 
 ![![139, 0, 0], ![26, 1, 0], ![66, 0, 1]] where
  M :=![![![-320, 19, 34], ![-4329, -293, 73], ![1119, -412, -362]]]
  hmulB := by decide  
  f := ![![![-136142, 7130, -11349]], ![![-14779, 774, -1232]], ![![-79833, 4181, -6655]]]
  g := ![![![-22, 19, 34], ![-11, -293, 73], ![257, -412, -362]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![136142, -7130, 11349]] ![![-320, 19, 34]]
  ![![139, 0, 0]] where
 M := ![![![-139, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![45, 21, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![45, 21, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![45, 21, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![45, 21, 1], ![-66, 148, 227], ![-2604, -53, -38]]]
  hmulB := by decide  
  f := ![![![-44, -21, -1], ![149, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -21, 149]], ![![0, 0, 1], ![-69, -31, 227], ![-6, 5, -38]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [111, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [134, 148], [0, 1]]
 g := ![![[129, 132], [42], [66, 110], [96], [74, 88], [76], [1]], ![[86, 17], [42], [55, 39], [96], [95, 61], [76], [1]]]
 h' := ![![[134, 148], [135, 79], [124, 108], [135, 109], [130, 120], [11, 104], [38, 134], [0, 1]], ![[0, 1], [142, 70], [143, 41], [139, 40], [118, 29], [90, 45], [114, 15], [134, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115]]
 b := ![[], [96, 132]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [111, 15, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11116, -7706, 449]
  a := ![7, 9, 26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-61, -115, 449]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![71, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![71, 1, 0]] 
 ![![149, 0, 0], ![71, 1, 0], ![38, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![71, 1, 0], ![3, 76, 11], ![-129, -2, 67]]]
  hmulB := by decide  
  f := ![![![1024, 36702, 5313], ![894, -71967, 0]], ![![477, 17477, 2530], ![448, -34270, 0]], ![![244, 9360, 1355], ![264, -18354, 0]]]
  g := ![![![1, 0, 0], ![-71, 149, 0], ![-38, 0, 149]], ![![0, 1, 0], ![-39, 76, 11], ![-17, -2, 67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![45, 21, 1]] ![![149, 0, 0], ![71, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![10579, 149, 0]], ![![6705, 3129, 149], ![3129, 1639, 298]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![71, 1, 0]]], ![![![45, 21, 1]], ![![21, 11, 2]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![12, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![12, 1, 0]] 
 ![![151, 0, 0], ![12, 1, 0], ![119, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![12, 1, 0], ![3, 17, 11], ![-129, -2, 8]]]
  hmulB := by decide  
  f := ![![![21532, 123148, 79695], ![2567, -1093995, 0]], ![![1701, 9773, 6325], ![303, -86825, 0]], ![![16964, 97050, 62806], ![2085, -862155, 0]]]
  g := ![![![1, 0, 0], ![-12, 151, 0], ![-119, 0, 151]], ![![0, 1, 0], ![-10, 17, 11], ![-7, -2, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![46, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![46, 1, 0]] 
 ![![151, 0, 0], ![46, 1, 0], ![89, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![46, 1, 0], ![3, 51, 11], ![-129, -2, 42]]]
  hmulB := by decide  
  f := ![![![-2575, -49259, -10626], ![-1057, 145866, 0]], ![![-790, -14992, -3234], ![-301, 44394, 0]], ![![-1543, -29034, -6263], ![-540, 85974, 0]]]
  g := ![![![1, 0, 0], ![-46, 151, 0], ![-89, 0, 151]], ![![0, 1, 0], ![-22, 51, 11], ![-25, -2, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20, 1, 2]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![-20, 1, 2]] 
 ![![151, 0, 0], ![92, 1, 0], ![95, 0, 1]] where
  M :=![![![-20, 1, 2], ![-255, -19, 3], ![81, -24, -22]]]
  hmulB := by decide  
  f := ![![![490, -26, 41]], ![![263, -14, 22]], ![![359, -19, 30]]]
  g := ![![![-2, 1, 2], ![8, -19, 3], ![29, -24, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![12, 1, 0]] ![![151, 0, 0], ![46, 1, 0]]
  ![![-490, 26, -41]] where
 M := ![![![22801, 0, 0], ![6946, 151, 0]], ![![1812, 151, 0], ![555, 63, 11]]]
 hmul := by decide  
 g := ![![![![3020, -151, -302]], ![![1175, -27, -95]]], ![![![495, 7, -27]], ![![174, 6, -7]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![-490, 26, -41]] ![![-20, 1, 2]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-54, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-54, 1, 0]] 
 ![![157, 0, 0], ![103, 1, 0], ![88, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-54, 1, 0], ![3, -49, 11], ![-129, -2, -58]]]
  hmulB := by decide  
  f := ![![![47566, -900235, 202125], ![-21980, -2884875, 0]], ![![31195, -590554, 132594], ![-14443, -1892478, 0]], ![![26644, -504590, 113293], ![-12370, -1617000, 0]]]
  g := ![![![1, 0, 0], ![-103, 157, 0], ![-88, 0, 157]], ![![-1, 1, 0], ![26, -49, 11], ![33, -2, -58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-52, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-52, 1, 0]] 
 ![![157, 0, 0], ![105, 1, 0], ![35, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-52, 1, 0], ![3, -47, 11], ![-129, -2, -56]]]
  hmulB := by decide  
  f := ![![![-1078, 20159, -4719], ![628, 67353, 0]], ![![-701, 13439, -3146], ![472, 44902, 0]], ![![-238, 4494, -1052], ![147, 15015, 0]]]
  g := ![![![1, 0, 0], ![-105, 157, 0], ![-35, 0, 157]], ![![-1, 1, 0], ![29, -47, 11], ![13, -2, -56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-54, 1, 0]] ![![157, 0, 0], ![-52, 1, 0]]
  ![![157, 0, 0], ![70, -52, 1]] where
 M := ![![![24649, 0, 0], ![-8164, 157, 0]], ![![-8478, 157, 0], ![2811, -101, 11]]]
 hmul := by decide  
 g := ![![![![87, 52, -1], ![157, 0, 0]], ![![-52, 1, 0], ![0, 0, 0]]], ![![![-54, 1, 0], ![0, 0, 0]], ![![13, 3, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![70, -52, 1]] ![![157, 0, 0], ![-52, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-8164, 157, 0]], ![![10990, -8164, 157], ![-3925, 2512, -628]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-52, 1, 0]]], ![![![70, -52, 1]], ![![-25, 16, -4]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [158, 9, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 54, 118], [55, 108, 45], [0, 1]]
 g := ![![[48, 24, 49], [28, 35, 115], [143, 34], [48, 134], [146, 156], [137, 132, 1], []], ![[17, 162, 64, 135], [8, 106, 135, 134], [95, 56], [23, 46], [113, 150], [47, 146, 150, 143], [10, 69]], ![[155, 83, 142, 80], [19, 22, 69, 109], [16, 24], [61, 100], [136, 33], [66, 36, 99, 5], [83, 69]]]
 h' := ![![[77, 54, 118], [140, 111, 156], [158, 54, 142], [101, 76, 69], [26, 116, 42], [33, 79, 112], [0, 0, 1], [0, 1]], ![[55, 108, 45], [86, 113, 117], [29, 106, 29], [83, 64, 120], [91, 148, 131], [129, 73, 65], [111, 95, 108], [77, 54, 118]], ![[0, 1], [95, 102, 53], [0, 3, 155], [75, 23, 137], [111, 62, 153], [88, 11, 149], [17, 68, 54], [55, 108, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 157], []]
 b := ![[], [89, 130, 152], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [158, 9, 31, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-140487064127, 4015184053, 6381437938]
  a := ![-131, -260, -459]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-861883829, 24633031, 39149926]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [59, 92, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 136, 108], [58, 30, 59], [0, 1]]
 g := ![![[69, 32, 11], [124, 18, 84], [115, 71, 147], [145, 85], [97, 115], [100, 162, 1], []], ![[40, 153, 84, 84], [0, 84, 82, 25], [24, 75, 155, 32], [74, 38], [17, 63], [82, 122, 44, 6], [114, 141]], ![[163, 31, 98, 17], [85, 140, 71, 53], [149, 34, 147, 46], [122, 150], [66, 162], [3, 119, 117, 86], [163, 141]]]
 h' := ![![[104, 136, 108], [32, 58, 126], [62, 159, 77], [137, 156, 100], [141, 84, 69], [112, 113, 68], [0, 0, 1], [0, 1]], ![[58, 30, 59], [30, 94, 24], [33, 161, 110], [12, 48, 142], [6, 118, 120], [72, 92, 49], [82, 129, 30], [104, 136, 108]], ![[0, 1], [84, 15, 17], [79, 14, 147], [115, 130, 92], [74, 132, 145], [131, 129, 50], [93, 38, 136], [58, 30, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97, 126], []]
 b := ![[], [6, 79, 138], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [59, 92, 5, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26142347, -25050, -65130]
  a := ![-7, -10, -26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-156541, -150, -390]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![72, -59, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![72, -59, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![72, 114, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![72, -59, 1], ![-306, -225, -653], ![7716, 107, 309]]]
  hmulB := by decide  
  f := ![![![-71, 59, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-72, -114, 173]], ![![0, -1, 1], ![270, 429, -653], ![-84, -203, 309]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [111, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [172, 172], [0, 1]]
 g := ![![[53, 135], [64], [44, 149], [66, 24], [109], [48, 1], [1]], ![[91, 38], [64], [68, 24], [42, 149], [109], [47, 172], [1]]]
 h' := ![![[172, 172], [32, 57], [133, 165], [113, 144], [25, 71], [35, 52], [62, 172], [0, 1]], ![[0, 1], [148, 116], [141, 8], [142, 29], [127, 102], [156, 121], [63, 1], [172, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [66, 132]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [111, 1, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4098, -1385, 44]
  a := ![-3, -6, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-42, -37, 44]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-39, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-39, 1, 0]] 
 ![![173, 0, 0], ![134, 1, 0], ![37, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-39, 1, 0], ![3, -34, 11], ![-129, -2, -43]]]
  hmulB := by decide  
  f := ![![![8329, -100558, 32538], ![-2422, -511734, 0]], ![![6445, -77883, 25201], ![-1902, -396343, 0]], ![![1796, -21507, 6959], ![-453, -109446, 0]]]
  g := ![![![1, 0, 0], ![-134, 173, 0], ![-37, 0, 173]], ![![-1, 1, 0], ![24, -34, 11], ![10, -2, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![72, -59, 1]] ![![173, 0, 0], ![-39, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-6747, 173, 0]], ![![12456, -10207, 173], ![-3114, 2076, -692]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-39, 1, 0]]], ![![![72, -59, 1]], ![![-18, 12, -4]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![74, -51, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![74, -51, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![74, 128, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![74, -51, 1], ![-282, -183, -565], ![6684, 91, 279]]]
  hmulB := by decide  
  f := ![![![-73, 51, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-74, -128, 179]], ![![0, -1, 1], ![232, 403, -565], ![-78, -199, 279]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [104, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [78, 178], [0, 1]]
 g := ![![[44, 93], [114, 142], [20], [89], [149, 144], [88, 177], [1]], ![[138, 86], [92, 37], [20], [89], [104, 35], [111, 2], [1]]]
 h' := ![![[78, 178], [137, 56], [174, 58], [74, 60], [77, 39], [156, 167], [75, 78], [0, 1]], ![[0, 1], [30, 123], [44, 121], [100, 119], [76, 140], [115, 12], [73, 101], [78, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [124, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [104, 101, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-93026, 1448, 6914]
  a := ![5, 28, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3378, -4936, 6914]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![28, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![28, 1, 0]] 
 ![![179, 0, 0], ![28, 1, 0], ![79, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![28, 1, 0], ![3, 33, 11], ![-129, -2, 24]]]
  hmulB := by decide  
  f := ![![![-5015, -57018, -19008], ![-1074, 309312, 0]], ![![-810, -8910, -2970], ![1, 48330, 0]], ![![-2231, -25165, -8389], ![-361, 136512, 0]]]
  g := ![![![1, 0, 0], ![-28, 179, 0], ![-79, 0, 179]], ![![0, 1, 0], ![-10, 33, 11], ![-11, -2, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![74, -51, 1]] ![![179, 0, 0], ![28, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![5012, 179, 0]], ![![13246, -9129, 179], ![1790, -1611, -537]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![28, 1, 0]]], ![![![74, -51, 1]], ![![10, -9, -3]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![76, 1, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![76, 1, 0]] 
 ![![181, 0, 0], ![76, 1, 0], ![33, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![76, 1, 0], ![3, 81, 11], ![-129, -2, 72]]]
  hmulB := by decide  
  f := ![![![32830, 1114044, 151305], ![20091, -2489655, 0]], ![![13753, 467728, 63525], ![8508, -1045275, 0]], ![![5986, 203113, 27586], ![3662, -453915, 0]]]
  g := ![![![1, 0, 0], ![-76, 181, 0], ![-33, 0, 181]], ![![0, 1, 0], ![-36, 81, 11], ![-13, -2, 72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-51, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-51, 1, 0]] 
 ![![181, 0, 0], ![130, 1, 0], ![149, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-51, 1, 0], ![3, -46, 11], ![-129, -2, -55]]]
  hmulB := by decide  
  f := ![![![50188, -849977, 203280], ![-18643, -3344880, 0]], ![![36043, -610438, 145992], ![-13393, -2402232, 0]], ![![41324, -699705, 167341], ![-15315, -2753520, 0]]]
  g := ![![![1, 0, 0], ![-130, 181, 0], ![-149, 0, 181]], ![![-1, 1, 0], ![24, -46, 11], ![46, -2, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-26, 1, 0]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-26, 1, 0]] 
 ![![181, 0, 0], ![155, 1, 0], ![0, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-26, 1, 0], ![3, -21, 11], ![-129, -2, -30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![21, 3, -2], ![150, 33, 0]]]
  g := ![![![1, 0, 0], ![-155, 181, 0], ![0, 0, 181]], ![![-1, 1, 0], ![18, -21, 11], ![1, -2, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![76, 1, 0]] ![![181, 0, 0], ![-51, 1, 0]]
  ![![181, 0, 0], ![-23, 85, 1]] where
 M := ![![![32761, 0, 0], ![-9231, 181, 0]], ![![13756, 181, 0], ![-3873, 30, 11]]]
 hmul := by decide  
 g := ![![![![181, 0, 0], ![0, 0, 0]], ![![-28, -84, -1], ![181, 0, 0]]], ![![![76, 1, 0], ![0, 0, 0]], ![![-20, -5, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-23, 85, 1]] ![![181, 0, 0], ![-26, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-4706, 181, 0]], ![![-4163, 15385, 181], ![724, -1810, 905]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-26, 1, 0]]], ![![![-23, 85, 1]], ![![4, -10, 5]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)


lemma PB189I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 188 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 188 (by omega)

def PB189I3 : PrimesBelowBoundCertificateInterval O 137 188 189 where
  m := 9
  g := ![2, 2, 3, 3, 1, 1, 2, 2, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181]
  hP := PB189I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1, I157N1]
    · exact ![I163N0]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N2]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![157, 157, 157]
    · exact ![4330747]
    · exact ![4657463]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![181, 181, 181]
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
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
  β := ![I139N1, I149N1, I151N0, I151N1, I151N2, I157N0, I157N1, I173N1, I179N1, I181N0, I181N1, I181N2]
  Il := ![[I139N1], [I149N1], [I151N0, I151N1, I151N2], [I157N0, I157N1, I157N1], [], [], [I173N1], [I179N1], [I181N0, I181N1, I181N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
