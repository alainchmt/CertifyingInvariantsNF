
import IdealArithmetic.Examples.NF3_3_866133_1.RI3_3_866133_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0]] 
 ![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [19, 75, 70, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 133, 118], [18, 5, 21], [0, 1]]
 g := ![![[129, 61, 46], [70, 138, 45], [48, 69], [53, 98, 83], [83, 71], [69, 1], []], ![[108, 66, 25, 5], [67, 117, 110, 137], [], [19, 79, 77, 36], [119, 118], [85, 25], [101, 24]], ![[125, 137, 66, 126], [52, 3, 101, 12], [134, 69], [131, 28, 40, 82], [41, 9], [99, 36], [59, 24]]]
 h' := ![![[51, 133, 118], [60, 95, 18], [105, 92, 36], [105, 92, 25], [77, 75, 19], [79, 88, 99], [0, 0, 1], [0, 1]], ![[18, 5, 21], [84, 92, 41], [20, 77, 55], [24, 74], [41, 48, 49], [83, 55, 37], [126, 114, 5], [51, 133, 118]], ![[0, 1], [73, 91, 80], [35, 109, 48], [45, 112, 114], [45, 16, 71], [44, 135, 3], [37, 25, 133], [18, 5, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 64], []]
 b := ![[], [55, 57, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [19, 75, 70, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7980685, -2189806, -737534]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-57415, -15754, -5306]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-57, 1, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-57, 1, 0]] 
 ![![149, 0, 0], ![92, 1, 0], ![68, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-57, 1, 0], ![2, -58, 4], ![349, 63, -56]]]
  hmulB := by decide  
  f := ![![![2824, -100039, 6900], ![-1639, -257025, 0]], ![![1732, -61763, 4260], ![-1042, -158685, 0]], ![![1324, -45656, 3149], ![-656, -117300, 0]]]
  g := ![![![1, 0, 0], ![-92, 149, 0], ![-68, 0, 149]], ![![-1, 1, 0], ![34, -58, 4], ![-11, 63, -56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-50, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-50, 1, 0]] 
 ![![149, 0, 0], ![99, 1, 0], ![108, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-50, 1, 0], ![2, -51, 4], ![349, 63, -49]]]
  hmulB := by decide  
  f := ![![![23783, -714731, 56064], ![-12665, -2088384, 0]], ![![15825, -474856, 37248], ![-8343, -1387488, 0]], ![![17236, -518060, 40637], ![-9188, -1513728, 0]]]
  g := ![![![1, 0, 0], ![-99, 149, 0], ![-108, 0, 149]], ![![-1, 1, 0], ![31, -51, 4], ![-4, 63, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-42, 1, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-42, 1, 0]] 
 ![![149, 0, 0], ![107, 1, 0], ![145, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-42, 1, 0], ![2, -43, 4], ![349, 63, -41]]]
  hmulB := by decide  
  f := ![![![-9197, 223013, -20748], ![4172, 772863, 0]], ![![-6607, 160112, -14896], ![2981, 554876, 0]], ![![-8947, 217026, -20191], ![4071, 752115, 0]]]
  g := ![![![1, 0, 0], ![-107, 149, 0], ![-145, 0, 149]], ![![-1, 1, 0], ![27, -43, 4], ![-3, 63, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-57, 1, 0]] ![![149, 0, 0], ![-50, 1, 0]]
  ![![149, 0, 0], ![-32, -27, 1]] where
 M := ![![![22201, 0, 0], ![-7450, 149, 0]], ![![-8493, 149, 0], ![2852, -108, 4]]]
 hmul := by decide  
 g := ![![![![149, 0, 0], ![0, 0, 0]], ![![-18, 28, -1], ![149, 0, 0]]], ![![![-25, 28, -1], ![149, 0, 0]], ![![20, 0, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-32, -27, 1]] ![![149, 0, 0], ![-42, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-6258, 149, 0]], ![![-4768, -4023, 149], ![1639, 1192, -149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-42, 1, 0]]], ![![![-32, -27, 1]], ![![11, 8, -1]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [108, 127, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 73, 127], [8, 77, 24], [0, 1]]
 g := ![![[10, 50, 55], [64, 34, 84], [140, 0, 110], [88, 81], [58, 74, 91], [136, 1], []], ![[86, 51, 20, 10], [79, 72], [24, 149, 121, 22], [97, 43], [117, 88, 19, 80], [132, 40], [87, 123]], ![[106, 67, 46, 23], [146, 100, 53, 53], [124, 71, 150, 113], [103, 50], [116, 58, 67, 24], [107, 44], [39, 123]]]
 h' := ![![[128, 73, 127], [34, 76, 120], [131, 129, 101], [53, 26, 84], [78, 64, 9], [110, 136, 98], [0, 0, 1], [0, 1]], ![[8, 77, 24], [4, 98, 17], [47, 86], [114, 46, 106], [41, 73, 63], [41, 16, 54], [42, 93, 77], [128, 73, 127]], ![[0, 1], [125, 128, 14], [32, 87, 50], [35, 79, 112], [102, 14, 79], [129, 150, 150], [80, 58, 73], [8, 77, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 64], []]
 b := ![[], [46, 36, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [108, 127, 15, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6937846, 2771454, 1381348]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![45946, 18354, 9148]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def PBC151 : ContainsPrimesAboveP 151 ![I151N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![151, 0, 0]]) timesTableT_eq_Table B_one_repr 151 (by decide) 𝕀

instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![34, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![34, 1, 0]] 
 ![![157, 0, 0], ![34, 1, 0], ![34, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![34, 1, 0], ![2, 33, 4], ![349, 63, 35]]]
  hmulB := by decide  
  f := ![![![7057, 124824, 15132], ![2355, -593931, 0]], ![![1502, 27023, 3276], ![629, -128583, 0]], ![![1496, 27031, 3277], ![659, -128622, 0]]]
  g := ![![![1, 0, 0], ![-34, 157, 0], ![-34, 0, 157]], ![![0, 1, 0], ![-8, 33, 4], ![-19, 63, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-21, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-21, 1, 0]] 
 ![![157, 0, 0], ![136, 1, 0], ![42, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-21, 1, 0], ![2, -22, 4], ![349, 63, -20]]]
  hmulB := by decide  
  f := ![![![16316, -184295, 33512], ![-3297, -1315346, 0]], ![![14137, -159636, 29028], ![-2825, -1139349, 0]], ![![4368, -49302, 8965], ![-858, -351876, 0]]]
  g := ![![![1, 0, 0], ![-136, 157, 0], ![-42, 0, 157]], ![![-1, 1, 0], ![18, -22, 4], ![-47, 63, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-13, 1, 0]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-13, 1, 0]] 
 ![![157, 0, 0], ![144, 1, 0], ![112, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-13, 1, 0], ![2, -14, 4], ![349, 63, -12]]]
  hmulB := by decide  
  f := ![![![-1461, 10414, -2976], ![314, 116808, 0]], ![![-1337, 9546, -2728], ![315, 107074, 0]], ![![-1041, 7429, -2123], ![239, 83328, 0]]]
  g := ![![![1, 0, 0], ![-144, 157, 0], ![-112, 0, 157]], ![![-1, 1, 0], ![10, -14, 4], ![-47, 63, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![34, 1, 0]] ![![157, 0, 0], ![-21, 1, 0]]
  ![![157, 0, 0], ![-21, 3, 1]] where
 M := ![![![24649, 0, 0], ![-3297, 157, 0]], ![![5338, 157, 0], ![-712, 12, 4]]]
 hmul := by decide  
 g := ![![![![157, 0, 0], ![0, 0, 0]], ![![0, -2, -1], ![157, 0, 0]]], ![![![34, 1, 0], ![0, 0, 0]], ![![-4, 0, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-21, 3, 1]] ![![157, 0, 0], ![-13, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-2041, 157, 0]], ![![-3297, 471, 157], ![628, 0, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-13, 1, 0]]], ![![![-21, 3, 1]], ![![4, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-14, 64, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-14, 64, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![149, 64, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-14, 64, 1], ![477, -15, 257], ![22542, 4135, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-149, -64, 163]], ![![-1, 0, 1], ![-232, -101, 257], ![35, -19, 113]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [23, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 162], [0, 1]]
 g := ![![[125, 145], [160, 1], [36], [33], [145], [56, 58], [1]], ![[41, 18], [56, 162], [36], [33], [145], [55, 105], [1]]]
 h' := ![![[59, 162], [69, 109], [132, 1], [54, 6], [18, 14], [16, 54], [140, 59], [0, 1]], ![[0, 1], [143, 54], [28, 162], [82, 157], [29, 149], [105, 109], [35, 104], [59, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [51, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [23, 104, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![848758, 440325, 276016]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-247102, -105673, 276016]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![69, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![69, 1, 0]] 
 ![![163, 0, 0], ![69, 1, 0], ![50, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![69, 1, 0], ![2, 68, 4], ![349, 63, 70]]]
  hmulB := by decide  
  f := ![![![2032, 90159, 5304], ![1467, -216138, 0]], ![![846, 38144, 2244], ![653, -91443, 0]], ![![614, 27656, 1627], ![472, -66300, 0]]]
  g := ![![![1, 0, 0], ![-69, 163, 0], ![-50, 0, 163]], ![![0, 1, 0], ![-30, 68, 4], ![-46, 63, 70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-14, 64, 1]] ![![163, 0, 0], ![69, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![11247, 163, 0]], ![![-2282, 10432, 163], ![-489, 4401, 326]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![69, 1, 0]]], ![![![-14, 64, 1]], ![![-3, 27, 2]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-17, -10, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-17, -10, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![150, 157, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-17, -10, 1], ![329, 56, -39], ![-3284, -527, 36]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-150, -157, 167]], ![![-1, -1, 1], ![37, 37, -39], ![-52, -37, 36]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [132, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [134, 166], [0, 1]]
 g := ![![[42, 62], [145, 38], [38, 32], [16], [93], [163, 87], [1]], ![[0, 105], [60, 129], [151, 135], [16], [93], [131, 80], [1]]]
 h' := ![![[134, 166], [65, 88], [161, 120], [134, 115], [143, 4], [27, 60], [35, 134], [0, 1]], ![[0, 1], [0, 79], [42, 47], [13, 52], [11, 163], [51, 107], [122, 33], [134, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [108, 128]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [132, 33, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2126, 5007, 4860]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4378, -4539, 4860]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![39, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![39, 1, 0]] 
 ![![167, 0, 0], ![39, 1, 0], ![131, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![39, 1, 0], ![2, 38, 4], ![349, 63, 40]]]
  hmulB := by decide  
  f := ![![![-2123, -43316, -4560], ![-668, 190380, 0]], ![![-493, -10107, -1064], ![-166, 44422, 0]], ![![-1688, -33979, -3577], ![-427, 149340, 0]]]
  g := ![![![1, 0, 0], ![-39, 167, 0], ![-131, 0, 167]], ![![0, 1, 0], ![-12, 38, 4], ![-44, 63, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-17, -10, 1]] ![![167, 0, 0], ![39, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![6513, 167, 0]], ![![-2839, -1670, 167], ![-334, -334, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![39, 1, 0]]], ![![![-17, -10, 1]], ![![-2, -2, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [65, 35, 73, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 24, 162], [37, 148, 11], [0, 1]]
 g := ![![[15, 67, 64], [70, 106], [107, 69, 9], [98, 8, 122], [80, 132], [104, 100, 1], []], ![[106, 147, 16, 104], [81, 139], [36, 139, 128, 39], [147, 28, 32, 112], [163, 16], [77, 82, 72, 45], [154, 121]], ![[143, 80, 22, 76], [62, 55], [122, 51, 37, 165], [97, 56, 3, 104], [121, 160], [151, 49, 76, 108], [132, 121]]]
 h' := ![![[63, 24, 162], [135, 39, 165], [138, 170, 25], [31, 52, 170], [159, 26, 45], [160, 67, 88], [0, 0, 1], [0, 1]], ![[37, 148, 11], [58, 90, 117], [126, 20, 100], [151, 109, 22], [5, 63, 146], [77, 15, 4], [14, 149, 148], [63, 24, 162]], ![[0, 1], [100, 44, 64], [18, 156, 48], [60, 12, 154], [136, 84, 155], [40, 91, 81], [55, 24, 24], [37, 148, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 49], []]
 b := ![[], [1, 145, 146], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [65, 35, 73, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7970802, -2181011, -730406]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-46074, -12607, -4222]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def PBC173 : ContainsPrimesAboveP 173 ![I173N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![173, 0, 0]]) timesTableT_eq_Table B_one_repr 173 (by decide) 𝕀

instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1234, -42, 23]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-1234, -42, 23]] 
 ![![179, 0, 0], ![0, 179, 0], ![102, 76, 1]] where
  M :=![![![-1234, -42, 23], ![7943, 257, -145], ![-9920, -277, 173]]]
  hmulB := by decide  
  f := ![![![24, 5, 1]], ![![359, 82, 21]], ![![177, 40, 10]]]
  g := ![![![-20, -10, 23], ![127, 63, -145], ![-154, -75, 173]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [88, 121, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 178], [0, 1]]
 g := ![![[158, 59], [171, 31], [74], [153], [26, 57], [176, 142], [1]], ![[0, 120], [0, 148], [74], [153], [110, 122], [178, 37], [1]]]
 h' := ![![[58, 178], [167, 136], [105, 63], [50, 49], [39, 137], [85, 86], [91, 58], [0, 1]], ![[0, 1], [0, 43], [0, 116], [28, 130], [109, 42], [61, 93], [54, 121], [58, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [27, 104]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [88, 121, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![354116, 184863, 123500]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-68396, -51403, 123500]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24, 5, 1]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![24, 5, 1]] 
 ![![179, 0, 0], ![53, 1, 0], ![117, 0, 1]] where
  M :=![![![24, 5, 1], ![359, 82, 21], ![1951, 418, 92]]]
  hmulB := by decide  
  f := ![![![-1234, -42, 23]], ![![-321, -11, 6]], ![![-862, -29, 16]]]
  g := ![![![-2, 5, 1], ![-36, 82, 21], ![-173, 418, 92]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-1234, -42, 23]] ![![24, 5, 1]]
  ![![179, 0, 0]] where
 M := ![![![179, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [177, 60, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 6, 152], [68, 174, 29], [0, 1]]
 g := ![![[105, 174, 166], [23, 34], [140, 0, 62], [88, 20], [80, 27, 170], [69, 126, 1], []], ![[64, 121, 60, 80], [170, 133], [8, 57, 15, 114], [173, 5], [96, 120, 102, 143], [41, 107, 135, 27], [95, 117]], ![[96, 57, 110, 111], [77, 180], [72, 35, 64, 177], [108, 45], [151, 135, 134, 135], [89, 11, 94, 139], [37, 117]]]
 h' := ![![[58, 6, 152], [19, 56, 96], [17, 166, 136], [125, 68, 65], [139, 170, 127], [95, 165, 52], [0, 0, 1], [0, 1]], ![[68, 174, 29], [148, 4, 57], [83, 43, 26], [2, 55, 107], [45, 166, 154], [4, 56, 100], [124, 170, 174], [58, 6, 152]], ![[0, 1], [27, 121, 28], [9, 153, 19], [170, 58, 9], [171, 26, 81], [86, 141, 29], [66, 11, 6], [68, 174, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 136], []]
 b := ![[], [164, 160, 142], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [177, 60, 55, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![168330, 39096, 10317]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![930, 216, 57]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-125, 82, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-125, 82, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![66, 82, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-125, 82, 1], ![513, -144, 329], ![28824, 5269, 20]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -82, 191]], ![![-1, 0, 1], ![-111, -142, 329], ![144, 19, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [81, 182, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 190], [0, 1]]
 g := ![![[106, 158], [33, 60], [11, 20], [88, 160], [91, 96], [35, 81], [1]], ![[0, 33], [0, 131], [0, 171], [0, 31], [0, 95], [0, 110], [1]]]
 h' := ![![[9, 190], [1, 106], [64, 99], [130, 28], [78, 55], [30, 124], [110, 9], [0, 1]], ![[0, 1], [0, 85], [0, 92], [0, 163], [0, 136], [0, 67], [0, 182], [9, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [147]]
 b := ![[], [99, 169]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [81, 182, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7664, 7392, 8196]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2792, -3480, 8196]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![53, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![53, 1, 0]] 
 ![![191, 0, 0], ![53, 1, 0], ![171, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![53, 1, 0], ![2, 52, 4], ![349, 63, 54]]]
  hmulB := by decide  
  f := ![![![27509, 800582, 61588], ![11842, -2940827, 0]], ![![7590, 222126, 17088], ![3439, -815952, 0]], ![![24606, 716751, 55139], ![10683, -2632887, 0]]]
  g := ![![![1, 0, 0], ![-53, 191, 0], ![-171, 0, 191]], ![![0, 1, 0], ![-18, 52, 4], ![-64, 63, 54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-125, 82, 1]] ![![191, 0, 0], ![53, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![10123, 191, 0]], ![![-23875, 15662, 191], ![-6112, 4202, 382]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![53, 1, 0]]], ![![![-125, 82, 1]], ![![-32, 22, 2]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-24, 73, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-24, 73, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![169, 73, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-24, 73, 1], ![495, -34, 293], ![25683, 4702, 112]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-169, -73, 193]], ![![-1, 0, 1], ![-254, -111, 293], ![35, -18, 112]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [179, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [113, 192], [0, 1]]
 g := ![![[77, 124], [179], [189], [185], [110], [95], [113, 1]], ![[0, 69], [179], [189], [185], [110], [95], [33, 192]]]
 h' := ![![[113, 192], [131, 33], [83, 76], [77, 31], [162, 125], [72, 66], [38, 45], [0, 1]], ![[0, 1], [0, 160], [179, 117], [106, 162], [5, 68], [3, 127], [105, 148], [113, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102]]
 b := ![[], [110, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [179, 80, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4954, 2575, 1225]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1047, -450, 1225]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![93, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![93, 1, 0]] 
 ![![193, 0, 0], ![93, 1, 0], ![81, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![93, 1, 0], ![2, 92, 4], ![349, 63, 94]]]
  hmulB := by decide  
  f := ![![![-15040, -961337, -41800], ![-12159, 2016850, 0]], ![![-7280, -463190, -20140], ![-5789, 971755, 0]], ![![-6342, -403463, -17543], ![-5041, 846450, 0]]]
  g := ![![![1, 0, 0], ![-93, 193, 0], ![-81, 0, 193]], ![![0, 1, 0], ![-46, 92, 4], ![-68, 63, 94]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-24, 73, 1]] ![![193, 0, 0], ![93, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![17949, 193, 0]], ![![-4632, 14089, 193], ![-1737, 6755, 386]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![93, 1, 0]]], ![![![-24, 73, 1]], ![![-9, 35, 2]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)


lemma PB207I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB207I3 : PrimesBelowBoundCertificateInterval O 137 193 207 where
  m := 11
  g := ![1, 3, 1, 3, 2, 2, 1, 2, 1, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB207I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1]
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
    · exact ![2685619]
    · exact ![149, 149, 149]
    · exact ![3442951]
    · exact ![157, 157, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![5177717]
    · exact ![32041, 179]
    · exact ![5929741]
    · exact ![36481, 191]
    · exact ![37249, 193]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I149N0, I149N1, I149N2, I157N0, I157N1, I157N2, I163N1, I167N1, I179N1, I191N1, I193N1]
  Il := ![[], [I149N0, I149N1, I149N2], [], [I157N0, I157N1, I157N2], [I163N1], [I167N1], [], [I179N1], [], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
