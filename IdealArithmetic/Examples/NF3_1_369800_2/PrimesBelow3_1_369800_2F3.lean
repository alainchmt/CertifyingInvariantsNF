
import IdealArithmetic.Examples.NF3_1_369800_2.RI3_1_369800_2
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [41, 79, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [124, 39, 43], [5, 99, 96], [0, 1]]
 g := ![![[58, 24, 5], [111, 84, 5], [73, 24], [136, 43, 79], [82, 24], [129, 1], []], ![[108, 125, 130, 92], [113, 126, 118, 138], [5, 29], [50, 65, 2, 23], [20, 124], [51, 71], [15, 42]], ![[38, 22, 20, 24], [66, 31, 123, 99], [91, 55], [112, 59, 41, 112], [96, 120], [54, 131], [101, 42]]]
 h' := ![![[124, 39, 43], [36, 61, 12], [43, 133, 12], [123, 115, 118], [23, 122, 45], [132, 54, 21], [0, 0, 1], [0, 1]], ![[5, 99, 96], [1, 20, 58], [40, 48, 96], [55, 30, 86], [103, 47, 110], [28, 28, 92], [27, 93, 99], [124, 39, 43]], ![[0, 1], [16, 58, 69], [105, 97, 31], [120, 133, 74], [5, 109, 123], [7, 57, 26], [54, 46, 39], [5, 99, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 104], []]
 b := ![[], [105, 55, 59], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [41, 79, 10, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-902944, -283977, -48094]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6496, -2043, -346]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-77, 32, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-77, 32, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![72, 32, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-77, 32, 1], ![359, -6, 65], ![10663, 2471, 26]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-72, -32, 149]], ![![-1, 0, 1], ![-29, -14, 65], ![59, 11, 26]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [48, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 148], [0, 1]]
 g := ![![[10, 110], [132], [50, 63], [132], [56, 121], [46], [1]], ![[105, 39], [132], [57, 86], [132], [86, 28], [46], [1]]]
 h' := ![![[116, 148], [29, 109], [133, 70], [107, 19], [143, 70], [96, 11], [101, 116], [0, 1]], ![[0, 1], [8, 40], [58, 79], [76, 130], [68, 79], [31, 138], [147, 33], [116, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [138, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [48, 33, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1443, 3481, 1948]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-951, -395, 1948]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-65, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-65, 1, 0]] 
 ![![149, 0, 0], ![84, 1, 0], ![123, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-65, 1, 0], ![1, -65, 2], ![327, 71, -64]]]
  hmulB := by decide  
  f := ![![![-4199, 403944, -12430], ![4619, 926035, 0]], ![![-2332, 227677, -7006], ![2683, 521947, 0]], ![![-3458, 333457, -10261], ![3832, 764445, 0]]]
  g := ![![![1, 0, 0], ![-84, 149, 0], ![-123, 0, 149]], ![![-1, 1, 0], ![35, -65, 2], ![15, 71, -64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-77, 32, 1]] ![![149, 0, 0], ![-65, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-9685, 149, 0]], ![![-11473, 4768, 149], ![5364, -2086, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-65, 1, 0]]], ![![![-77, 32, 1]], ![![36, -14, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-82, -40, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-82, -40, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![69, 111, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-82, -40, 1], ![287, -11, -79], ![-12881, -2641, -51]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-69, -111, 151]], ![![-1, -1, 1], ![38, 58, -79], ![-62, 20, -51]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [71, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 150], [0, 1]]
 g := ![![[44, 118], [60, 38], [48, 95], [34], [32, 116], [95], [1]], ![[3, 33], [34, 113], [134, 56], [34], [48, 35], [95], [1]]]
 h' := ![![[47, 150], [119, 119], [65, 75], [51, 47], [144, 100], [108, 56], [80, 47], [0, 1]], ![[0, 1], [125, 32], [117, 76], [146, 104], [12, 51], [22, 95], [24, 104], [47, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [114, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [71, 104, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![821217, 857446, 310862]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-136611, -222836, 310862]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-72, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-72, 1, 0]] 
 ![![151, 0, 0], ![79, 1, 0], ![51, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-72, 1, 0], ![1, -72, 2], ![327, 71, -71]]]
  hmulB := by decide  
  f := ![![![-3928, 453927, -12610], ![4983, 952055, 0]], ![![-2073, 237439, -6596], ![2568, 497998, 0]], ![![-1320, 153313, -4259], ![1697, 321555, 0]]]
  g := ![![![1, 0, 0], ![-79, 151, 0], ![-51, 0, 151]], ![![-1, 1, 0], ![37, -72, 2], ![-11, 71, -71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-82, -40, 1]] ![![151, 0, 0], ![-72, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-10872, 151, 0]], ![![-12382, -6040, 151], ![6191, 2869, -151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-72, 1, 0]]], ![![![-82, -40, 1]], ![![41, 19, -1]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-5, -73, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-5, -73, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![152, 84, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-5, -73, 1], ![254, 66, -145], ![-23672, -4984, -7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-152, -84, 157]], ![![-1, -1, 1], ![142, 78, -145], ![-144, -28, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [141, 132, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 156], [0, 1]]
 g := ![![[31, 49], [111], [145, 10], [156, 127], [42, 146], [154], [1]], ![[0, 108], [111], [81, 147], [34, 30], [81, 11], [154], [1]]]
 h' := ![![[25, 156], [18, 150], [122, 116], [141, 18], [44, 21], [51, 97], [16, 25], [0, 1]], ![[0, 1], [0, 7], [39, 41], [120, 139], [98, 136], [121, 60], [13, 132], [25, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [21, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [141, 132, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1587, 4393, 1127]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1081, -575, 1127]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-12, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-12, 1, 0]] 
 ![![157, 0, 0], ![145, 1, 0], ![7, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-12, 1, 0], ![1, -12, 2], ![327, 71, -11]]]
  hmulB := by decide  
  f := ![![![-559, 6863, -1144], ![157, 89804, 0]], ![![-515, 6335, -1056], ![158, 82896, 0]], ![![-25, 306, -51], ![6, 4004, 0]]]
  g := ![![![1, 0, 0], ![-145, 157, 0], ![-7, 0, 157]], ![![-1, 1, 0], ![11, -12, 2], ![-63, 71, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-5, -73, 1]] ![![157, 0, 0], ![-12, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-1884, 157, 0]], ![![-785, -11461, 157], ![314, 942, -157]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-12, 1, 0]]], ![![![-5, -73, 1]], ![![2, 6, -1]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![22, 1, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![22, 1, 0]] 
 ![![163, 0, 0], ![22, 1, 0], ![3, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![22, 1, 0], ![1, 22, 2], ![327, 71, 23]]]
  hmulB := by decide  
  f := ![![![-7065, -160765, -14616], ![-1793, 1191204, 0]], ![![-964, -21691, -1972], ![-162, 160718, 0]], ![![-133, -2959, -269], ![-11, 21924, 0]]]
  g := ![![![1, 0, 0], ![-22, 163, 0], ![-3, 0, 163]], ![![0, 1, 0], ![-3, 22, 2], ![-8, 71, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N0)

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := prime_ideal_of_norm_prime hp163.out _ NI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![45, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![45, 1, 0]] 
 ![![163, 0, 0], ![45, 1, 0], ![129, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![45, 1, 0], ![1, 45, 2], ![327, 71, 46]]]
  hmulB := by decide  
  f := ![![![1255, 66550, 2958], ![815, -241077, 0]], ![![318, 18358, 816], ![327, -66504, 0]], ![![975, 52668, 2341], ![711, -190791, 0]]]
  g := ![![![1, 0, 0], ![-45, 163, 0], ![-129, 0, 163]], ![![0, 1, 0], ![-14, 45, 2], ![-54, 71, 46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-68, 1, 0]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-68, 1, 0]] 
 ![![163, 0, 0], ![95, 1, 0], ![52, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-68, 1, 0], ![1, -68, 2], ![327, 71, -67]]]
  hmulB := by decide  
  f := ![![![3405, -328555, 9664], ![-3423, -787616, 0]], ![![2001, -191476, 5632], ![-1955, -459008, 0]], ![![1148, -104816, 3083], ![-944, -251264, 0]]]
  g := ![![![1, 0, 0], ![-95, 163, 0], ![-52, 0, 163]], ![![-1, 1, 0], ![39, -68, 2], ![-18, 71, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![22, 1, 0]] ![![163, 0, 0], ![45, 1, 0]]
  ![![163, 0, 0], ![-75, -48, 1]] where
 M := ![![![26569, 0, 0], ![7335, 163, 0]], ![![3586, 163, 0], ![991, 67, 2]]]
 hmul := by decide  
 g := ![![![![163, 0, 0], ![0, 0, 0]], ![![45, 1, 0], ![0, 0, 0]]], ![![![22, 1, 0], ![0, 0, 0]], ![![7, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-75, -48, 1]] ![![163, 0, 0], ![-68, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-11084, 163, 0]], ![![-12225, -7824, 163], ![5379, 3260, -163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-68, 1, 0]]], ![![![-75, -48, 1]], ![![33, 20, -1]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![36, -50, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![36, -50, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![36, 117, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![36, -50, 1], ![277, 107, -99], ![-16151, -3351, 57]]]
  hmulB := by decide  
  f := ![![![-35, 50, -1], ![167, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -117, 167]], ![![0, -1, 1], ![23, 70, -99], ![-109, -60, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [21, 105, 1] where
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
 g := ![![[5, 8], [130, 116], [150, 152], [32], [152], [87, 3], [1]], ![[0, 159], [141, 51], [55, 15], [32], [152], [106, 164], [1]]]
 h' := ![![[62, 166], [109, 141], [23, 28], [44, 73], [81, 115], [10, 94], [146, 62], [0, 1]], ![[0, 1], [0, 26], [89, 139], [61, 94], [30, 52], [160, 73], [149, 105], [62, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132]]
 b := ![[], [125, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [21, 105, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2022, 977, 84]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6, -53, 84]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-68, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-68, 1, 0]] 
 ![![167, 0, 0], ![99, 1, 0], ![110, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-68, 1, 0], ![1, -68, 2], ![327, 71, -67]]]
  hmulB := by decide  
  f := ![![![-2058, 200111, -5886], ![2171, 491481, 0]], ![![-1199, 118584, -3488], ![1337, 291248, 0]], ![![-1380, 131810, -3877], ![1370, 323730, 0]]]
  g := ![![![1, 0, 0], ![-99, 167, 0], ![-110, 0, 167]], ![![-1, 1, 0], ![39, -68, 2], ![4, 71, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![36, -50, 1]] ![![167, 0, 0], ![-68, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-11356, 167, 0]], ![![6012, -8350, 167], ![-2171, 3507, -167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-68, 1, 0]]], ![![![36, -50, 1]], ![![-13, 21, -1]]]]
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


lemma PB173I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 172 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 172 (by omega)

def PB173I3 : PrimesBelowBoundCertificateInterval O 137 172 173 where
  m := 6
  g := ![1, 2, 2, 2, 3, 2]
  P := ![139, 149, 151, 157, 163, 167]
  hP := PB173I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2685619]
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![163, 163, 163]
    · exact ![27889, 167]
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
      exact NI163N1
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
  β := ![I149N1, I151N1, I157N1, I163N0, I163N1, I163N2, I167N1]
  Il := ![[], [I149N1], [I151N1], [I157N1], [I163N0, I163N1, I163N2], [I167N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
