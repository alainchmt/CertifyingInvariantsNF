
import IdealArithmetic.Examples.NF3_3_574857_1.RI3_3_574857_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 20, 3]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![1, 20, 3]] 
 ![![139, 0, 0], ![0, 139, 0], ![93, 53, 1]] where
  M :=![![![1, 20, 3], ![609, 226, 20], ![4060, 2109, 226]]]
  hmulB := by decide  
  f := ![![![-64, -13, 2]], ![![406, 86, -13]], ![![93, 20, -3]]]
  g := ![![![-2, -1, 3], ![-9, -6, 20], ![-122, -71, 226]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [60, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 138], [0, 1]]
 g := ![![[66, 121], [92, 47], [54], [16, 64], [106], [37], [1]], ![[39, 18], [93, 92], [54], [112, 75], [106], [37], [1]]]
 h' := ![![[71, 138], [40, 128], [126, 66], [13, 101], [134, 8], [129, 84], [79, 71], [0, 1]], ![[0, 1], [93, 11], [86, 73], [95, 38], [7, 131], [116, 55], [116, 68], [71, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113]]
 b := ![[], [114, 126]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [60, 68, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![466, 285, 8]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, -1, 8]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![64, 13, -2]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![64, 13, -2]] 
 ![![139, 0, 0], ![86, 1, 0], ![110, 0, 1]] where
  M :=![![![64, 13, -2], ![-406, -86, 13], ![2639, 569, -86]]]
  hmulB := by decide  
  f := ![![![-1, -20, -3]], ![![-5, -14, -2]], ![![-30, -31, -4]]]
  g := ![![![-6, 13, -2], ![40, -86, 13], ![-265, 569, -86]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![1, 20, 3]] ![![64, 13, -2]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 9, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![6, 9, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![6, 9, 1]] where
  M :=![![![6, 9, 1], ![203, 81, 9], ![1827, 878, 81]]]
  hmulB := by decide  
  f := ![![![-9, 1, 0]], ![![0, -9, 1]], ![![1, 0, 0]]]
  g := ![![![0, 0, 1], ![1, 0, 9], ![9, 1, 81]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [1, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 148], [0, 1]]
 g := ![![[75, 1], [100], [144, 86], [104], [44, 45], [112], [1]], ![[0, 148], [100], [101, 63], [104], [96, 104], [112], [1]]]
 h' := ![![[74, 148], [74, 148], [5, 139], [44, 58], [105, 36], [38, 94], [148, 74], [0, 1]], ![[0, 1], [0, 1], [10, 10], [15, 91], [87, 113], [140, 55], [111, 75], [74, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [20, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [1, 75, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2509, 781, 898]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-53, -49, 898]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-9, 1, 0]] 
 ![![149, 0, 0], ![140, 1, 0], ![68, 0, 1]] where
  M :=![![![-9, 1, 0], ![0, -9, 1], ![203, 75, -9]]]
  hmulB := by decide  
  f := ![![![6, 9, 1]], ![![7, 9, 1]], ![![15, 10, 1]]]
  g := ![![![-1, 1, 0], ![8, -9, 1], ![-65, 75, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![6, 9, 1]] ![![-9, 1, 0]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![685, 323, 33]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![685, 323, 33]] 
 ![![151, 0, 0], ![10, 1, 0], ![51, 0, 1]] where
  M :=![![![685, 323, 33], ![6699, 3160, 323], ![65569, 30924, 3160]]]
  hmulB := by decide  
  f := ![![![2852, 188, -49]], ![![123, 7, -2]], ![![1216, 91, -22]]]
  g := ![![![-28, 323, 33], ![-274, 3160, 323], ![-2681, 30924, 3160]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![165, 78, 8]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![165, 78, 8]] 
 ![![151, 0, 0], ![146, 1, 0], ![126, 0, 1]] where
  M :=![![![165, 78, 8], ![1624, 765, 78], ![15834, 7474, 765]]]
  hmulB := by decide  
  f := ![![![-2253, -122, 36]], ![![-2130, -115, 34]], ![![-2044, -114, 33]]]
  g := ![![![-81, 78, 8], ![-794, 765, 78], ![-7760, 7474, 765]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![685, 323, 33]] ![![165, 78, 8]]
  ![![1160099, 547167, 55919]] where
 M := ![![![1160099, 547167, 55919]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![1160099, 547167, 55919]] ![![165, 78, 8]]
  ![![151, 0, 0]] where
 M := ![![![1965436989, 927009083, 94737853]]]
 hmul := by decide  
 g := ![![![![13016139, 6139133, 627403]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1091, -241, 36]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-1091, -241, 36]] 
 ![![157, 0, 0], ![0, 157, 0], ![70, 50, 1]] where
  M :=![![![-1091, -241, 36], ![7308, 1609, -241], ![-48923, -10767, 1609]]]
  hmulB := by decide  
  f := ![![![38, -1, -1]], ![![-203, -37, -1]], ![![-49, -14, -1]]]
  g := ![![![-23, -13, 36], ![154, 87, -241], ![-1029, -581, 1609]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [72, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [131, 156], [0, 1]]
 g := ![![[153, 58], [14], [55, 27], [19, 101], [63, 99], [48], [1]], ![[58, 99], [14], [138, 130], [62, 56], [1, 58], [48], [1]]]
 h' := ![![[131, 156], [60, 23], [122, 64], [45, 59], [17, 27], [1, 141], [85, 131], [0, 1]], ![[0, 1], [90, 134], [28, 93], [81, 98], [100, 130], [103, 16], [133, 26], [131, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123]]
 b := ![[], [93, 140]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [72, 26, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2098, -49, 178]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-66, -57, 178]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38, -1, -1]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![38, -1, -1]] 
 ![![157, 0, 0], ![107, 1, 0], ![12, 0, 1]] where
  M :=![![![38, -1, -1], ![-203, -37, -1], ![-203, -278, -37]]]
  hmulB := by decide  
  f := ![![![-1091, -241, 36]], ![![-697, -154, 23]], ![![-395, -87, 13]]]
  g := ![![![1, -1, -1], ![24, -37, -1], ![191, -278, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-1091, -241, 36]] ![![38, -1, -1]]
  ![![157, 0, 0]] where
 M := ![![![157, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [139, 135, 121, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 90, 95], [24, 72, 68], [0, 1]]
 g := ![![[123, 26, 135], [71, 84, 4], [4, 53], [150, 140], [144, 126], [162, 42, 1], []], ![[85, 29, 121, 104], [143, 162, 75, 100], [68, 150], [92, 39], [93, 38], [8, 108, 130, 57], [60, 60]], ![[129, 115, 127, 27], [146, 135, 105, 44], [74, 6], [23, 34], [3, 155], [56, 110, 92, 23], [87, 60]]]
 h' := ![![[18, 90, 95], [74, 81, 102], [106, 21, 161], [70, 38, 78], [120, 114, 125], [139, 2, 17], [0, 0, 1], [0, 1]], ![[24, 72, 68], [41, 98, 43], [53, 91, 58], [122, 68, 98], [14, 40, 107], [8, 68, 110], [134, 3, 72], [18, 90, 95]], ![[0, 1], [69, 147, 18], [9, 51, 107], [134, 57, 150], [76, 9, 94], [161, 93, 36], [56, 160, 90], [24, 72, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 35], []]
 b := ![[], [10, 119, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [139, 135, 121, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-852001, -500899, -64385]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5227, -3073, -395]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-507, -243, -25]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-507, -243, -25]] 
 ![![167, 0, 0], ![0, 167, 0], ![47, 150, 1]] where
  M :=![![![-507, -243, -25], ![-5075, -2382, -243], ![-49329, -23300, -2382]]]
  hmulB := by decide  
  f := ![![![-72, -22, 3]], ![![609, 153, -22]], ![![500, 125, -18]]]
  g := ![![![4, 21, -25], ![38, 204, -243], ![375, 2000, -2382]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [49, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [122, 166], [0, 1]]
 g := ![![[35, 75], [162, 49], [48, 38], [8], [72], [125, 21], [1]], ![[0, 92], [128, 118], [8, 129], [8], [72], [15, 146], [1]]]
 h' := ![![[122, 166], [78, 24], [153, 160], [72, 47], [56, 26], [54, 89], [118, 122], [0, 1]], ![[0, 1], [0, 143], [134, 7], [128, 120], [55, 141], [57, 78], [139, 45], [122, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [110, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [49, 45, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![455, 308, 31]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6, -26, 31]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-72, -22, 3]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-72, -22, 3]] 
 ![![167, 0, 0], ![17, 1, 0], ![45, 0, 1]] where
  M :=![![![-72, -22, 3], ![609, 153, -22], ![-4466, -1041, 153]]]
  hmulB := by decide  
  f := ![![![-507, -243, -25]], ![![-82, -39, -4]], ![![-432, -205, -21]]]
  g := ![![![1, -22, 3], ![-6, 153, -22], ![38, -1041, 153]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-507, -243, -25]] ![![-72, -22, 3]]
  ![![167, 0, 0]] where
 M := ![![![167, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB169I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 168 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 168 (by omega)

def PB169I3 : PrimesBelowBoundCertificateInterval O 137 168 169 where
  m := 6
  g := ![2, 2, 3, 2, 1, 2]
  P := ![139, 149, 151, 157, 163, 167]
  hP := PB169I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
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
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![24649, 157]
    · exact ![4330747]
    · exact ![27889, 167]
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
  β := ![I139N1, I149N1, I151N0, I151N1, I157N1, I167N1]
  Il := ![[I139N1], [I149N1], [I151N0, I151N1, I151N1], [I157N1], [], [I167N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
