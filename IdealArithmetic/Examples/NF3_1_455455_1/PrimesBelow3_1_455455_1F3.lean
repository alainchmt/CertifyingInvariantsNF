
import IdealArithmetic.Examples.NF3_1_455455_1.RI3_1_455455_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-27, 42, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-27, 42, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![112, 42, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-27, 42, 1], ![-132, 20, 252], ![-5522, 188, -22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-112, -42, 139]], ![![-1, 0, 1], ![-204, -76, 252], ![-22, 8, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [132, 128, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 138], [0, 1]]
 g := ![![[81, 36], [31, 4], [29], [5, 36], [129], [121], [1]], ![[60, 103], [75, 135], [29], [123, 103], [129], [121], [1]]]
 h' := ![![[11, 138], [78, 6], [38, 137], [35, 53], [21, 133], [62, 95], [7, 11], [0, 1]], ![[0, 1], [5, 133], [16, 2], [62, 86], [94, 6], [134, 44], [128, 128], [11, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [15, 111]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [132, 128, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3014, -2694, -779]
  a := ![0, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![606, 216, -779]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![26, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![26, 1, 0]] 
 ![![139, 0, 0], ![26, 1, 0], ![22, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![26, 1, 0], ![0, 27, 6], ![-132, 5, 26]]]
  hmulB := by decide  
  f := ![![![2263, 87, 0], ![-12093, 0, 0]], ![![390, 15, 0], ![-2084, 0, 0]], ![![326, -10, -5], ![-1742, 116, 0]]]
  g := ![![![1, 0, 0], ![-26, 139, 0], ![-22, 0, 139]], ![![0, 1, 0], ![-6, 27, 6], ![-6, 5, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-27, 42, 1]] ![![139, 0, 0], ![26, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![3614, 139, 0]], ![![-3753, 5838, 139], ![-834, 1112, 278]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![26, 1, 0]]], ![![![-27, 42, 1]], ![![-6, 8, 2]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-23, -12, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-23, -12, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![126, 137, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-23, -12, 1], ![-132, -30, -72], ![1606, -82, -18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-126, -137, 149]], ![![-1, -1, 1], ![60, 66, -72], ![26, 16, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [27, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [146, 148], [0, 1]]
 g := ![![[116, 1], [16], [63, 113], [118], [108, 47], [9], [1]], ![[113, 148], [16], [22, 36], [118], [116, 102], [9], [1]]]
 h' := ![![[146, 148], [134, 1], [87, 145], [16, 115], [64, 77], [39, 135], [122, 146], [0, 1]], ![[0, 1], [131, 148], [99, 4], [118, 34], [131, 72], [81, 14], [131, 3], [146, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [137]]
 b := ![[], [140, 143]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [27, 3, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-679, -1326, 334]
  a := ![-1, 1, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-287, -316, 334]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![72, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![72, 1, 0]] 
 ![![149, 0, 0], ![72, 1, 0], ![18, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![72, 1, 0], ![0, 73, 6], ![-132, 5, 72]]]
  hmulB := by decide  
  f := ![![![4681, 65, 0], ![-9685, 0, 0]], ![![2232, 31, 0], ![-4618, 0, 0]], ![![522, -5, -1], ![-1080, 25, 0]]]
  g := ![![![1, 0, 0], ![-72, 149, 0], ![-18, 0, 149]], ![![0, 1, 0], ![-36, 73, 6], ![-12, 5, 72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-23, -12, 1]] ![![149, 0, 0], ![72, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![10728, 149, 0]], ![![-3427, -1788, 149], ![-1788, -894, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![72, 1, 0]]], ![![![-23, -12, 1]], ![![-12, -6, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![53, -46, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![53, -46, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![53, 105, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![53, -46, 1], ![-132, 12, -276], ![6094, -252, 58]]]
  hmulB := by decide  
  f := ![![![-52, 46, -1], ![151, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-53, -105, 151]], ![![0, -1, 1], ![96, 192, -276], ![20, -42, 58]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [36, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 150], [0, 1]]
 g := ![![[19, 21], [22, 72], [110, 58], [90], [52, 43], [58], [1]], ![[0, 130], [0, 79], [0, 93], [90], [85, 108], [58], [1]]]
 h' := ![![[71, 150], [114, 126], [117, 26], [58, 80], [91, 40], [114, 63], [115, 71], [0, 1]], ![[0, 1], [0, 25], [0, 125], [0, 71], [62, 111], [57, 88], [22, 80], [71, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [137]]
 b := ![[], [22, 144]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [36, 80, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-966, -22, 53]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-25, -37, 53]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-26, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-26, 1, 0]] 
 ![![151, 0, 0], ![125, 1, 0], ![93, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-26, 1, 0], ![0, -25, 6], ![-132, 5, -26]]]
  hmulB := by decide  
  f := ![![![3433, -132, 0], ![19932, 0, 0]], ![![2835, -109, 0], ![16460, 0, 0]], ![![2103, -60, -5], ![12210, 126, 0]]]
  g := ![![![1, 0, 0], ![-125, 151, 0], ![-93, 0, 151]], ![![-1, 1, 0], ![17, -25, 6], ![11, 5, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![53, -46, 1]] ![![151, 0, 0], ![-26, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-3926, 151, 0]], ![![8003, -6946, 151], ![-1510, 1208, -302]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-26, 1, 0]]], ![![![53, -46, 1]], ![![-10, 8, -2]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-43, -36, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-43, -36, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![114, 121, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-43, -36, 1], ![-132, -74, -216], ![4774, -202, -38]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-114, -121, 157]], ![![-1, -1, 1], ![156, 166, -216], ![58, 28, -38]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [50, 114, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 156], [0, 1]]
 g := ![![[153, 30], [108], [112, 146], [68, 147], [148, 16], [122], [1]], ![[30, 127], [108], [110, 11], [109, 10], [51, 141], [122], [1]]]
 h' := ![![[43, 156], [130, 117], [52, 118], [54, 97], [136, 33], [11, 4], [107, 43], [0, 1]], ![[0, 1], [137, 40], [102, 39], [143, 60], [142, 124], [26, 153], [72, 114], [43, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [149]]
 b := ![[], [86, 153]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [50, 114, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2981, -3686, -639]
  a := ![1, -2, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![445, 469, -639]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![59, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![59, 1, 0]] 
 ![![157, 0, 0], ![59, 1, 0], ![38, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![59, 1, 0], ![0, 60, 6], ![-132, 5, 59]]]
  hmulB := by decide  
  f := ![![![119, 2, 0], ![-314, 0, 0]], ![![59, 1, 0], ![-156, 0, 0]], ![![4, -50, -5], ![-10, 131, 0]]]
  g := ![![![1, 0, 0], ![-59, 157, 0], ![-38, 0, 157]], ![![0, 1, 0], ![-24, 60, 6], ![-17, 5, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-43, -36, 1]] ![![157, 0, 0], ![59, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![9263, 157, 0]], ![![-6751, -5652, 157], ![-2669, -2198, -157]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![59, 1, 0]]], ![![![-43, -36, 1]], ![![-17, -14, -1]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-81, -44, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-81, -44, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![82, 119, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-81, -44, 1], ![-132, -120, -264], ![5830, -242, -76]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-82, -119, 163]], ![![-1, -1, 1], ![132, 192, -264], ![74, 54, -76]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [151, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [154, 162], [0, 1]]
 g := ![![[40, 95], [35, 22], [132], [113], [16], [33, 81], [1]], ![[0, 68], [0, 141], [132], [113], [16], [119, 82], [1]]]
 h' := ![![[154, 162], [94, 101], [106, 48], [106, 135], [39, 90], [70, 4], [12, 154], [0, 1]], ![[0, 1], [0, 62], [0, 115], [32, 28], [44, 73], [34, 159], [93, 9], [154, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [53, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [151, 9, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2995, -2456, 530]
  a := ![0, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-285, -402, 530]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-62, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-62, 1, 0]] 
 ![![163, 0, 0], ![101, 1, 0], ![76, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-62, 1, 0], ![0, -61, 6], ![-132, 5, -62]]]
  hmulB := by decide  
  f := ![![![7999, -129, 0], ![21027, 0, 0]], ![![4961, -80, 0], ![13041, 0, 0]], ![![3776, -10, -5], ![9926, 136, 0]]]
  g := ![![![1, 0, 0], ![-101, 163, 0], ![-76, 0, 163]], ![![-1, 1, 0], ![35, -61, 6], ![25, 5, -62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-81, -44, 1]] ![![163, 0, 0], ![-62, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-10106, 163, 0]], ![![-13203, -7172, 163], ![4890, 2608, -326]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-62, 1, 0]]], ![![![-81, -44, 1]], ![![30, 16, -2]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [97, 28, 136, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 59, 72], [28, 107, 95], [0, 1]]
 g := ![![[74, 25, 58], [113, 141, 12], [153, 83, 87], [122, 44], [76, 85], [98, 31, 1], []], ![[135, 100, 2, 9], [53, 113, 116, 107], [81, 143, 165, 107], [67, 25], [73, 99], [22, 5, 43, 16], [29, 7]], ![[25, 8, 135, 163], [24, 63, 100, 118], [10, 104, 114, 83], [35, 54], [120, 124], [131, 97, 136, 35], [6, 7]]]
 h' := ![![[3, 59, 72], [61, 9, 152], [22, 59, 124], [6, 11, 33], [145, 87, 85], [13, 94, 69], [0, 0, 1], [0, 1]], ![[28, 107, 95], [64, 51, 45], [30, 101, 148], [25, 35, 148], [41, 4, 162], [38, 72, 123], [35, 32, 107], [3, 59, 72]], ![[0, 1], [122, 107, 137], [2, 7, 62], [133, 121, 153], [45, 76, 87], [50, 1, 142], [35, 135, 59], [28, 107, 95]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [144, 22], []]
 b := ![[], [76, 38, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [97, 28, 136, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2652100614, -254834318, -21229875]
  a := ![1, 20, 101]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15880842, -1525954, -127125]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![65, 1, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![65, 1, 0]] 
 ![![173, 0, 0], ![65, 1, 0], ![150, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![65, 1, 0], ![0, 66, 6], ![-132, 5, 65]]]
  hmulB := by decide  
  f := ![![![261, 4, 0], ![-692, 0, 0]], ![![65, 1, 0], ![-172, 0, 0]], ![![200, -8, -1], ![-530, 29, 0]]]
  g := ![![![1, 0, 0], ![-65, 173, 0], ![-150, 0, 173]], ![![0, 1, 0], ![-30, 66, 6], ![-59, 5, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N0 : Nat.card (O ⧸ I173N0) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N0)

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := prime_ideal_of_norm_prime hp173.out _ NI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-50, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-50, 1, 0]] 
 ![![173, 0, 0], ![123, 1, 0], ![53, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-50, 1, 0], ![0, -49, 6], ![-132, 5, -50]]]
  hmulB := by decide  
  f := ![![![4451, -89, 0], ![15397, 0, 0]], ![![3201, -64, 0], ![11073, 0, 0]], ![![1411, -20, -1], ![4881, 29, 0]]]
  g := ![![![1, 0, 0], ![-123, 173, 0], ![-53, 0, 173]], ![![-1, 1, 0], ![33, -49, 6], ![11, 5, -50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-16, 1, 0]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-16, 1, 0]] 
 ![![173, 0, 0], ![157, 1, 0], ![133, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-16, 1, 0], ![0, -15, 6], ![-132, 5, -16]]]
  hmulB := by decide  
  f := ![![![2065, -129, 0], ![22317, 0, 0]], ![![1857, -116, 0], ![20069, 0, 0]], ![![1577, -96, -1], ![17043, 29, 0]]]
  g := ![![![1, 0, 0], ![-157, 173, 0], ![-133, 0, 173]], ![![-1, 1, 0], ![9, -15, 6], ![7, 5, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![65, 1, 0]] ![![173, 0, 0], ![-50, 1, 0]]
  ![![173, 0, 0], ![35, -55, 1]] where
 M := ![![![29929, 0, 0], ![-8650, 173, 0]], ![![11245, 173, 0], ![-3250, 16, 6]]]
 hmul := by decide  
 g := ![![![![138, 55, -1], ![173, 0, 0]], ![![-50, 1, 0], ![0, 0, 0]]], ![![![30, 56, -1], ![173, 0, 0]], ![![-20, 2, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![35, -55, 1]] ![![173, 0, 0], ![-16, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-2768, 173, 0]], ![![6055, -9515, 173], ![-692, 865, -346]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-16, 1, 0]]], ![![![35, -55, 1]], ![![-4, 5, -2]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![24, 1, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![24, 1, 0]] 
 ![![179, 0, 0], ![24, 1, 0], ![79, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![24, 1, 0], ![0, 25, 6], ![-132, 5, 24]]]
  hmulB := by decide  
  f := ![![![2137, 89, 0], ![-15931, 0, 0]], ![![264, 11, 0], ![-1968, 0, 0]], ![![941, 35, -1], ![-7015, 30, 0]]]
  g := ![![![1, 0, 0], ![-24, 179, 0], ![-79, 0, 179]], ![![0, 1, 0], ![-6, 25, 6], ![-12, 5, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![37, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![37, 1, 0]] 
 ![![179, 0, 0], ![37, 1, 0], ![64, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![37, 1, 0], ![0, 38, 6], ![-132, 5, 37]]]
  hmulB := by decide  
  f := ![![![5107, 138, 0], ![-24702, 0, 0]], ![![999, 27, 0], ![-4832, 0, 0]], ![![1790, 42, -1], ![-8658, 30, 0]]]
  g := ![![![1, 0, 0], ![-37, 179, 0], ![-64, 0, 179]], ![![0, 1, 0], ![-10, 38, 6], ![-15, 5, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-62, 1, 0]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-62, 1, 0]] 
 ![![179, 0, 0], ![117, 1, 0], ![26, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-62, 1, 0], ![0, -61, 6], ![-132, 5, -62]]]
  hmulB := by decide  
  f := ![![![6077, -98, 0], ![17542, 0, 0]], ![![3907, -63, 0], ![11278, 0, 0]], ![![882, -4, -1], ![2546, 30, 0]]]
  g := ![![![1, 0, 0], ![-117, 179, 0], ![-26, 0, 179]], ![![-1, 1, 0], ![39, -61, 6], ![5, 5, -62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![24, 1, 0]] ![![179, 0, 0], ![37, 1, 0]]
  ![![179, 0, 0], ![-31, 70, 1]] where
 M := ![![![32041, 0, 0], ![6623, 179, 0]], ![![4296, 179, 0], ![888, 62, 6]]]
 hmul := by decide  
 g := ![![![![179, 0, 0], ![0, 0, 0]], ![![37, 1, 0], ![0, 0, 0]]], ![![![24, 1, 0], ![0, 0, 0]], ![![6, -2, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-31, 70, 1]] ![![179, 0, 0], ![-62, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-11098, 179, 0]], ![![-5549, 12530, 179], ![1790, -4296, 358]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-62, 1, 0]]], ![![![-31, 70, 1]], ![![10, -24, 2]]]]
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [62, 101, 92, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 82, 53], [34, 98, 128], [0, 1]]
 g := ![![[148, 131, 60], [36, 156], [63, 147, 139], [44, 33], [33, 73, 70], [37, 89, 1], []], ![[55, 23, 27, 41], [157, 152], [38, 119, 51, 155], [139, 81], [164, 65, 31, 19], [38, 7, 97, 40], [44, 94]], ![[129, 41, 62, 162], [94, 125], [75, 33, 16, 53], [7, 44], [146, 65, 45, 90], [56, 51, 56, 17], [150, 94]]]
 h' := ![![[55, 82, 53], [105, 51, 153], [76, 151, 86], [116, 146, 35], [126, 147, 157], [59, 157, 34], [0, 0, 1], [0, 1]], ![[34, 98, 128], [24, 142, 140], [76, 97, 141], [79, 8, 127], [178, 110, 9], [149, 171, 69], [116, 15, 98], [55, 82, 53]], ![[0, 1], [1, 169, 69], [47, 114, 135], [47, 27, 19], [32, 105, 15], [1, 34, 78], [1, 166, 82], [34, 98, 128]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [170, 36], []]
 b := ![[], [19, 1, 153], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [62, 101, 92, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1605832, -304080, 10860]
  a := ![-1, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8872, -1680, 60]
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



lemma PB191I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 190 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 190 (by omega)

def PB191I3 : PrimesBelowBoundCertificateInterval O 137 190 191 where
  m := 9
  g := ![2, 2, 2, 2, 2, 1, 3, 3, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181]
  hP := PB191I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1, I173N2]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0]
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
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![173, 173, 173]
    · exact ![179, 179, 179]
    · exact ![5929741]
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
      exact NI173N2
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
      exact NI179N2
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
  β := ![I139N1, I149N1, I151N1, I157N1, I163N1, I173N0, I173N1, I173N2, I179N0, I179N1, I179N2]
  Il := ![[I139N1], [I149N1], [I151N1], [I157N1], [I163N1], [], [I173N0, I173N1, I173N2], [I179N0, I179N1, I179N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
