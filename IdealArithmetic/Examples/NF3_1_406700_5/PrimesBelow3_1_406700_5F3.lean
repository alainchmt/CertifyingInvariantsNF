
import IdealArithmetic.Examples.NF3_1_406700_5.RI3_1_406700_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![17, 57, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![17, 57, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![17, 57, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![17, 57, 1], ![13, -30, 58], ![754, -2713, 28]]]
  hmulB := by decide  
  f := ![![![-16, -57, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -57, 139]], ![![0, 0, 1], ![-7, -24, 58], ![2, -31, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [32, 100, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 138], [0, 1]]
 g := ![![[90, 81], [77, 136], [46], [113, 71], [89], [131], [1]], ![[52, 58], [99, 3], [46], [102, 68], [89], [131], [1]]]
 h' := ![![[39, 138], [38, 9], [61, 54], [137, 18], [78, 40], [29, 111], [107, 39], [0, 1]], ![[0, 1], [111, 130], [82, 85], [5, 121], [109, 99], [49, 28], [99, 100], [39, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [13, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [32, 100, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![71, -228, -143]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18, 57, -143]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-58, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-58, 1, 0]] 
 ![![139, 0, 0], ![81, 1, 0], ![111, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-58, 1, 0], ![0, -58, 1], ![13, -47, -57]]]
  hmulB := by decide  
  f := ![![![1161, -20, 0], ![2780, 0, 0]], ![![755, -13, 0], ![1808, 0, 0]], ![![953, -16, 0], ![2282, 1, 0]]]
  g := ![![![1, 0, 0], ![-81, 139, 0], ![-111, 0, 139]], ![![-1, 1, 0], ![33, -58, 1], ![73, -47, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![17, 57, 1]] ![![139, 0, 0], ![-58, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-8062, 139, 0]], ![![2363, 7923, 139], ![-973, -3336, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-58, 1, 0]]], ![![![17, 57, 1]], ![![-7, -24, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![16, 65, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![16, 65, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![16, 65, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![16, 65, 1], ![13, -31, 66], ![858, -3089, 35]]]
  hmulB := by decide  
  f := ![![![-15, -65, -1], ![149, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -65, 149]], ![![0, 0, 1], ![-7, -29, 66], ![2, -36, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [72, 107, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 148], [0, 1]]
 g := ![![[136, 110], [85], [9, 17], [104], [80, 127], [125], [1]], ![[137, 39], [85], [127, 132], [104], [50, 22], [125], [1]]]
 h' := ![![[42, 148], [11, 40], [97, 54], [30, 100], [51, 113], [58, 96], [77, 42], [0, 1]], ![[0, 1], [52, 109], [130, 95], [58, 49], [29, 36], [67, 53], [53, 107], [42, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128]]
 b := ![[], [146, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [72, 107, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-73, 48, -107]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11, 47, -107]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-66, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-66, 1, 0]] 
 ![![149, 0, 0], ![83, 1, 0], ![114, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-66, 1, 0], ![0, -66, 1], ![13, -47, -65]]]
  hmulB := by decide  
  f := ![![![6469, -98, 0], ![14602, 0, 0]], ![![3631, -55, 0], ![8196, 0, 0]], ![![5046, -76, 0], ![11390, 1, 0]]]
  g := ![![![1, 0, 0], ![-83, 149, 0], ![-114, 0, 149]], ![![-1, 1, 0], ![36, -66, 1], ![76, -47, -65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![16, 65, 1]] ![![149, 0, 0], ![-66, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-9834, 149, 0]], ![![2384, 9685, 149], ![-1043, -4321, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-66, 1, 0]]], ![![![16, 65, 1]], ![![-7, -29, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [11, 62, 98, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 6, 121], [119, 144, 30], [0, 1]]
 g := ![![[6, 129, 20], [128, 136, 74], [78, 123, 139], [37, 121], [100, 119, 86], [53, 1], []], ![[139, 13, 95, 137], [145, 91, 98, 76], [46, 39, 59, 81], [140, 85], [107, 110, 7, 19], [20, 49], [77, 145]], ![[15, 53, 73, 67], [134, 112, 127, 141], [24, 56, 71, 93], [13, 136], [148, 22, 103, 56], [109, 36], [17, 145]]]
 h' := ![![[85, 6, 121], [102, 120, 110], [48, 96, 136], [83, 72, 21], [108, 29, 140], [21, 25, 29], [0, 0, 1], [0, 1]], ![[119, 144, 30], [68, 22, 9], [118, 26, 94], [13, 145, 109], [63, 123, 113], [19, 106, 104], [36, 87, 144], [85, 6, 121]], ![[0, 1], [148, 9, 32], [125, 29, 72], [105, 85, 21], [90, 150, 49], [89, 20, 18], [82, 64, 6], [119, 144, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 26], []]
 b := ![[], [127, 15, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [11, 62, 98, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![135749, -2416, 2416]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![899, -16, 16]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![100, -15, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![100, -15, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![100, 142, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![100, -15, 1], ![13, 53, -14], ![-182, 671, 39]]]
  hmulB := by decide  
  f := ![![![-99, 15, -1], ![157, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-100, -142, 157]], ![![0, -1, 1], ![9, 13, -14], ![-26, -31, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [133, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [99, 156], [0, 1]]
 g := ![![[63, 138], [93], [105, 146], [57, 9], [117, 124], [67], [1]], ![[66, 19], [93], [115, 11], [6, 148], [147, 33], [67], [1]]]
 h' := ![![[99, 156], [98, 74], [8, 67], [112, 60], [139, 154], [143, 81], [24, 99], [0, 1]], ![[0, 1], [45, 83], [47, 90], [86, 97], [156, 3], [155, 76], [91, 58], [99, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104]]
 b := ![[], [95, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [133, 58, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![231, 36, -599]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![383, 542, -599]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![14, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![14, 1, 0]] 
 ![![157, 0, 0], ![14, 1, 0], ![118, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![14, 1, 0], ![0, 14, 1], ![13, -47, 15]]]
  hmulB := by decide  
  f := ![![![1247, 89, 0], ![-13973, 0, 0]], ![![98, 7, 0], ![-1098, 0, 0]], ![![926, 66, 0], ![-10376, 1, 0]]]
  g := ![![![1, 0, 0], ![-14, 157, 0], ![-118, 0, 157]], ![![0, 1, 0], ![-2, 14, 1], ![-7, -47, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![100, -15, 1]] ![![157, 0, 0], ![14, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![2198, 157, 0]], ![![15700, -2355, 157], ![1413, -157, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![14, 1, 0]]], ![![![100, -15, 1]], ![![9, -1, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![12, 68, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![12, 68, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![12, 68, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![12, 68, 1], ![13, -35, 69], ![897, -3230, 34]]]
  hmulB := by decide  
  f := ![![![-11, -68, -1], ![163, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -68, 163]], ![![0, 0, 1], ![-5, -29, 69], ![3, -34, 34]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [155, 131, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 162], [0, 1]]
 g := ![![[4, 61], [145, 133], [1], [49], [87], [28, 46], [1]], ![[0, 102], [0, 30], [1], [49], [87], [33, 117], [1]]]
 h' := ![![[32, 162], [19, 86], [24, 40], [159, 162], [16, 7], [61, 24], [8, 32], [0, 1]], ![[0, 1], [0, 77], [0, 123], [127, 1], [77, 156], [14, 139], [54, 131], [32, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [84, 117]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [155, 131, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![194, -259, -174]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14, 71, -174]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-69, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-69, 1, 0]] 
 ![![163, 0, 0], ![94, 1, 0], ![129, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-69, 1, 0], ![0, -69, 1], ![13, -47, -68]]]
  hmulB := by decide  
  f := ![![![2899, -42, 0], ![6846, 0, 0]], ![![1726, -25, 0], ![4076, 0, 0]], ![![2307, -33, 0], ![5448, 1, 0]]]
  g := ![![![1, 0, 0], ![-94, 163, 0], ![-129, 0, 163]], ![![-1, 1, 0], ![39, -69, 1], ![81, -47, -68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![12, 68, 1]] ![![163, 0, 0], ![-69, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-11247, 163, 0]], ![![1956, 11084, 163], ![-815, -4727, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-69, 1, 0]]], ![![![12, 68, 1]], ![![-5, -29, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![35, 1, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![35, 1, 0]] 
 ![![167, 0, 0], ![35, 1, 0], ![111, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![35, 1, 0], ![0, 35, 1], ![13, -47, 36]]]
  hmulB := by decide  
  f := ![![![2696, 77, 0], ![-12859, 0, 0]], ![![560, 16, 0], ![-2671, 0, 0]], ![![1758, 50, 0], ![-8385, 1, 0]]]
  g := ![![![1, 0, 0], ![-35, 167, 0], ![-111, 0, 167]], ![![0, 1, 0], ![-8, 35, 1], ![-14, -47, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![37, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![37, 1, 0]] 
 ![![167, 0, 0], ![37, 1, 0], ![134, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![37, 1, 0], ![0, 37, 1], ![13, -47, 38]]]
  hmulB := by decide  
  f := ![![![3479, 94, 0], ![-15698, 0, 0]], ![![777, 21, 0], ![-3506, 0, 0]], ![![2784, 75, 0], ![-12562, 1, 0]]]
  g := ![![![1, 0, 0], ![-37, 167, 0], ![-134, 0, 167]], ![![0, 1, 0], ![-9, 37, 1], ![-20, -47, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-73, 1, 0]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-73, 1, 0]] 
 ![![167, 0, 0], ![94, 1, 0], ![15, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-73, 1, 0], ![0, -73, 1], ![13, -47, -72]]]
  hmulB := by decide  
  f := ![![![11900, -163, 0], ![27221, 0, 0]], ![![6644, -91, 0], ![15198, 0, 0]], ![![1200, -16, 0], ![2745, 1, 0]]]
  g := ![![![1, 0, 0], ![-94, 167, 0], ![-15, 0, 167]], ![![-1, 1, 0], ![41, -73, 1], ![33, -47, -72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![35, 1, 0]] ![![167, 0, 0], ![37, 1, 0]]
  ![![167, 0, 0], ![-41, 72, 1]] where
 M := ![![![27889, 0, 0], ![6179, 167, 0]], ![![5845, 167, 0], ![1295, 72, 1]]]
 hmul := by decide  
 g := ![![![![167, 0, 0], ![0, 0, 0]], ![![37, 1, 0], ![0, 0, 0]]], ![![![35, 1, 0], ![0, 0, 0]], ![![8, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-41, 72, 1]] ![![167, 0, 0], ![-73, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-12191, 167, 0]], ![![-6847, 12024, 167], ![3006, -5344, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-73, 1, 0]]], ![![![-41, 72, 1]], ![![18, -32, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [39, 127, 71, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [156, 9, 150], [119, 163, 23], [0, 1]]
 g := ![![[169, 29, 22], [98, 41], [55, 111, 142], [159, 116, 124], [125, 149], [70, 102, 1], []], ![[68, 64, 131, 163], [64, 51], [109, 103, 103, 158], [114, 68, 43, 43], [163, 116], [39, 11, 113, 122], [87, 10]], ![[76, 71, 62, 90], [117, 130], [23, 155, 132, 35], [152, 4, 92, 159], [107, 40], [103, 109, 46, 133], [41, 10]]]
 h' := ![![[156, 9, 150], [74, 59, 56], [104, 141, 53], [27, 171, 90], [29, 113, 41], [38, 107, 29], [0, 0, 1], [0, 1]], ![[119, 163, 23], [150, 38, 159], [140, 27, 33], [96, 135, 11], [75, 66, 105], [66, 130, 17], [10, 19, 163], [156, 9, 150]], ![[0, 1], [56, 76, 131], [11, 5, 87], [160, 40, 72], [3, 167, 27], [102, 109, 127], [106, 154, 9], [119, 163, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 26], []]
 b := ![[], [146, 163, 129], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [39, 127, 71, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![105876, -361570, -19030]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![612, -2090, -110]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-21, 41, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-21, 41, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![158, 41, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-21, 41, 1], ![13, -68, 42], ![546, -1961, -26]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-158, -41, 179]], ![![-1, 0, 1], ![-37, -10, 42], ![26, -5, -26]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [53, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [121, 178], [0, 1]]
 g := ![![[45, 65], [11, 31], [76], [75], [139, 116], [60, 142], [1]], ![[34, 114], [3, 148], [76], [75], [34, 63], [58, 37], [1]]]
 h' := ![![[121, 178], [133, 85], [155, 63], [31, 75], [151, 84], [42, 37], [126, 121], [0, 1]], ![[0, 1], [36, 94], [81, 116], [156, 104], [112, 95], [44, 142], [89, 58], [121, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87]]
 b := ![[], [98, 133]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [53, 58, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-69, 416, -99]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![87, 25, -99]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-42, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-42, 1, 0]] 
 ![![179, 0, 0], ![137, 1, 0], ![26, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-42, 1, 0], ![0, -42, 1], ![13, -47, -41]]]
  hmulB := by decide  
  f := ![![![4243, -101, 0], ![18079, 0, 0]], ![![3277, -78, 0], ![13963, 0, 0]], ![![682, -16, 0], ![2906, 1, 0]]]
  g := ![![![1, 0, 0], ![-137, 179, 0], ![-26, 0, 179]], ![![-1, 1, 0], ![32, -42, 1], ![42, -47, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-21, 41, 1]] ![![179, 0, 0], ![-42, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-7518, 179, 0]], ![![-3759, 7339, 179], ![895, -1790, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-42, 1, 0]]], ![![![-21, 41, 1]], ![![5, -10, 0]]]]
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


lemma PB181I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 180 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 180 (by omega)

def PB181I3 : PrimesBelowBoundCertificateInterval O 137 180 181 where
  m := 8
  g := ![2, 2, 1, 2, 2, 3, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179]
  hP := PB181I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![167, 167, 167]
    · exact ![5177717]
    · exact ![32041, 179]
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
      exact NI167N1
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
  β := ![I139N1, I149N1, I157N1, I163N1, I167N0, I167N1, I167N2, I179N1]
  Il := ![[I139N1], [I149N1], [], [I157N1], [I163N1], [I167N0, I167N1, I167N2], [], [I179N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
