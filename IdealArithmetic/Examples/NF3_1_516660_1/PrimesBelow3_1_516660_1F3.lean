
import IdealArithmetic.Examples.NF3_1_516660_1.RI3_1_516660_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-85, -38, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-85, -38, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![54, 101, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-85, -38, 1], ![198, -93, -228], ![-7557, -1107, -55]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-54, -101, 139]], ![![-1, -1, 1], ![90, 165, -228], ![-33, 32, -55]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [77, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 138], [0, 1]]
 g := ![![[100, 65], [6, 129], [122], [25, 118], [1], [106], [1]], ![[0, 74], [0, 10], [122], [68, 21], [1], [106], [1]]]
 h' := ![![[84, 138], [94, 75], [82, 95], [21, 119], [4, 102], [130, 138], [62, 84], [0, 1]], ![[0, 1], [0, 64], [0, 44], [9, 20], [93, 37], [46, 1], [29, 55], [84, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [117]]
 b := ![[], [45, 128]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [77, 55, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4796, 5207, 3049]
  a := ![0, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1150, -2178, 3049]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-50, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-50, 1, 0]] 
 ![![139, 0, 0], ![89, 1, 0], ![55, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-50, 1, 0], ![0, -49, 6], ![198, 30, -50]]]
  hmulB := by decide  
  f := ![![![6401, -128, 0], ![17792, 0, 0]], ![![4151, -83, 0], ![11538, 0, 0]], ![![2545, -10, -5], ![7074, 116, 0]]]
  g := ![![![1, 0, 0], ![-89, 139, 0], ![-55, 0, 139]], ![![-1, 1, 0], ![29, -49, 6], ![2, 30, -50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-85, -38, 1]] ![![139, 0, 0], ![-50, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-6950, 139, 0]], ![![-11815, -5282, 139], ![4448, 1807, -278]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-50, 1, 0]]], ![![![-85, -38, 1]], ![![32, 13, -2]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-94, -59, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-94, -59, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![55, 90, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-94, -59, 1], ![198, -123, -354], ![-11715, -1737, -64]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-55, -90, 149]], ![![-1, -1, 1], ![132, 213, -354], ![-55, 27, -64]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [15, 145, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 148], [0, 1]]
 g := ![![[109, 37], [82], [47, 22], [68], [69, 7], [16], [1]], ![[108, 112], [82], [135, 127], [68], [97, 142], [16], [1]]]
 h' := ![![[4, 148], [72, 127], [40, 126], [87, 52], [8, 98], [134, 93], [134, 4], [0, 1]], ![[0, 1], [133, 22], [97, 23], [146, 97], [102, 51], [59, 56], [1, 145], [4, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122]]
 b := ![[], [27, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [15, 145, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![927, 2736, 3070]
  a := ![-1, 1, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1127, -1836, 3070]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![56, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![56, 1, 0]] 
 ![![149, 0, 0], ![56, 1, 0], ![64, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![56, 1, 0], ![0, 57, 6], ![198, 30, 56]]]
  hmulB := by decide  
  f := ![![![337, 6, 0], ![-894, 0, 0]], ![![56, 1, 0], ![-148, 0, 0]], ![![144, -7, -1], ![-382, 25, 0]]]
  g := ![![![1, 0, 0], ![-56, 149, 0], ![-64, 0, 149]], ![![0, 1, 0], ![-24, 57, 6], ![-34, 30, 56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-94, -59, 1]] ![![149, 0, 0], ![56, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![8344, 149, 0]], ![![-14006, -8791, 149], ![-5066, -3427, -298]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![56, 1, 0]]], ![![![-94, -59, 1]], ![![-34, -23, -2]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [132, 63, 101, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 44, 125], [124, 106, 26], [0, 1]]
 g := ![![[12, 118, 55], [107, 95, 10], [14, 115, 34], [4, 64], [69, 23, 139], [50, 1], []], ![[9, 42, 129, 125], [123, 119, 133, 64], [23, 115, 62, 47], [100, 40], [92, 74, 50, 100], [99, 62], [104, 72]], ![[150, 63, 81, 48], [62, 0, 32, 67], [73, 105, 56, 63], [97, 128], [2, 100, 66, 26], [41, 124], [52, 72]]]
 h' := ![![[77, 44, 125], [70, 135, 120], [115, 32, 114], [115, 57, 51], [103, 140, 8], [44, 40, 21], [0, 0, 1], [0, 1]], ![[124, 106, 26], [64, 76, 150], [14, 35, 78], [110, 46, 149], [133, 21, 77], [9, 9, 129], [53, 82, 106], [77, 44, 125]], ![[0, 1], [125, 91, 32], [48, 84, 110], [73, 48, 102], [93, 141, 66], [140, 102, 1], [56, 69, 44], [124, 106, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 109], []]
 b := ![[], [81, 146, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [132, 63, 101, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![145111, -4983, -3020]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![961, -33, -20]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [19, 60, 151, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 114, 108], [34, 42, 49], [0, 1]]
 g := ![![[18, 127, 140], [132, 90], [118, 54, 130], [112, 45, 111], [149, 139, 105], [6, 1], []], ![[93, 1, 122, 35], [143, 105], [77, 15, 42, 144], [107, 39, 49, 143], [154, 130, 64, 57], [90, 37], [94, 46]], ![[70, 22, 116, 109], [117, 115], [95, 64, 155, 82], [63, 26, 146, 113], [127, 95, 150, 1], [81, 122], [153, 46]]]
 h' := ![![[129, 114, 108], [56, 103, 104], [113, 91, 103], [70, 143, 82], [152, 2, 41], [43, 92, 133], [0, 0, 1], [0, 1]], ![[34, 42, 49], [38, 140, 106], [20, 52, 24], [95, 47, 48], [148, 29, 54], [6, 74, 136], [97, 133, 42], [129, 114, 108]], ![[0, 1], [120, 71, 104], [107, 14, 30], [138, 124, 27], [21, 126, 62], [136, 148, 45], [133, 24, 114], [34, 42, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106, 144], []]
 b := ![[], [156, 147, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [19, 60, 151, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17485875, -4200692, -1353968]
  a := ![1, -2, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-111375, -26756, -8624]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def PBC157 : ContainsPrimesAboveP 157 ![I157N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![157, 0, 0]]) timesTableT_eq_Table B_one_repr 157 (by decide) 𝕀

instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-6, 76, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-6, 76, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![157, 76, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-6, 76, 1], ![198, 100, 456], ![15015, 2313, 24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-157, -76, 163]], ![![-1, 0, 1], ![-438, -212, 456], ![69, 3, 24]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [69, 138, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 162], [0, 1]]
 g := ![![[2, 26], [58, 22], [60], [26], [25], [113, 136], [1]], ![[0, 137], [119, 141], [60], [26], [25], [90, 27], [1]]]
 h' := ![![[25, 162], [73, 134], [107, 115], [160, 95], [145, 29], [27, 158], [94, 25], [0, 1]], ![[0, 1], [0, 29], [48, 48], [90, 68], [55, 134], [65, 5], [67, 138], [25, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [157, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [69, 138, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4788, 5041, 2136]
  a := ![0, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2028, -965, 2136]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![33, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![33, 1, 0]] 
 ![![163, 0, 0], ![33, 1, 0], ![139, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![33, 1, 0], ![0, 34, 6], ![198, 30, 33]]]
  hmulB := by decide  
  f := ![![![2575, 78, 0], ![-12714, 0, 0]], ![![495, 15, 0], ![-2444, 0, 0]], ![![2191, 38, -5], ![-10818, 136, 0]]]
  g := ![![![1, 0, 0], ![-33, 163, 0], ![-139, 0, 163]], ![![0, 1, 0], ![-12, 34, 6], ![-33, 30, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-6, 76, 1]] ![![163, 0, 0], ![33, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![5379, 163, 0]], ![![-978, 12388, 163], ![0, 2608, 489]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![33, 1, 0]]], ![![![-6, 76, 1]], ![![0, 16, 3]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [153, 146, 96, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 131, 108], [42, 35, 59], [0, 1]]
 g := ![![[14, 36, 77], [12, 131, 62], [10, 99, 7], [105, 77], [117, 66], [52, 71, 1], []], ![[83, 57, 81, 99], [142, 111, 84, 63], [17, 24, 150, 44], [7, 56], [93, 33], [25, 140, 112, 36], [64, 141]], ![[160, 144, 161, 53], [42, 25, 43, 146], [50, 125, 76, 60], [22, 72], [161, 76], [127, 89, 155, 145], [113, 141]]]
 h' := ![![[29, 131, 108], [1, 143, 54], [140, 122, 79], [14, 19, 95], [61, 28, 113], [60, 82, 20], [0, 0, 1], [0, 1]], ![[42, 35, 59], [84, 150, 133], [120, 93, 76], [83, 101, 33], [94, 40, 132], [104, 105, 37], [67, 61, 35], [29, 131, 108]], ![[0, 1], [152, 41, 147], [60, 119, 12], [46, 47, 39], [78, 99, 89], [117, 147, 110], [6, 106, 131], [42, 35, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 130], []]
 b := ![[], [62, 111, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [153, 146, 96, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9402994953, 2665303467, 1066891858]
  a := ![1, 20, 101]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![56305359, 15959901, 6388574]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-71, -76, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-71, -76, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![102, 97, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-71, -76, 1], ![198, -117, -456], ![-15081, -2247, -41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-102, -97, 173]], ![![-1, -1, 1], ![270, 255, -456], ![-63, 10, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [16, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [91, 172], [0, 1]]
 g := ![![[70, 119], [136], [19, 160], [170, 35], [23], [12, 150], [1]], ![[0, 54], [136], [47, 13], [68, 138], [23], [168, 23], [1]]]
 h' := ![![[91, 172], [107, 130], [42, 89], [48, 81], [166, 30], [154, 159], [157, 91], [0, 1]], ![[0, 1], [0, 43], [10, 84], [153, 92], [128, 143], [91, 14], [134, 82], [91, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [164, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [16, 82, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4390, 3917, 3174]
  a := ![-1, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1846, -1757, 3174]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-63, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-63, 1, 0]] 
 ![![173, 0, 0], ![110, 1, 0], ![41, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-63, 1, 0], ![0, -62, 6], ![198, 30, -63]]]
  hmulB := by decide  
  f := ![![![5230, -83, 0], ![14359, 0, 0]], ![![3340, -53, 0], ![9170, 0, 0]], ![![1348, -11, -1], ![3701, 29, 0]]]
  g := ![![![1, 0, 0], ![-110, 173, 0], ![-41, 0, 173]], ![![-1, 1, 0], ![38, -62, 6], ![-3, 30, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-71, -76, 1]] ![![173, 0, 0], ![-63, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-10899, 173, 0]], ![![-12283, -13148, 173], ![4671, 4671, -519]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-63, 1, 0]]], ![![![-71, -76, 1]], ![![27, 27, -3]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![58, 16, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![58, 16, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![58, 16, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![58, 16, 1], ![198, 104, 96], ![3135, 513, 88]]]
  hmulB := by decide  
  f := ![![![-57, -16, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-58, -16, 179]], ![![0, 0, 1], ![-30, -8, 96], ![-11, -5, 88]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [18, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [134, 178], [0, 1]]
 g := ![![[92, 144], [113, 144], [110], [89], [168, 177], [174, 56], [1]], ![[56, 35], [77, 35], [110], [89], [79, 2], [160, 123], [1]]]
 h' := ![![[134, 178], [114, 167], [133, 12], [12, 162], [19, 39], [90, 78], [161, 134], [0, 1]], ![[0, 1], [117, 12], [130, 167], [61, 17], [54, 140], [160, 101], [38, 45], [134, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [14, 112]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [18, 45, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10677, 12741, 9489]
  a := ![0, 3, 17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3015, -777, 9489]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![83, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![83, 1, 0]] 
 ![![179, 0, 0], ![83, 1, 0], ![91, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![83, 1, 0], ![0, 84, 6], ![198, 30, 83]]]
  hmulB := by decide  
  f := ![![![3985, 48, 0], ![-8592, 0, 0]], ![![1743, 21, 0], ![-3758, 0, 0]], ![![1999, 10, -1], ![-4310, 30, 0]]]
  g := ![![![1, 0, 0], ![-83, 179, 0], ![-91, 0, 179]], ![![0, 1, 0], ![-42, 84, 6], ![-55, 30, 83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![58, 16, 1]] ![![179, 0, 0], ![83, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![14857, 179, 0]], ![![10382, 2864, 179], ![5012, 1432, 179]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![83, 1, 0]]], ![![![58, 16, 1]], ![![28, 8, 1]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39319, -8898, -3256]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-39319, -8898, -3256]] 
 ![![181, 0, 0], ![0, 181, 0], ![160, 76, 1]] where
  M :=![![![-39319, -8898, -3256], ![-644688, -145897, -53388], ![-1654356, -374388, -136999]]]
  hmulB := by decide  
  f := ![![![461, 54, -32]], ![![-6336, -445, 324]], ![![-2188, -136, 105]]]
  g := ![![![2661, 1318, -3256], ![43632, 21611, -53388], ![111964, 55456, -136999]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [94, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 180], [0, 1]]
 g := ![![[159, 52], [70], [30, 114], [147], [133, 144], [55, 137], [1]], ![[0, 129], [70], [120, 67], [147], [180, 37], [106, 44], [1]]]
 h' := ![![[77, 180], [101, 41], [76, 147], [107, 64], [168, 50], [79, 12], [87, 77], [0, 1]], ![[0, 1], [0, 140], [173, 34], [148, 117], [36, 131], [98, 169], [43, 104], [77, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [33, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [94, 104, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![73038, 65092, 39600]
  a := ![2, -8, -38]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-34602, -16268, 39600]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-461, -54, 32]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-461, -54, 32]] 
 ![![181, 0, 0], ![87, 1, 0], ![172, 0, 1]] where
  M :=![![![-461, -54, 32], ![6336, 445, -324], ![-11748, -564, 499]]]
  hmulB := by decide  
  f := ![![![39319, 8898, 3256]], ![![22461, 5083, 1860]], ![![46504, 10524, 3851]]]
  g := ![![![-7, -54, 32], ![129, 445, -324], ![-268, -564, 499]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-39319, -8898, -3256]] ![![-461, -54, 32]]
  ![![181, 0, 0]] where
 M := ![![![-181, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-53991454039778, -370381665273, 1427535974613]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-53991454039778, -370381665273, 1427535974613]] 
 ![![191, 0, 0], ![0, 191, 0], ![39, 89, 1]] where
  M :=![![![-53991454039778, -370381665273, 1427535974613], ![282652122973374, -11535756466661, -2222289991638], ![-120444256886283, 35997237204039, -11165374801388]]]
  hmulB := by decide  
  f := ![![![1093179814308692834179850, 247392151744020303315513, 90527763446887599800337]], ![![17924497162483744760466726, 4056404869459341131505473, 1484352910464121819893078]], ![![8816285288328068238102687, 1995170199193539541498265, 730089028918590466967995]]]
  g := ![![![-574164173035, -667126091130, 1427535974613], ![1933620066216, 975120695231, -2222289991638], ![1649242724439, 5391181123181, -11165374801388]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [78, 174, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 190], [0, 1]]
 g := ![![[61, 120], [41, 65], [170, 26], [41, 154], [175, 5], [160, 98], [1]], ![[0, 71], [0, 126], [39, 165], [176, 37], [69, 186], [107, 93], [1]]]
 h' := ![![[17, 190], [49, 87], [110, 16], [49, 44], [102, 125], [126, 14], [113, 17], [0, 1]], ![[0, 1], [0, 104], [0, 175], [33, 147], [126, 66], [173, 177], [20, 174], [17, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [74, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [78, 174, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2476, 33, 230]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-34, -107, 230]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1093179814308692834179850, -247392151744020303315513, -90527763446887599800337]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-1093179814308692834179850, -247392151744020303315513, -90527763446887599800337]] 
 ![![191, 0, 0], ![39, 1, 0], ![122, 0, 1]] where
  M :=![![![-1093179814308692834179850, -247392151744020303315513, -90527763446887599800337], ![-17924497162483744760466726, -4056404869459341131505473, -1484352910464121819893078], ![-45996229851568729263060453, -10409180746067899892876511, -3809012717715320828189960]]]
  hmulB := by decide  
  f := ![![![53991454039778, 370381665273, -1427535974613]], ![![9544578976848, 136024300588, -279851377059]], ![![35117286124289, 48111654237, -853371801578]]]
  g := ![![![102615189760358042778881, -247392151744020303315513, -90527763446887599800337], ![1682546323680907965419907, -4056404869459341131505473, -1484352910464121819893078], ![4317598800033238259676956, -10409180746067899892876511, -3809012717715320828189960]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-53991454039778, -370381665273, 1427535974613]] ![![-1093179814308692834179850, -247392151744020303315513, -90527763446887599800337]]
  ![![191, 0, 0]] where
 M := ![![![-191, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![42, 1, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![42, 1, 0]] 
 ![![193, 0, 0], ![42, 1, 0], ![85, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![42, 1, 0], ![0, 43, 6], ![198, 30, 42]]]
  hmulB := by decide  
  f := ![![![883, 21, 0], ![-4053, 0, 0]], ![![126, 3, 0], ![-578, 0, 0]], ![![415, -26, -5], ![-1905, 161, 0]]]
  g := ![![![1, 0, 0], ![-42, 193, 0], ![-85, 0, 193]], ![![0, 1, 0], ![-12, 43, 6], ![-24, 30, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N0 : Nat.card (O ⧸ I193N0) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N0)

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := prime_ideal_of_norm_prime hp193.out _ NI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-341042404, -36540403, 22345071]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-341042404, -36540403, 22345071]] 
 ![![193, 0, 0], ![152, 1, 0], ![177, 0, 1]] where
  M :=![![![-341042404, -36540403, 22345071], ![4424324058, 292769323, -219242418], ![-7972387137, -358824747, 329309726]]]
  hmulB := by decide  
  f := ![![![17742180367817252, 4015145651587541, 1469254999357521]], ![![15480434744979334, 3503301114204335, 1281956651874966]], ![![20139271239063153, 4557619507033260, 1667761477900643]]]
  g := ![![![6518245, -36540403, 22345071], ![-6583964, 292769323, -219242418], ![-60719415, -358824747, 329309726]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-2, 1, 0]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-2, 1, 0]] 
 ![![193, 0, 0], ![191, 1, 0], ![64, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-2, 1, 0], ![0, -1, 6], ![198, 30, -2]]]
  hmulB := by decide  
  f := ![![![3, 95, -576], ![193, 18528, 0]], ![![1, 95, -570], ![1, 18335, 0]], ![![2, 31, -191], ![161, 6144, 0]]]
  g := ![![![1, 0, 0], ![-191, 193, 0], ![-64, 0, 193]], ![![-1, 1, 0], ![-1, -1, 6], ![-28, 30, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![42, 1, 0]] ![![-341042404, -36540403, 22345071]]
  ![![193, 0, 0], ![-94, -64, 1]] where
 M := ![![![-65821183972, -7052297779, 4312598703]], ![![-9899456910, -1241927603, 719250564]]]
 hmul := by decide  
 g := ![![![![-276569496, 7356045, 21659189], ![132375226, 0, 0]]], ![![![-41482508, 244301, 3622325], ![20141839, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-94, -64, 1]] ![![193, 0, 0], ![-2, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-386, 193, 0]], ![![-18142, -12352, 193], ![386, 0, -386]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-2, 1, 0]]], ![![![-94, -64, 1]], ![![2, 0, -2]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1, I193N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
    exact isPrimeI193N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0 ⊙ MulI193N1)


lemma PB204I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB204I3 : PrimesBelowBoundCertificateInterval O 137 193 204 where
  m := 11
  g := ![2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB204I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1, I193N2]
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
    · exact ![3442951]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![32761, 181]
    · exact ![36481, 191]
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
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
  β := ![I139N1, I149N1, I163N1, I173N1, I179N1, I181N1, I191N1, I193N0, I193N1, I193N2]
  Il := ![[I139N1], [I149N1], [], [], [I163N1], [], [I173N1], [I179N1], [I181N1], [I191N1], [I193N0, I193N1, I193N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
