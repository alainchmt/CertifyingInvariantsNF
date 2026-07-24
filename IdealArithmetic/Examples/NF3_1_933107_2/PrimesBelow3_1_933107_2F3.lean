
import IdealArithmetic.Examples.NF3_1_933107_2.RI3_1_933107_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 2, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![15, 2, 0]] 
 ![![139, 0, 0], ![77, 1, 0], ![48, 0, 1]] where
  M :=![![![15, 2, 0], ![0, 15, 2], ![-436, 74, 17]]]
  hmulB := by decide  
  f := ![![![-107, 34, -4]], ![![-53, 17, -2]], ![![-84, 26, -3]]]
  g := ![![![-1, 2, 0], ![-9, 15, 2], ![-50, 74, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, -65, -8]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-31, -65, -8]] 
 ![![139, 0, 0], ![100, 1, 0], ![8, 0, 1]] where
  M :=![![![-31, -65, -8], ![1744, -327, -73], ![15914, -957, -400]]]
  hmulB := by decide  
  f := ![![![-60939, 18344, -2129]], ![![-40502, 12192, -1415]], ![![-28938, 8711, -1011]]]
  g := ![![![47, -65, -8], ![252, -327, -73], ![826, -957, -400]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![15, 2, 0]] ![![-31, -65, -8]]
  ![![3023, -1629, -266]] where
 M := ![![![3023, -1629, -266]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![3023, -1629, -266]] ![![-31, -65, -8]]
  ![![139, 0, 0]] where
 M := ![![![-7167813, 590750, 201133]]]
 hmul := by decide  
 g := ![![![![-51567, 4250, 1447]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [24, 1, 76, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [98, 0, 10], [124, 148, 139], [0, 1]]
 g := ![![[58, 96, 133], [26, 37], [130, 138, 33], [99, 95], [47, 123, 104], [73, 1], []], ![[20, 91, 72, 146], [84, 133], [113, 118, 0, 135], [130, 63], [137, 34, 89, 57], [103, 1], [148, 100]], ![[42, 145, 72, 93], [105, 17], [109, 61, 3, 70], [28, 148], [122, 145, 135, 52], [], [19, 100]]]
 h' := ![![[98, 0, 10], [53, 98, 122], [9, 139, 22], [81, 8, 35], [64, 85, 86], [36, 52, 113], [0, 0, 1], [0, 1]], ![[124, 148, 139], [21, 107, 113], [10, 117, 27], [62, 71, 45], [65, 51, 19], [32, 93, 109], [92, 134, 148], [98, 0, 10]], ![[0, 1], [43, 93, 63], [103, 42, 100], [134, 70, 69], [106, 13, 44], [102, 4, 76], [20, 15], [124, 148, 139]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 126], []]
 b := ![[], [12, 113, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [24, 1, 76, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-55130, 2384, 2384]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-370, 16, 16]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀

instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-89, -24, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-89, -24, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![62, 127, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-89, -24, 1], ![-218, -52, -23], ![5014, -1069, -75]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-62, -127, 151]], ![![-1, -1, 1], ![8, 19, -23], ![64, 56, -75]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [147, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [98, 150], [0, 1]]
 g := ![![[100, 58], [63, 44], [82, 31], [144], [64, 85], [91], [1]], ![[46, 93], [147, 107], [100, 120], [144], [89, 66], [91], [1]]]
 h' := ![![[98, 150], [101, 80], [26, 78], [125, 22], [105, 12], [78, 38], [4, 98], [0, 1]], ![[0, 1], [89, 71], [120, 73], [16, 129], [73, 139], [27, 113], [95, 53], [98, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [87, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [147, 53, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![749, -2175, 487]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-195, -424, 487]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![23, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![23, 1, 0]] 
 ![![151, 0, 0], ![23, 1, 0], ![75, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![23, 1, 0], ![0, 23, 1], ![-218, 37, 24]]]
  hmulB := by decide  
  f := ![![![921, 40, 0], ![-6040, 0, 0]], ![![115, 5, 0], ![-754, 0, 0]], ![![441, 19, 0], ![-2892, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 151, 0], ![-75, 0, 151]], ![![0, 1, 0], ![-4, 23, 1], ![-19, 37, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-89, -24, 1]] ![![151, 0, 0], ![23, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![3473, 151, 0]], ![![-13439, -3624, 151], ![-2265, -604, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![23, 1, 0]]], ![![![-89, -24, 1]], ![![-15, -4, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [130, 146, 109, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [142, 83, 145], [63, 73, 12], [0, 1]]
 g := ![![[139, 102, 120], [112, 42], [90, 117, 81], [117, 109, 9], [62, 58, 30], [48, 1], []], ![[5, 82, 74, 124], [7, 13], [135, 96, 137, 86], [48, 23, 1, 130], [106, 80, 114, 49], [71, 148], [53, 144]], ![[102, 147, 64, 156], [41, 147], [76, 49, 78, 46], [63, 127, 151, 86], [142, 41, 107, 51], [99, 138], [29, 144]]]
 h' := ![![[142, 83, 145], [14, 155, 80], [75, 114, 55], [19, 131, 148], [104, 80, 154], [40, 84, 117], [0, 0, 1], [0, 1]], ![[63, 73, 12], [16, 58, 55], [112, 39, 135], [106, 109, 126], [59, 69, 77], [50, 109, 154], [86, 97, 73], [142, 83, 145]], ![[0, 1], [108, 101, 22], [147, 4, 124], [44, 74, 40], [151, 8, 83], [41, 121, 43], [42, 60, 83], [63, 73, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 2], []]
 b := ![[], [135, 156, 131], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [130, 146, 109, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![101422, 37366, -3140]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![646, 238, -20]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-1, 54, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-1, 54, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![162, 54, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-1, 54, 1], ![-218, 36, 55], ![-11990, 1817, 91]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-162, -54, 163]], ![![-1, 0, 1], ![-56, -18, 55], ![-164, -19, 91]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [54, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 162], [0, 1]]
 g := ![![[47, 160], [120, 93], [95], [133], [151], [149, 10], [1]], ![[0, 3], [110, 70], [95], [133], [151], [34, 153], [1]]]
 h' := ![![[70, 162], [40, 46], [55, 16], [135, 101], [54, 40], [104, 92], [109, 70], [0, 1]], ![[0, 1], [0, 117], [34, 147], [33, 62], [83, 123], [24, 71], [119, 93], [70, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [150, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [54, 93, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-600, -200, -52]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![48, 16, -52]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-55, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-55, 1, 0]] 
 ![![163, 0, 0], ![108, 1, 0], ![72, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-55, 1, 0], ![0, -55, 1], ![-218, 37, -54]]]
  hmulB := by decide  
  f := ![![![5996, -109, 0], ![17767, 0, 0]], ![![4016, -73, 0], ![11900, 0, 0]], ![![2714, -49, 0], ![8042, 1, 0]]]
  g := ![![![1, 0, 0], ![-108, 163, 0], ![-72, 0, 163]], ![![-1, 1, 0], ![36, -55, 1], ![-2, 37, -54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-1, 54, 1]] ![![163, 0, 0], ![-55, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-8965, 163, 0]], ![![-163, 8802, 163], ![-163, -2934, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-55, 1, 0]]], ![![![-1, 54, 1]], ![![-1, -18, 0]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [9, 28, 70, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 110, 143], [162, 56, 24], [0, 1]]
 g := ![![[100, 77, 154], [117, 14, 64], [40, 14, 150], [49, 47], [34, 62], [29, 97, 1], []], ![[33, 95, 33, 39], [164, 133, 141, 52], [123, 108, 163, 113], [51, 38], [97, 130], [42, 57, 0, 53], [158, 75]], ![[144, 162, 51, 126], [124, 90, 52, 126], [73, 45, 84, 66], [97, 29], [22, 22], [123, 45, 98, 154], [110, 75]]]
 h' := ![![[102, 110, 143], [116, 113, 34], [141, 93, 8], [62, 34, 22], [13, 141, 106], [73, 152, 88], [0, 0, 1], [0, 1]], ![[162, 56, 24], [64, 156, 27], [154, 161, 53], [66, 140, 82], [58, 123, 47], [51, 149, 111], [131, 140, 56], [102, 110, 143]], ![[0, 1], [141, 65, 106], [139, 80, 106], [38, 160, 63], [57, 70, 14], [64, 33, 135], [37, 27, 110], [162, 56, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 104], []]
 b := ![[], [109, 103, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [9, 28, 70, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2792908, 204575, 72979]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16724, 1225, 437]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [129, 114, 75, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [134, 155, 104], [137, 17, 69], [0, 1]]
 g := ![![[121, 164, 55], [12, 130], [2, 109, 41], [69, 54, 132], [6, 136], [148, 98, 1], []], ![[16, 53, 32, 61], [132, 36], [74, 16, 67, 91], [45, 167, 91, 65], [74, 137], [170, 104, 93, 127], [59, 90]], ![[125, 8, 36, 26], [126, 172], [51, 9, 172, 69], [108, 68, 139, 156], [126, 122], [2, 154, 141, 39], [94, 90]]]
 h' := ![![[134, 155, 104], [141, 151, 48], [88, 99, 86], [95, 79, 53], [129, 31, 88], [111, 69, 89], [0, 0, 1], [0, 1]], ![[137, 17, 69], [11, 68, 85], [137, 110, 167], [3, 90, 121], [165, 167, 49], [14, 24, 39], [138, 22, 17], [134, 155, 104]], ![[0, 1], [93, 127, 40], [36, 137, 93], [43, 4, 172], [68, 148, 36], [135, 80, 45], [69, 151, 155], [137, 17, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84, 8], []]
 b := ![[], [127, 46, 133], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [129, 114, 75, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27161, 1038, -346]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-157, 6, -2]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [77, 4, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [146, 23, 176], [5, 155, 3], [0, 1]]
 g := ![![[26, 147, 81], [135, 106, 60], [165, 36], [114, 151], [52, 38, 15], [64, 151, 1], []], ![[89, 47, 161, 166], [165, 169, 50, 143], [105, 161], [9, 49], [44, 56, 7, 69], [66, 19, 108, 62], [147, 9]], ![[110, 145, 151, 151], [178, 76, 69, 25], [126, 141], [155, 153], [58, 71, 68, 138], [81, 12, 128, 155], [141, 9]]]
 h' := ![![[146, 23, 176], [166, 164, 9], [128, 38, 113], [53, 53, 6], [113, 163, 144], [84, 110, 33], [0, 0, 1], [0, 1]], ![[5, 155, 3], [60, 61, 8], [119, 164, 38], [111, 177, 55], [154, 42, 172], [38, 21, 131], [152, 65, 155], [146, 23, 176]], ![[0, 1], [158, 133, 162], [125, 156, 28], [124, 128, 118], [31, 153, 42], [104, 48, 15], [87, 114, 23], [5, 155, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 118], []]
 b := ![[], [26, 55, 99], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [77, 4, 28, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![99703, -111517, 11277]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![557, -623, 63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def PBC179 : ContainsPrimesAboveP 179 ![I179N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![179, 0, 0]]) timesTableT_eq_Table B_one_repr 179 (by decide) 𝕀

instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![47, 1, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![47, 1, 0]] 
 ![![181, 0, 0], ![47, 1, 0], ![144, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![47, 1, 0], ![0, 47, 1], ![-218, 37, 48]]]
  hmulB := by decide  
  f := ![![![3479, 74, 0], ![-13394, 0, 0]], ![![893, 19, 0], ![-3438, 0, 0]], ![![2786, 59, 0], ![-10726, 1, 0]]]
  g := ![![![1, 0, 0], ![-47, 181, 0], ![-144, 0, 181]], ![![0, 1, 0], ![-13, 47, 1], ![-49, 37, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-47, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-47, 1, 0]] 
 ![![181, 0, 0], ![134, 1, 0], ![144, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-47, 1, 0], ![0, -47, 1], ![-218, 37, -46]]]
  hmulB := by decide  
  f := ![![![5923, -126, 0], ![22806, 0, 0]], ![![4372, -93, 0], ![16834, 0, 0]], ![![4760, -101, 0], ![18328, 1, 0]]]
  g := ![![![1, 0, 0], ![-134, 181, 0], ![-144, 0, 181]], ![![-1, 1, 0], ![34, -47, 1], ![8, 37, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, 0]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![-1, 1, 0]] 
 ![![181, 0, 0], ![180, 1, 0], ![180, 0, 1]] where
  M :=![![![-1, 1, 0], ![0, -1, 1], ![-218, 37, 0]]]
  hmulB := by decide  
  f := ![![![37, 0, -1]], ![![38, 0, -1]], ![![38, 1, -1]]]
  g := ![![![-1, 1, 0], ![0, -1, 1], ![-38, 37, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![47, 1, 0]] ![![181, 0, 0], ![-47, 1, 0]]
  ![![-37, 0, 1]] where
 M := ![![![32761, 0, 0], ![-8507, 181, 0]], ![![8507, 181, 0], ![-2209, 0, 1]]]
 hmul := by decide  
 g := ![![![![181, -181, 0]], ![![-47, 48, -1]]], ![![![47, -46, -1]], ![![-11, 12, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![-37, 0, 1]] ![![-1, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![-181, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-65, 67, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-65, 67, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![126, 67, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-65, 67, 1], ![-218, -28, 68], ![-14824, 2298, 40]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-126, -67, 191]], ![![-1, 0, 1], ![-46, -24, 68], ![-104, -2, 40]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [38, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [171, 190], [0, 1]]
 g := ![![[91, 109], [42, 103], [55, 18], [28, 92], [80, 54], [14, 18], [1]], ![[12, 82], [83, 88], [77, 173], [98, 99], [146, 137], [36, 173], [1]]]
 h' := ![![[171, 190], [123, 142], [11, 165], [82, 20], [16, 130], [41, 98], [153, 171], [0, 1]], ![[0, 1], [148, 49], [149, 26], [64, 171], [90, 61], [182, 93], [171, 20], [171, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [3, 134]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [38, 20, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7930, -2444, 260]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-130, -104, 260]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-68, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-68, 1, 0]] 
 ![![191, 0, 0], ![123, 1, 0], ![151, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-68, 1, 0], ![0, -68, 1], ![-218, 37, -67]]]
  hmulB := by decide  
  f := ![![![5781, -85, 0], ![16235, 0, 0]], ![![3809, -56, 0], ![10697, 0, 0]], ![![4581, -67, 0], ![12865, 1, 0]]]
  g := ![![![1, 0, 0], ![-123, 191, 0], ![-151, 0, 191]], ![![-1, 1, 0], ![43, -68, 1], ![28, 37, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-65, 67, 1]] ![![191, 0, 0], ![-68, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-12988, 191, 0]], ![![-12415, 12797, 191], ![4202, -4584, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-68, 1, 0]]], ![![![-65, 67, 1]], ![![22, -24, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0]] 
 ![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [163, 108, 80, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 23, 124], [50, 169, 69], [0, 1]]
 g := ![![[60, 35, 138], [38, 83], [174, 16], [0, 54], [53, 145], [132, 31], [1]], ![[136, 168, 126, 179], [141, 134], [71, 107], [51, 63], [146, 189], [81, 84], [14, 115, 126, 170]], ![[160, 45, 81, 151], [126, 2], [147, 161], [161, 139], [36, 110], [52, 12], [163, 157, 66, 23]]]
 h' := ![![[63, 23, 124], [7, 133, 157], [5, 1, 58], [31, 37, 4], [113, 69, 132], [35, 73, 97], [30, 85, 113], [0, 1]], ![[50, 169, 69], [113, 144, 179], [69, 141, 83], [86, 167, 53], [183, 52, 177], [7, 146, 162], [146, 2, 108], [63, 23, 124]], ![[0, 1], [167, 109, 50], [132, 51, 52], [136, 182, 136], [18, 72, 77], [17, 167, 127], [1, 106, 165], [50, 169, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [172, 100], []]
 b := ![[], [134, 190, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [163, 108, 80, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![98816, -50759, 8685]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![512, -263, 45]
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



lemma PB274I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB274I3 : PrimesBelowBoundCertificateInterval O 137 193 274 where
  m := 11
  g := ![3, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB274I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0]
    · exact ![I179N0]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1]
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
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![5177717]
    · exact ![5735339]
    · exact ![181, 181, 181]
    · exact ![36481, 191]
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
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I139N0, I139N1, I151N1, I163N1, I181N0, I181N1, I181N2, I191N1]
  Il := ![[I139N0, I139N1, I139N1], [], [I151N1], [], [I163N1], [], [], [], [I181N0, I181N1, I181N2], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
