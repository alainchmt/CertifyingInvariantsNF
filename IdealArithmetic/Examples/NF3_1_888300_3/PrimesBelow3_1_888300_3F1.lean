
import IdealArithmetic.Examples.NF3_1_888300_3.RI3_1_888300_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [36, 32, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 18, 35], [30, 18, 2], [0, 1]]
 g := ![![[3, 6, 26], [31, 33], [29, 28, 34], [33, 1], []], ![[27, 7, 23, 6], [10, 4], [17, 23, 19, 23], [31, 28], [23, 4]], ![[34, 7, 19, 35], [26, 11], [25, 15, 36, 24], [4, 28], [19, 4]]]
 h' := ![![[3, 18, 35], [21, 13, 27], [29, 4, 25], [33, 18, 21], [0, 0, 1], [0, 1]], ![[30, 18, 2], [36, 36, 16], [27, 12, 35], [19, 22, 9], [32, 5, 18], [3, 18, 35]], ![[0, 1], [27, 25, 31], [36, 21, 14], [3, 34, 7], [31, 32, 18], [30, 18, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 15], []]
 b := ![[], [14, 31, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [36, 32, 4, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-856254, -284752, -24568]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23142, -7696, -664]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-91, 10, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-91, 10, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![32, 10, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-91, 10, 1], ![730, 59, 10], ![7300, 2230, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![3, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -10, 41]], ![![-3, 0, 1], ![10, -1, 10], ![132, 40, 59]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [26, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 40], [0, 1]]
 g := ![![[33, 36], [25], [32], [35, 9], [1]], ![[18, 5], [25], [32], [21, 32], [1]]]
 h' := ![![[3, 40], [4, 6], [11, 36], [33, 14], [15, 3], [0, 1]], ![[0, 1], [22, 35], [37, 5], [34, 27], [24, 38], [3, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [25, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [26, 38, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8771, 4698, 1462]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1355, -242, 1462]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-10, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-10, 1, 0]] 
 ![![41, 0, 0], ![31, 1, 0], ![23, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-10, 1, 0], ![0, -10, 1], ![730, 150, -10]]]
  hmulB := by decide  
  f := ![![![391, -39, 0], ![1599, 0, 0]], ![![301, -30, 0], ![1231, 0, 0]], ![![233, -23, 0], ![953, 1, 0]]]
  g := ![![![1, 0, 0], ![-31, 41, 0], ![-23, 0, 41]], ![![-1, 1, 0], ![7, -10, 1], ![-90, 150, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-91, 10, 1]] ![![41, 0, 0], ![-10, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-410, 41, 0]], ![![-3731, 410, 41], ![1640, -41, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-10, 1, 0]]], ![![![-91, 10, 1]], ![![40, -1, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-83, 14, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-83, 14, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![3, 14, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-83, 14, 1], ![730, 67, 14], ![10220, 2830, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -14, 43]], ![![-2, 0, 1], ![16, -3, 14], ![233, 44, 67]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [6, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 42], [0, 1]]
 g := ![![[41, 36], [31, 1], [38], [36, 15], [1]], ![[0, 7], [0, 42], [38], [1, 28], [1]]]
 h' := ![![[12, 42], [29, 37], [31, 1], [42, 34], [37, 12], [0, 1]], ![[0, 1], [0, 6], [0, 42], [20, 9], [9, 31], [12, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [13, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [6, 31, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![658, 333, 248]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, -73, 248]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-14, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-14, 1, 0]] 
 ![![43, 0, 0], ![29, 1, 0], ![19, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-14, 1, 0], ![0, -14, 1], ![730, 150, -14]]]
  hmulB := by decide  
  f := ![![![589, -42, 0], ![1806, 0, 0]], ![![407, -29, 0], ![1248, 0, 0]], ![![285, -20, 0], ![874, 1, 0]]]
  g := ![![![1, 0, 0], ![-29, 43, 0], ![-19, 0, 43]], ![![-1, 1, 0], ![9, -14, 1], ![-78, 150, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-83, 14, 1]] ![![43, 0, 0], ![-14, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-602, 43, 0]], ![![-3569, 602, 43], ![1892, -129, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-14, 1, 0]]], ![![![-83, 14, 1]], ![![44, -3, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![12, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![12, 1, 0]] 
 ![![47, 0, 0], ![12, 1, 0], ![44, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![12, 1, 0], ![0, 12, 1], ![730, 150, 12]]]
  hmulB := by decide  
  f := ![![![25, 2, 0], ![-94, 0, 0]], ![![-12, -1, 0], ![48, 0, 0]], ![![28, 2, 0], ![-106, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 47, 0], ![-44, 0, 47]], ![![0, 1, 0], ![-4, 12, 1], ![-34, 150, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![23, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![23, 1, 0]] 
 ![![47, 0, 0], ![23, 1, 0], ![35, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![23, 1, 0], ![0, 23, 1], ![730, 150, 23]]]
  hmulB := by decide  
  f := ![![![208, 9, 0], ![-423, 0, 0]], ![![92, 4, 0], ![-187, 0, 0]], ![![150, 6, 0], ![-305, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 47, 0], ![-35, 0, 47]], ![![0, 1, 0], ![-12, 23, 1], ![-75, 150, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![12, 1, 0]] ![![47, 0, 0], ![12, 1, 0]]
  ![![47, 0, 0], ![-91, -23, 1]] where
 M := ![![![2209, 0, 0], ![564, 47, 0]], ![![564, 47, 0], ![144, 24, 1]]]
 hmul := by decide  
 g := ![![![![47, 0, 0], ![0, 0, 0]], ![![12, 1, 0], ![0, 0, 0]]], ![![![12, 1, 0], ![0, 0, 0]], ![![5, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-91, -23, 1]] ![![47, 0, 0], ![23, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![1081, 47, 0]], ![![-4277, -1081, 47], ![-1363, -470, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![23, 1, 0]]], ![![![-91, -23, 1]], ![![-29, -10, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-84, -15, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-84, -15, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![22, 38, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-84, -15, 1], ![730, 66, -15], ![-10950, -1520, 66]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -38, 53]], ![![-2, -1, 1], ![20, 12, -15], ![-234, -76, 66]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [52, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 52], [0, 1]]
 g := ![![[4, 52], [10], [20, 29], [24], [4, 1]], ![[0, 1], [10], [30, 24], [24], [8, 52]]]
 h' := ![![[4, 52], [39, 30], [20, 13], [40, 20], [4, 17], [0, 1]], ![[0, 1], [0, 23], [19, 40], [14, 33], [19, 36], [4, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [32, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [52, 49, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4278, 5721, 1198]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-578, -751, 1198]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![15, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![15, 1, 0]] 
 ![![53, 0, 0], ![15, 1, 0], ![40, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![15, 1, 0], ![0, 15, 1], ![730, 150, 15]]]
  hmulB := by decide  
  f := ![![![361, 24, 0], ![-1272, 0, 0]], ![![105, 7, 0], ![-370, 0, 0]], ![![260, 17, 0], ![-916, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 53, 0], ![-40, 0, 53]], ![![0, 1, 0], ![-5, 15, 1], ![-40, 150, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-84, -15, 1]] ![![53, 0, 0], ![15, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![795, 53, 0]], ![![-4452, -795, 53], ![-530, -159, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![15, 1, 0]]], ![![![-84, -15, 1]], ![![-10, -3, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [38, 41, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 42, 18], [37, 16, 41], [0, 1]]
 g := ![![[57, 2, 48], [34, 45, 45], [32, 12], [24, 49, 25], [1]], ![[24, 10, 20, 6], [38, 36, 35, 11], [54, 29], [30, 24, 24, 31], [14, 21, 41, 50]], ![[35, 21, 49, 41], [47, 13, 54, 3], [26, 16], [47, 51, 32, 15], [40, 50, 49, 9]]]
 h' := ![![[17, 42, 18], [6, 12, 15], [44, 13, 24], [32, 14, 37], [21, 18, 54], [0, 1]], ![[37, 16, 41], [25, 11, 43], [28, 5, 28], [30, 17, 18], [15, 55, 8], [17, 42, 18]], ![[0, 1], [16, 36, 1], [43, 41, 7], [38, 28, 4], [45, 45, 56], [37, 16, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 22], []]
 b := ![[], [28, 54, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [38, 41, 5, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-854792, -283731, -24426]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14488, -4809, -414]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-116, 20, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-116, 20, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![6, 20, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-116, 20, 1], ![730, 34, 20], ![14600, 3730, 34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -20, 61]], ![![-2, 0, 1], ![10, -6, 20], ![236, 50, 34]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [53, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 60], [0, 1]]
 g := ![![[47, 14], [14], [55, 45], [25, 13], [10, 1]], ![[4, 47], [14], [17, 16], [33, 48], [20, 60]]]
 h' := ![![[10, 60], [37, 21], [13, 40], [17, 44], [19, 47], [0, 1]], ![[0, 1], [3, 40], [47, 21], [30, 17], [1, 14], [10, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [1, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [53, 51, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27845, 7437, 564]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![401, -63, 564]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-20, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-20, 1, 0]] 
 ![![61, 0, 0], ![41, 1, 0], ![27, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-20, 1, 0], ![0, -20, 1], ![730, 150, -20]]]
  hmulB := by decide  
  f := ![![![1201, -60, 0], ![3660, 0, 0]], ![![821, -41, 0], ![2502, 0, 0]], ![![567, -28, 0], ![1728, 1, 0]]]
  g := ![![![1, 0, 0], ![-41, 61, 0], ![-27, 0, 61]], ![![-1, 1, 0], ![13, -20, 1], ![-80, 150, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-116, 20, 1]] ![![61, 0, 0], ![-20, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1220, 61, 0]], ![![-7076, 1220, 61], ![3050, -366, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-20, 1, 0]]], ![![![-116, 20, 1]], ![![50, -6, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-90, -23, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-90, -23, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![44, 44, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-90, -23, 1], ![730, 60, -23], ![-16790, -2720, 60]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -44, 67]], ![![-2, -1, 1], ![26, 16, -23], ![-290, -80, 60]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [4, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 66], [0, 1]]
 g := ![![[60, 17], [37, 25], [19], [65], [47], [1]], ![[0, 50], [0, 42], [19], [65], [47], [1]]]
 h' := ![![[28, 66], [53, 34], [6, 62], [45, 32], [29, 20], [63, 28], [0, 1]], ![[0, 1], [0, 33], [0, 5], [3, 35], [53, 47], [43, 39], [28, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [29, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [4, 39, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4414, -59, 122]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-146, -81, 122]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![23, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![23, 1, 0]] 
 ![![67, 0, 0], ![23, 1, 0], ![7, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![23, 1, 0], ![0, 23, 1], ![730, 150, 23]]]
  hmulB := by decide  
  f := ![![![530, 23, 0], ![-1541, 0, 0]], ![![184, 8, 0], ![-535, 0, 0]], ![![54, 2, 0], ![-157, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 67, 0], ![-7, 0, 67]], ![![0, 1, 0], ![-8, 23, 1], ![-43, 150, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-90, -23, 1]] ![![67, 0, 0], ![23, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![1541, 67, 0]], ![![-6030, -1541, 67], ![-1340, -469, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![23, 1, 0]]], ![![![-90, -23, 1]], ![![-20, -7, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-74, 17, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-74, 17, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![68, 17, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-74, 17, 1], ![730, 76, 17], ![12410, 3280, 76]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-68, -17, 71]], ![![-2, 0, 1], ![-6, -3, 17], ![102, 28, 76]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [64, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 70], [0, 1]]
 g := ![![[21, 10], [24, 54], [27, 5], [40], [25], [1]], ![[0, 61], [10, 17], [52, 66], [40], [25], [1]]]
 h' := ![![[5, 70], [26, 9], [47, 14], [46, 17], [11, 53], [7, 5], [0, 1]], ![[0, 1], [0, 62], [46, 57], [60, 54], [63, 18], [32, 66], [5, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [51, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [64, 66, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2984, 3586, 733]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-660, -125, 733]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-17, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-17, 1, 0]] 
 ![![71, 0, 0], ![54, 1, 0], ![66, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-17, 1, 0], ![0, -17, 1], ![730, 150, -17]]]
  hmulB := by decide  
  f := ![![![919, -54, 0], ![3834, 0, 0]], ![![698, -41, 0], ![2912, 0, 0]], ![![872, -51, 0], ![3638, 1, 0]]]
  g := ![![![1, 0, 0], ![-54, 71, 0], ![-66, 0, 71]], ![![-1, 1, 0], ![12, -17, 1], ![-88, 150, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-74, 17, 1]] ![![71, 0, 0], ![-17, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1207, 71, 0]], ![![-5254, 1207, 71], ![1988, -213, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-17, 1, 0]]], ![![![-74, 17, 1]], ![![28, -3, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![0, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![0, 1, 0]] 
 ![![73, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![0, 1, 0], ![0, 0, 1], ![730, 150, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![0, 1, 0], ![0, 0, 1], ![10, 150, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![2, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![2, 1, 0]] 
 ![![73, 0, 0], ![2, 1, 0], ![69, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![2, 1, 0], ![0, 2, 1], ![730, 150, 2]]]
  hmulB := by decide  
  f := ![![![71, 35, 0], ![-2555, 0, 0]], ![![-2, -1, 0], ![74, 0, 0]], ![![67, 33, 0], ![-2411, 1, 0]]]
  g := ![![![1, 0, 0], ![-2, 73, 0], ![-69, 0, 73]], ![![0, 1, 0], ![-1, 2, 1], ![4, 150, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-2, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-2, 1, 0]] 
 ![![73, 0, 0], ![71, 1, 0], ![69, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-2, 1, 0], ![0, -2, 1], ![730, 150, -2]]]
  hmulB := by decide  
  f := ![![![79, -39, 0], ![2847, 0, 0]], ![![77, -38, 0], ![2775, 0, 0]], ![![75, -37, 0], ![2703, 1, 0]]]
  g := ![![![1, 0, 0], ![-71, 73, 0], ![-69, 0, 73]], ![![-1, 1, 0], ![1, -2, 1], ![-134, 150, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![0, 1, 0]] ![![73, 0, 0], ![2, 1, 0]]
  ![![73, 0, 0], ![-73, 2, 1]] where
 M := ![![![5329, 0, 0], ![146, 73, 0]], ![![0, 73, 0], ![0, 2, 1]]]
 hmul := by decide  
 g := ![![![![73, 0, 0], ![0, 0, 0]], ![![2, 1, 0], ![0, 0, 0]]], ![![![73, -1, -1], ![73, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-73, 2, 1]] ![![73, 0, 0], ![-2, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-146, 73, 0]], ![![-5329, 146, 73], ![876, 73, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-2, 1, 0]]], ![![![-73, 2, 1]], ![![12, 1, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-33, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-33, 1, 0]] 
 ![![79, 0, 0], ![46, 1, 0], ![17, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-33, 1, 0], ![0, -33, 1], ![730, 150, -33]]]
  hmulB := by decide  
  f := ![![![661, -20, 0], ![1580, 0, 0]], ![![430, -13, 0], ![1028, 0, 0]], ![![179, -5, 0], ![428, 1, 0]]]
  g := ![![![1, 0, 0], ![-46, 79, 0], ![-17, 0, 79]], ![![-1, 1, 0], ![19, -33, 1], ![-71, 150, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-31, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-31, 1, 0]] 
 ![![79, 0, 0], ![48, 1, 0], ![66, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-31, 1, 0], ![0, -31, 1], ![730, 150, -31]]]
  hmulB := by decide  
  f := ![![![2016, -65, 0], ![5135, 0, 0]], ![![1210, -39, 0], ![3082, 0, 0]], ![![1656, -53, 0], ![4218, 1, 0]]]
  g := ![![![1, 0, 0], ![-48, 79, 0], ![-66, 0, 79]], ![![-1, 1, 0], ![18, -31, 1], ![-56, 150, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-15, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-15, 1, 0]] 
 ![![79, 0, 0], ![64, 1, 0], ![12, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-15, 1, 0], ![0, -15, 1], ![730, 150, -15]]]
  hmulB := by decide  
  f := ![![![961, -64, 0], ![5056, 0, 0]], ![![796, -53, 0], ![4188, 0, 0]], ![![168, -11, 0], ![884, 1, 0]]]
  g := ![![![1, 0, 0], ![-64, 79, 0], ![-12, 0, 79]], ![![-1, 1, 0], ![12, -15, 1], ![-110, 150, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-33, 1, 0]] ![![79, 0, 0], ![-31, 1, 0]]
  ![![79, 0, 0], ![-83, 15, 1]] where
 M := ![![![6241, 0, 0], ![-2449, 79, 0]], ![![-2607, 79, 0], ![1023, -64, 1]]]
 hmul := by decide  
 g := ![![![![79, 0, 0], ![0, 0, 0]], ![![52, -14, -1], ![79, 0, 0]]], ![![![50, -14, -1], ![79, 0, 0]], ![![14, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-83, 15, 1]] ![![79, 0, 0], ![-15, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-1185, 79, 0]], ![![-6557, 1185, 79], ![1975, -158, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-15, 1, 0]]], ![![![-83, 15, 1]], ![![25, -2, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB267I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB267I1 : PrimesBelowBoundCertificateInterval O 31 79 267 where
  m := 11
  g := ![1, 2, 2, 3, 2, 1, 2, 2, 2, 3, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB267I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1, I73N2]
    · exact ![I79N0, I79N1, I79N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![73, 73, 73]
    · exact ![79, 79, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I41N1, I43N1, I47N0, I47N1, I53N1, I61N1, I67N1, I71N1, I73N0, I73N1, I73N2, I79N0, I79N1, I79N2]
  Il := ![[], [I41N1], [I43N1], [I47N0, I47N0, I47N1], [I53N1], [], [I61N1], [I67N1], [I71N1], [I73N0, I73N1, I73N2], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
