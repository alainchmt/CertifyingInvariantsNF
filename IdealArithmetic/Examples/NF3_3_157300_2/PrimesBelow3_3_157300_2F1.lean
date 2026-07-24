
import IdealArithmetic.Examples.NF3_3_157300_2.RI3_3_157300_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-32, -7, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-32, -7, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![5, 30, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-32, -7, 1], ![11, -8, -20], ![-112, -154, -15]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -30, 37]], ![![-1, -1, 1], ![3, 16, -20], ![-1, 8, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [23, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 36], [0, 1]]
 g := ![![[6, 11], [11], [28, 3], [26], [1]], ![[5, 26], [11], [21, 34], [26], [1]]]
 h' := ![![[10, 36], [9, 23], [22, 14], [5, 22], [14, 10], [0, 1]], ![[0, 1], [17, 14], [14, 23], [3, 15], [3, 27], [10, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [29, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [23, 27, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![232, 245, 150]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14, -115, 150]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-17, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-17, 1, 0]] 
 ![![37, 0, 0], ![20, 1, 0], ![15, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-17, 1, 0], ![1, -17, 3], ![18, 24, -16]]]
  hmulB := by decide  
  f := ![![![-170, 4635, -819], ![222, 10101, 0]], ![![-95, 2496, -441], ![112, 5439, 0]], ![![-68, 1879, -332], ![92, 4095, 0]]]
  g := ![![![1, 0, 0], ![-20, 37, 0], ![-15, 0, 37]], ![![-1, 1, 0], ![8, -17, 3], ![-6, 24, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-32, -7, 1]] ![![37, 0, 0], ![-17, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-629, 37, 0]], ![![-1184, -259, 37], ![555, 111, -37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-17, 1, 0]]], ![![![-32, -7, 1]], ![![15, 3, -1]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-4, -8, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-4, -8, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![37, 33, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-4, -8, 1], ![10, 20, -23], ![-130, -178, 12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -33, 41]], ![![-1, -1, 1], ![21, 19, -23], ![-14, -14, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [27, 38, 1] where
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
 g := ![![[9, 4], [39], [1], [29, 9], [1]], ![[21, 37], [39], [1], [15, 32], [1]]]
 h' := ![![[3, 40], [11, 39], [30, 11], [37, 40], [14, 3], [0, 1]], ![[0, 1], [5, 2], [22, 30], [34, 1], [23, 38], [3, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [36, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [27, 38, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![293, -70, 1454]
  a := ![2, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1305, -1172, 1454]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-18, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-18, 1, 0]] 
 ![![41, 0, 0], ![23, 1, 0], ![29, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-18, 1, 0], ![1, -18, 3], ![18, 24, -17]]]
  hmulB := by decide  
  f := ![![![357, -8992, 1500], ![-328, -20500, 0]], ![![191, -5035, 840], ![-204, -11480, 0]], ![![249, -6360, 1061], ![-240, -14500, 0]]]
  g := ![![![1, 0, 0], ![-23, 41, 0], ![-29, 0, 41]], ![![-1, 1, 0], ![8, -18, 3], ![-1, 24, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-4, -8, 1]] ![![41, 0, 0], ![-18, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-738, 41, 0]], ![![-164, -328, 41], ![82, 164, -41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-18, 1, 0]]], ![![![-4, -8, 1]], ![![2, 4, -1]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [24, 38, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 31, 20], [34, 11, 23], [0, 1]]
 g := ![![[35, 1, 40], [27, 3, 14], [42, 4], [40, 11, 1], []], ![[29, 14, 16, 18], [42, 30, 8, 37], [7, 15], [31, 21, 11, 12], [7, 13]], ![[20, 41, 8, 17], [16, 11, 15, 1], [37, 24], [11, 3, 14, 1], [4, 13]]]
 h' := ![![[20, 31, 20], [40, 2, 30], [5, 14, 33], [29, 22, 41], [0, 0, 1], [0, 1]], ![[34, 11, 23], [31, 13, 26], [29, 6, 41], [5, 3, 31], [17, 17, 11], [20, 31, 20]], ![[0, 1], [2, 28, 30], [29, 23, 12], [33, 18, 14], [28, 26, 31], [34, 11, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 7], []]
 b := ![[], [1, 14, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [24, 38, 32, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1337467270, -1518486520, -1422689830]
  a := ![-65, 1, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-31103890, -35313640, -33085810]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-3, 12, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-3, 12, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![44, 12, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-3, 12, 1], ![30, 21, 37], ![230, 302, 33]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -12, 47]], ![![-1, 0, 1], ![-34, -9, 37], ![-26, -2, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [22, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 46], [0, 1]]
 g := ![![[13, 28], [2, 34], [26, 28], [18, 16], [1]], ![[42, 19], [7, 13], [8, 19], [1, 31], [1]]]
 h' := ![![[43, 46], [3, 13], [39, 9], [27, 13], [25, 43], [0, 1]], ![[0, 1], [45, 34], [3, 38], [22, 34], [41, 4], [43, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [34, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [22, 4, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![453, 350, 1165]
  a := ![-2, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1081, -290, 1165]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![10, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![10, 1, 0]] 
 ![![47, 0, 0], ![10, 1, 0], ![14, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![10, 1, 0], ![1, 10, 3], ![18, 24, 11]]]
  hmulB := by decide  
  f := ![![![-1364, -14838, -4455], ![-564, 69795, 0]], ![![-295, -3148, -945], ![-93, 14805, 0]], ![![-408, -4420, -1327], ![-160, 20790, 0]]]
  g := ![![![1, 0, 0], ![-10, 47, 0], ![-14, 0, 47]], ![![0, 1, 0], ![-3, 10, 3], ![-8, 24, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-3, 12, 1]] ![![47, 0, 0], ![10, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![470, 47, 0]], ![![-141, 564, 47], ![0, 141, 47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![10, 1, 0]]], ![![![-3, 12, 1]], ![![0, 3, 1]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![0, 1, 0]] 
 ![![53, 0, 0], ![0, 1, 0], ![18, 0, 1]] where
  M :=![![![0, 1, 0], ![1, 0, 3], ![18, 24, 1]]]
  hmulB := by decide  
  f := ![![![-72, -1, 3]], ![![1, 0, 0]], ![![-24, 0, 1]]]
  g := ![![![0, 1, 0], ![-1, 0, 3], ![0, 24, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![4, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![4, 1, 0]] 
 ![![53, 0, 0], ![4, 1, 0], ![48, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![4, 1, 0], ![1, 4, 3], ![18, 24, 5]]]
  hmulB := by decide  
  f := ![![![-1107, -4477, -3360], ![-159, 59360, 0]], ![![-84, -336, -252], ![1, 4452, 0]], ![![-1004, -4055, -3043], ![-125, 53760, 0]]]
  g := ![![![1, 0, 0], ![-4, 53, 0], ![-48, 0, 53]], ![![0, 1, 0], ![-3, 4, 3], ![-6, 24, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-5, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-5, 1, 0]] 
 ![![53, 0, 0], ![48, 1, 0], ![45, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-5, 1, 0], ![1, -5, 3], ![18, 24, -4]]]
  hmulB := by decide  
  f := ![![![-1050, 5351, -3213], ![212, 56763, 0]], ![![-948, 4841, -2907], ![213, 51357, 0]], ![![-890, 4543, -2728], ![196, 48195, 0]]]
  g := ![![![1, 0, 0], ![-48, 53, 0], ![-45, 0, 53]], ![![-1, 1, 0], ![2, -5, 3], ![-18, 24, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![0, 1, 0]] ![![53, 0, 0], ![4, 1, 0]]
  ![![53, 0, 0], ![-35, 19, 1]] where
 M := ![![![0, 53, 0], ![1, 4, 3]]]
 hmul := by decide  
 g := ![![![![0, 1, 0], ![0, 0, 0]], ![![2, -1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-35, 19, 1]] ![![53, 0, 0], ![-5, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-265, 53, 0]], ![![-1855, 1007, 53], ![212, -106, 53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-5, 1, 0]]], ![![![-35, 19, 1]], ![![4, -2, 1]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-7, 23, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-7, 23, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![52, 23, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-7, 23, 1], ![41, 17, 70], ![428, 566, 40]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -23, 59]], ![![-1, 0, 1], ![-61, -27, 70], ![-28, -6, 40]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [33, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 58], [0, 1]]
 g := ![![[13, 15], [12, 1], [19], [29, 51], [43, 1]], ![[9, 44], [55, 58], [19], [39, 8], [27, 58]]]
 h' := ![![[43, 58], [17, 30], [14, 1], [46, 45], [56, 46], [0, 1]], ![[0, 1], [9, 29], [57, 58], [34, 14], [28, 13], [43, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [17, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [33, 16, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![253, 256, 183]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-157, -67, 183]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-11, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-11, 1, 0]] 
 ![![59, 0, 0], ![48, 1, 0], ![19, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-11, 1, 0], ![1, -11, 3], ![18, 24, -10]]]
  hmulB := by decide  
  f := ![![![-515, 6156, -1680], ![236, 33040, 0]], ![![-421, 5002, -1365], ![178, 26845, 0]], ![![-161, 1982, -541], ![102, 10640, 0]]]
  g := ![![![1, 0, 0], ![-48, 59, 0], ![-19, 0, 59]], ![![-1, 1, 0], ![8, -11, 3], ![-16, 24, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-7, 23, 1]] ![![59, 0, 0], ![-11, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-649, 59, 0]], ![![-413, 1357, 59], ![118, -236, 59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-11, 1, 0]]], ![![![-7, 23, 1]], ![![2, -4, 1]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [29, 17, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 42, 37], [41, 18, 24], [0, 1]]
 g := ![![[7, 44, 36], [31, 27], [17, 14, 15], [17, 7, 14], [1]], ![[0, 30, 60, 44], [44, 48], [17, 15, 35, 43], [4, 4, 11, 44], [8, 24, 42, 23]], ![[10, 33, 30, 30], [21, 3], [56, 34, 52, 54], [3, 15, 34, 7], [37, 57, 60, 38]]]
 h' := ![![[41, 42, 37], [41, 22, 6], [56, 1, 37], [56, 44, 25], [32, 44, 21], [0, 1]], ![[41, 18, 24], [1, 49, 7], [22, 4, 32], [9, 22, 4], [3, 36, 54], [41, 42, 37]], ![[0, 1], [57, 51, 48], [42, 56, 53], [39, 56, 32], [16, 42, 47], [41, 18, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 60], []]
 b := ![[], [48, 17, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [29, 17, 40, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1497123, 1882338, 672525]
  a := ![2, 19, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![24543, 30858, 11025]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-6, -33, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-6, -33, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![61, 34, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-6, -33, 1], ![-15, 18, -98], ![-580, -778, -15]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-61, -34, 67]], ![![-1, -1, 1], ![89, 50, -98], ![5, -4, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [60, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 66], [0, 1]]
 g := ![![[16, 19], [24, 62], [14], [19], [15], [1]], ![[0, 48], [0, 5], [14], [19], [15], [1]]]
 h' := ![![[45, 66], [34, 32], [40, 14], [64, 58], [20, 32], [7, 45], [0, 1]], ![[0, 1], [0, 35], [0, 53], [61, 9], [53, 35], [22, 22], [45, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [40, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [60, 22, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-161, -316, 507]
  a := ![-2, 3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-464, -262, 507]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![31, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![31, 1, 0]] 
 ![![67, 0, 0], ![31, 1, 0], ![15, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![31, 1, 0], ![1, 31, 3], ![18, 24, 32]]]
  hmulB := by decide  
  f := ![![![317, 16516, 1599], ![469, -35711, 0]], ![![153, 7623, 738], ![202, -16482, 0]], ![![52, 3697, 358], ![146, -7995, 0]]]
  g := ![![![1, 0, 0], ![-31, 67, 0], ![-15, 0, 67]], ![![0, 1, 0], ![-15, 31, 3], ![-18, 24, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-6, -33, 1]] ![![67, 0, 0], ![31, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![2077, 67, 0]], ![![-402, -2211, 67], ![-201, -1005, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![31, 1, 0]]], ![![![-6, -33, 1]], ![![-3, -15, -1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-1, 13, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-1, 13, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![70, 13, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-1, 13, 1], ![31, 23, 40], ![248, 326, 36]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-70, -13, 71]], ![![-1, 0, 1], ![-39, -7, 40], ![-32, -2, 36]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [17, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 70], [0, 1]]
 g := ![![[2, 40], [11, 9], [31, 1], [15], [20], [1]], ![[62, 31], [60, 62], [68, 70], [15], [20], [1]]]
 h' := ![![[37, 70], [26, 18], [41, 3], [3, 70], [20, 50], [54, 37], [0, 1]], ![[0, 1], [53, 53], [10, 68], [37, 1], [24, 21], [3, 34], [37, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [51, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [17, 34, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![810, 830, 1107]
  a := ![2, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1080, -191, 1107]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![31, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![31, 1, 0]] 
 ![![71, 0, 0], ![31, 1, 0], ![35, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![31, 1, 0], ![1, 31, 3], ![18, 24, 32]]]
  hmulB := by decide  
  f := ![![![-133, -5114, -495], ![-71, 11715, 0]], ![![-72, -2232, -216], ![1, 5112, 0]], ![![-66, -2521, -244], ![-34, 5775, 0]]]
  g := ![![![1, 0, 0], ![-31, 71, 0], ![-35, 0, 71]], ![![0, 1, 0], ![-15, 31, 3], ![-26, 24, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-1, 13, 1]] ![![71, 0, 0], ![31, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![2201, 71, 0]], ![![-71, 923, 71], ![0, 426, 71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![31, 1, 0]]], ![![![-1, 13, 1]], ![![0, 6, 1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-27, -5, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-27, -5, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![46, 68, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-27, -5, 1], ![13, -3, -14], ![-76, -106, -8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-46, -68, 73]], ![![-1, -1, 1], ![9, 13, -14], ![4, 6, -8]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [6, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 72], [0, 1]]
 g := ![![[22, 61], [24], [36], [50, 3], [50], [1]], ![[0, 12], [24], [36], [19, 70], [50], [1]]]
 h' := ![![[14, 72], [38, 39], [67, 43], [65, 6], [28, 21], [67, 14], [0, 1]], ![[0, 1], [0, 34], [12, 30], [3, 67], [30, 52], [44, 59], [14, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [23, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [6, 59, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1136, 1400, 1910]
  a := ![-5, 0, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1188, -1760, 1910]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![14, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![14, 1, 0]] 
 ![![73, 0, 0], ![14, 1, 0], ![8, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![14, 1, 0], ![1, 14, 3], ![18, 24, 15]]]
  hmulB := by decide  
  f := ![![![-1358, -20391, -4371], ![-511, 106361, 0]], ![![-265, -3905, -837], ![-72, 20367, 0]], ![![-154, -2235, -479], ![-29, 11656, 0]]]
  g := ![![![1, 0, 0], ![-14, 73, 0], ![-8, 0, 73]], ![![0, 1, 0], ![-3, 14, 3], ![-6, 24, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-27, -5, 1]] ![![73, 0, 0], ![14, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![1022, 73, 0]], ![![-1971, -365, 73], ![-365, -73, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![14, 1, 0]]], ![![![-27, -5, 1]], ![![-5, -1, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [48, 16, 71, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 45, 63], [60, 33, 16], [0, 1]]
 g := ![![[34, 22, 65], [20, 10, 13], [5, 4, 9], [30, 35, 13], [8, 1], []], ![[23, 11, 35, 37], [51, 21, 47, 35], [25, 43, 25, 37], [59, 45, 16, 27], [23, 62], [55, 19]], ![[10, 55, 28, 26], [50, 70, 59, 45], [7, 62, 70, 1], [38, 32, 20, 52], [18, 50], [23, 19]]]
 h' := ![![[27, 45, 63], [67, 78, 12], [76, 52, 31], [61, 15, 3], [11, 61, 48], [0, 0, 1], [0, 1]], ![[60, 33, 16], [18, 27, 17], [67, 77, 33], [26, 61, 17], [69, 31, 55], [64, 6, 33], [27, 45, 63]], ![[0, 1], [18, 53, 50], [71, 29, 15], [75, 3, 59], [2, 66, 55], [47, 73, 45], [60, 33, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 39], []]
 b := ![[], [66, 7, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [48, 16, 71, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-850988, -1333520, 835820]
  a := ![4, -10, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10772, -16880, 10580]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB89I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB89I1 : PrimesBelowBoundCertificateInterval O 31 79 89 where
  m := 11
  g := ![2, 2, 1, 2, 3, 2, 1, 2, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB89I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
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
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I41N1, I47N1, I53N0, I53N1, I53N2, I59N1, I67N1, I71N1, I73N1]
  Il := ![[I37N1], [I41N1], [], [I47N1], [I53N0, I53N1, I53N2], [I59N1], [], [I67N1], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
