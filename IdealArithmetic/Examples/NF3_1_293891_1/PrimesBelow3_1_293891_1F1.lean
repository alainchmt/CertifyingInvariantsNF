
import IdealArithmetic.Examples.NF3_1_293891_1.RI3_1_293891_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![4, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![4, 1, 0]] 
 ![![37, 0, 0], ![4, 1, 0], ![21, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![4, 1, 0], ![0, 4, 1], ![91, -26, 4]]]
  hmulB := by decide  
  f := ![![![89, 22, 0], ![-814, 0, 0]], ![![4, 1, 0], ![-36, 0, 0]], ![![49, 12, 0], ![-448, 1, 0]]]
  g := ![![![1, 0, 0], ![-4, 37, 0], ![-21, 0, 37]], ![![0, 1, 0], ![-1, 4, 1], ![3, -26, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-8, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-8, 1, 0]] 
 ![![37, 0, 0], ![29, 1, 0], ![10, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-8, 1, 0], ![0, -8, 1], ![91, -26, -8]]]
  hmulB := by decide  
  f := ![![![145, -18, 0], ![666, 0, 0]], ![![121, -15, 0], ![556, 0, 0]], ![![50, -6, 0], ![230, 1, 0]]]
  g := ![![![1, 0, 0], ![-29, 37, 0], ![-10, 0, 37]], ![![-1, 1, 0], ![6, -8, 1], ![25, -26, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![4, 1, 0]] ![![37, 0, 0], ![4, 1, 0]]
  ![![37, 0, 0], ![16, 8, 1]] where
 M := ![![![1369, 0, 0], ![148, 37, 0]], ![![148, 37, 0], ![16, 8, 1]]]
 hmul := by decide  
 g := ![![![![21, -8, -1], ![37, 0, 0]], ![![-12, -7, -1], ![37, 0, 0]]], ![![![-12, -7, -1], ![37, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![16, 8, 1]] ![![37, 0, 0], ![-8, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-296, 37, 0]], ![![592, 296, 37], ![-37, -74, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-8, 1, 0]]], ![![![16, 8, 1]], ![![-1, -2, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![10, 5, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![10, 5, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![10, 5, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![10, 5, 1], ![91, -16, 5], ![455, -39, -16]]]
  hmulB := by decide  
  f := ![![![-9, -5, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -5, 41]], ![![0, 0, 1], ![1, -1, 5], ![15, 1, -16]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [19, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 40], [0, 1]]
 g := ![![[], [], [23], [], [1]], ![[], [], [23], [], [1]]]
 h' := ![![[0, 40], [32], [14], [0, 33], [22], [0, 1]], ![[0, 1], [32], [14], [0, 8], [22], [0, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [0, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [19, 0, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![201, 39, -25]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11, 4, -25]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-5, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-5, 1, 0]] 
 ![![41, 0, 0], ![36, 1, 0], ![16, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-5, 1, 0], ![0, -5, 1], ![91, -26, -5]]]
  hmulB := by decide  
  f := ![![![176, -35, 0], ![1435, 0, 0]], ![![156, -31, 0], ![1272, 0, 0]], ![![76, -15, 0], ![620, 1, 0]]]
  g := ![![![1, 0, 0], ![-36, 41, 0], ![-16, 0, 41]], ![![-1, 1, 0], ![4, -5, 1], ![27, -26, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![10, 5, 1]] ![![41, 0, 0], ![-5, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-205, 41, 0]], ![![410, 205, 41], ![41, -41, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-5, 1, 0]]], ![![![10, 5, 1]], ![![1, -1, 0]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [13, 14, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 38, 21], [28, 4, 22], [0, 1]]
 g := ![![[21, 35, 23], [15, 6, 14], [8, 24], [26, 13, 1], []], ![[12, 4, 28, 35], [35, 30, 15, 36], [], [24, 3, 35, 35], [19, 11]], ![[12, 0, 28, 27], [5, 4, 17, 28], [18, 24], [2, 8, 21, 34], [18, 11]]]
 h' := ![![[28, 38, 21], [20, 36, 25], [18, 17, 10], [6, 26, 14], [0, 0, 1], [0, 1]], ![[28, 4, 22], [5, 10, 39], [16, 34, 10], [39, 28], [21, 42, 4], [28, 38, 21]], ![[0, 1], [29, 40, 22], [17, 35, 23], [6, 32, 29], [34, 1, 38], [28, 4, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 25], []]
 b := ![[], [24, 36, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [13, 14, 30, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![321167, -130161, 6063]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7469, -3027, 141]
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


def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-17, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-17, 1, 0]] 
 ![![47, 0, 0], ![30, 1, 0], ![40, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-17, 1, 0], ![0, -17, 1], ![91, -26, -17]]]
  hmulB := by decide  
  f := ![![![715, -42, 0], ![1974, 0, 0]], ![![460, -27, 0], ![1270, 0, 0]], ![![602, -35, 0], ![1662, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 47, 0], ![-40, 0, 47]], ![![-1, 1, 0], ![10, -17, 1], ![33, -26, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 2, -1]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![2, 2, -1]] 
 ![![47, 0, 0], ![34, 1, 0], ![19, 0, 1]] where
  M :=![![![2, 2, -1], ![-91, 28, 2], ![182, -143, 28]]]
  hmulB := by decide  
  f := ![![![1070, 87, 32]], ![![836, 68, 25]], ![![601, 49, 18]]]
  g := ![![![-1, 2, -1], ![-23, 28, 2], ![96, -143, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-17, 1, 0]] ![![47, 0, 0], ![-17, 1, 0]]
  ![![1070, 87, 32]] where
 M := ![![![2209, 0, 0], ![-799, 47, 0]], ![![-799, 47, 0], ![289, -34, 1]]]
 hmul := by decide  
 g := ![![![![94, 94, -47]], ![![-125, -6, 19]]], ![![![-125, -6, 19]], ![![82, -11, -7]]]]
 hle2 := by decide  
def MulI47N1 : IdealMulLeCertificate' Table 
  ![![1070, 87, 32]] ![![2, 2, -1]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [34, 35, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 18, 41], [5, 34, 12], [0, 1]]
 g := ![![[37, 46, 15], [14, 17], [23, 52, 52], [17, 43], [1]], ![[16, 15, 10, 2], [36, 52], [32, 41, 8, 23], [12, 36], [22, 44, 13, 21]], ![[9, 12, 31, 35], [21, 4], [32, 0, 34, 2], [11, 42], [32, 16, 32, 32]]]
 h' := ![![[14, 18, 41], [11, 47, 42], [13, 49, 32], [48, 5, 23], [19, 18, 19], [0, 1]], ![[5, 34, 12], [19, 6, 16], [17, 30, 23], [22, 1, 33], [35, 50, 6], [14, 18, 41]], ![[0, 1], [27, 0, 48], [23, 27, 51], [25, 47, 50], [44, 38, 28], [5, 34, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 19], []]
 b := ![[], [13, 35, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [34, 35, 34, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-111618, -8162, -4346]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2106, -154, -82]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![27, -1, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![27, -1, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![27, 58, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![27, -1, 1], ![91, 1, -1], ![-91, 117, 1]]]
  hmulB := by decide  
  f := ![![![-26, 1, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -58, 59]], ![![0, -1, 1], ![2, 1, -1], ![-2, 1, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [1, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 58], [0, 1]]
 g := ![![[15, 1], [15, 1], [9], [17, 26], [44, 1]], ![[0, 58], [0, 58], [9], [40, 33], [29, 58]]]
 h' := ![![[44, 58], [44, 58], [44, 58], [42, 3], [15, 47], [0, 1]], ![[0, 1], [0, 1], [0, 1], [56, 56], [18, 12], [44, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [1, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [1, 15, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-529, 992, -284]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![121, 296, -284]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![1, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![1, 1, 0]] 
 ![![59, 0, 0], ![1, 1, 0], ![58, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![1, 1, 0], ![0, 1, 1], ![91, -26, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![59, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 0], ![58, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 59, 0], ![-58, 0, 59]], ![![0, 1, 0], ![-1, 1, 1], ![1, -26, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![27, -1, 1]] ![![59, 0, 0], ![1, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![59, 59, 0]], ![![1593, -59, 59], ![118, 0, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![1, 1, 0]]], ![![![27, -1, 1]], ![![2, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![25, -11, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![25, -11, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![25, 50, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![25, -11, 1], ![91, -1, -11], ![-1001, 377, -1]]]
  hmulB := by decide  
  f := ![![![-24, 11, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -50, 61]], ![![0, -1, 1], ![6, 9, -11], ![-16, 7, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [10, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 60], [0, 1]]
 g := ![![[57, 22], [14], [49, 57], [2, 16], [40, 1]], ![[22, 39], [14], [11, 4], [32, 45], [19, 60]]]
 h' := ![![[40, 60], [47, 49], [59, 21], [41, 39], [27, 4], [0, 1]], ![[0, 1], [55, 12], [45, 40], [15, 22], [4, 57], [40, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [36, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [10, 21, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![192, 18, -46]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![22, 38, -46]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![11, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![11, 1, 0]] 
 ![![61, 0, 0], ![11, 1, 0], ![1, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![11, 1, 0], ![0, 11, 1], ![91, -26, 11]]]
  hmulB := by decide  
  f := ![![![375, 34, 0], ![-2074, 0, 0]], ![![55, 5, 0], ![-304, 0, 0]], ![![-9, -1, 0], ![50, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 61, 0], ![-1, 0, 61]], ![![0, 1, 0], ![-2, 11, 1], ![6, -26, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![25, -11, 1]] ![![61, 0, 0], ![11, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![671, 61, 0]], ![![1525, -671, 61], ![366, -122, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![11, 1, 0]]], ![![![25, -11, 1]], ![![6, -2, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-1, -24, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-1, -24, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![66, 43, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-1, -24, 1], ![91, -27, -24], ![-2184, 715, -27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -43, 67]], ![![-1, -1, 1], ![25, 15, -24], ![-6, 28, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [18, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 66], [0, 1]]
 g := ![![[2, 4], [11, 35], [33], [1], [23], [1]], ![[59, 63], [24, 32], [33], [1], [23], [1]]]
 h' := ![![[31, 66], [3, 2], [31, 54], [42, 10], [44, 66], [49, 31], [0, 1]], ![[0, 1], [65, 65], [30, 13], [17, 57], [13, 1], [5, 36], [31, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [65, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [18, 36, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3513, -175, 373]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-315, -242, 373]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![24, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![24, 1, 0]] 
 ![![67, 0, 0], ![24, 1, 0], ![27, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![24, 1, 0], ![0, 24, 1], ![91, -26, 24]]]
  hmulB := by decide  
  f := ![![![289, 12, 0], ![-804, 0, 0]], ![![72, 3, 0], ![-200, 0, 0]], ![![105, 4, 0], ![-292, 1, 0]]]
  g := ![![![1, 0, 0], ![-24, 67, 0], ![-27, 0, 67]], ![![0, 1, 0], ![-9, 24, 1], ![1, -26, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-1, -24, 1]] ![![67, 0, 0], ![24, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![1608, 67, 0]], ![![-67, -1608, 67], ![67, -603, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![24, 1, 0]]], ![![![-1, -24, 1]], ![![1, -9, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [49, 66, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 35, 3], [57, 35, 68], [0, 1]]
 g := ![![[19, 13, 18], [55, 46, 1], [57, 4, 57], [0, 64], [49, 1], []], ![[35, 46, 12, 12], [45, 53, 62, 4], [19, 11, 38, 54], [44, 8], [48, 18], [12, 9]], ![[45, 44, 24, 70], [1, 53, 30, 23], [45, 64, 57, 55], [53, 43], [12, 18], [18, 9]]]
 h' := ![![[63, 35, 3], [3, 17, 35], [47, 37, 70], [27, 43, 46], [13, 54, 63], [0, 0, 1], [0, 1]], ![[57, 35, 68], [58, 36, 69], [62, 35, 5], [3, 38, 35], [10, 46, 24], [44, 53, 35], [63, 35, 3]], ![[0, 1], [37, 18, 38], [2, 70, 67], [32, 61, 61], [59, 42, 55], [24, 18, 35], [57, 35, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 56], []]
 b := ![[], [7, 23, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [49, 66, 22, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-37488, 12425, 497]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-528, 175, 7]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-298, -24, -9]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-298, -24, -9]] 
 ![![73, 0, 0], ![0, 73, 0], ![25, 27, 1]] where
  M :=![![![-298, -24, -9], ![-819, -64, -24], ![-2184, -195, -64]]]
  hmulB := by decide  
  f := ![![![8, -3, 0]], ![![0, 8, -3]], ![![-1, 3, -1]]]
  g := ![![![-1, 3, -9], ![-3, 8, -24], ![-8, 21, -64]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [7, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 72], [0, 1]]
 g := ![![[8, 35], [46], [46], [62, 9], [70], [1]], ![[19, 38], [46], [46], [69, 64], [70], [1]]]
 h' := ![![[17, 72], [20, 20], [59, 22], [4, 51], [70, 3], [66, 17], [0, 1]], ![[0, 1], [68, 53], [68, 51], [68, 22], [48, 70], [63, 56], [17, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [23, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [7, 56, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![371, 316, 9]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2, 1, 9]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, 3, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-8, 3, 0]] 
 ![![73, 0, 0], ![46, 1, 0], ![1, 0, 1]] where
  M :=![![![-8, 3, 0], ![0, -8, 3], ![273, -78, -8]]]
  hmulB := by decide  
  f := ![![![298, 24, 9]], ![![199, 16, 6]], ![![34, 3, 1]]]
  g := ![![![-2, 3, 0], ![5, -8, 3], ![53, -78, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-298, -24, -9]] ![![-8, 3, 0]]
  ![![73, 0, 0]] where
 M := ![![![-73, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![31, -20, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![31, -20, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![31, 59, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![31, -20, 1], ![91, 5, -20], ![-1820, 611, 5]]]
  hmulB := by decide  
  f := ![![![-30, 20, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -59, 79]], ![![0, -1, 1], ![9, 15, -20], ![-25, 4, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [3, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 78], [0, 1]]
 g := ![![[77, 40], [32, 5], [54, 76], [49, 10], [36], [1]], ![[1, 39], [62, 74], [36, 3], [30, 69], [36], [1]]]
 h' := ![![[6, 78], [62, 35], [75, 59], [11, 32], [59, 22], [76, 6], [0, 1]], ![[0, 1], [35, 44], [34, 20], [45, 47], [33, 57], [33, 73], [6, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [20, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [3, 73, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3487, 634, 150]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-103, -104, 150]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![20, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![20, 1, 0]] 
 ![![79, 0, 0], ![20, 1, 0], ![74, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![20, 1, 0], ![0, 20, 1], ![91, -26, 20]]]
  hmulB := by decide  
  f := ![![![41, 2, 0], ![-158, 0, 0]], ![![-20, -1, 0], ![80, 0, 0]], ![![46, 2, 0], ![-178, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 79, 0], ![-74, 0, 79]], ![![0, 1, 0], ![-6, 20, 1], ![-11, -26, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![31, -20, 1]] ![![79, 0, 0], ![20, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![1580, 79, 0]], ![![2449, -1580, 79], ![711, -395, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![20, 1, 0]]], ![![![31, -20, 1]], ![![9, -5, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB154I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB154I1 : PrimesBelowBoundCertificateInterval O 31 79 154 where
  m := 11
  g := ![3, 2, 1, 3, 1, 2, 2, 2, 1, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB154I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
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
    · exact ![37, 37, 37]
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![47, 47, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![357911]
    · exact ![5329, 73]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
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
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N0, I37N1, I41N1, I47N0, I47N1, I59N1, I61N1, I67N1, I73N1, I79N1]
  Il := ![[I37N0, I37N0, I37N1], [I41N1], [], [I47N0, I47N0, I47N1], [], [I59N1], [I61N1], [I67N1], [], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
