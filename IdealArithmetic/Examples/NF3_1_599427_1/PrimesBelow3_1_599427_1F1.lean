
import IdealArithmetic.Examples.NF3_1_599427_1.RI3_1_599427_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![11, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![11, 1, 0]] 
 ![![37, 0, 0], ![11, 1, 0], ![27, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![11, 1, 0], ![0, 11, 1], ![149, 0, 11]]]
  hmulB := by decide  
  f := ![![![166, 15, 0], ![-555, 0, 0]], ![![44, 4, 0], ![-147, 0, 0]], ![![114, 10, 0], ![-381, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 37, 0], ![-27, 0, 37]], ![![0, 1, 0], ![-4, 11, 1], ![-4, 0, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-10, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-10, 1, 0]] 
 ![![37, 0, 0], ![27, 1, 0], ![11, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-10, 1, 0], ![0, -10, 1], ![149, 0, -10]]]
  hmulB := by decide  
  f := ![![![301, -30, 0], ![1110, 0, 0]], ![![231, -23, 0], ![852, 0, 0]], ![![103, -10, 0], ![380, 1, 0]]]
  g := ![![![1, 0, 0], ![-27, 37, 0], ![-11, 0, 37]], ![![-1, 1, 0], ![7, -10, 1], ![7, 0, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, 4, -2]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![35, 4, -2]] 
 ![![37, 0, 0], ![36, 1, 0], ![36, 0, 1]] where
  M :=![![![35, 4, -2], ![-298, 35, 4], ![596, -298, 35]]]
  hmulB := by decide  
  f := ![![![-2417, -456, -86]], ![![-2698, -509, -96]], ![![-4188, -790, -149]]]
  g := ![![![-1, 4, -2], ![-46, 35, 4], ![272, -298, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![11, 1, 0]] ![![37, 0, 0], ![-10, 1, 0]]
  ![![-2417, -456, -86]] where
 M := ![![![1369, 0, 0], ![-370, 37, 0]], ![![407, 37, 0], ![-110, 1, 1]]]
 hmul := by decide  
 g := ![![![![1295, 148, -74]], ![![-648, -5, 24]]], ![![![87, 79, -18]], ![![-96, -19, 7]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-2417, -456, -86]] ![![35, 4, -2]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18524499012838, 3494226464944, 659106547489]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![18524499012838, 3494226464944, 659106547489]] 
 ![![41, 0, 0], ![0, 41, 0], ![8, 34, 1]] where
  M :=![![![18524499012838, 3494226464944, 659106547489], ![98206875575861, 18524499012838, 3494226464944], ![520639743276656, 98206875575861, 18524499012838]]]
  hmulB := by decide  
  f := ![![![3895060, 136877, -164406]], ![![-24496494, 3895060, 136877]], ![![-19056723, 2659282, 176430]]]
  g := ![![![323210893486, -461351125602, 659106547489], ![1713489362349, -2445834165738, 3494226464944], ![9083993931072, -12966490020991, 18524499012838]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [5, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 40], [0, 1]]
 g := ![![[8, 33], [16], [39], [32, 1], [1]], ![[0, 8], [16], [39], [33, 40], [1]]]
 h' := ![![[1, 40], [22, 19], [26, 4], [4, 11], [36, 1], [0, 1]], ![[0, 1], [0, 22], [30, 37], [15, 30], [37, 40], [1, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [28, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [5, 40, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![303, 109, -39]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15, 35, -39]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3895060, -136877, 164406]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-3895060, -136877, 164406]] 
 ![![41, 0, 0], ![7, 1, 0], ![33, 0, 1]] where
  M :=![![![-3895060, -136877, 164406], ![24496494, -3895060, -136877], ![-20394673, 24496494, -3895060]]]
  hmulB := by decide  
  f := ![![![-18524499012838, -3494226464944, -659106547489]], ![![-5558008991847, -1048392299206, -197755421887]], ![![-27608492943910, -5207715827293, -982317440975]]]
  g := ![![![-203959, -136877, 164406], ![1372655, -3895060, -136877], ![-1544711, 24496494, -3895060]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![18524499012838, 3494226464944, 659106547489]] ![![-3895060, -136877, 164406]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [41, 19, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 13, 32], [34, 29, 11], [0, 1]]
 g := ![![[3, 16, 11], [26, 41, 17], [2, 9], [33, 40, 1], []], ![[23, 20, 29, 33], [8, 40, 31, 7], [40, 4], [38, 14, 36, 37], [39, 35]], ![[42, 28, 8, 16], [7, 36, 31, 23], [38, 1], [23, 40, 27, 10], [17, 35]]]
 h' := ![![[6, 13, 32], [9, 6, 22], [17, 16, 19], [23, 12, 3], [0, 0, 1], [0, 1]], ![[34, 29, 11], [16, 14, 13], [0, 12, 31], [7, 30, 41], [28, 1, 29], [6, 13, 32]], ![[0, 1], [34, 23, 8], [37, 15, 36], [2, 1, 42], [29, 42, 13], [34, 29, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 39], []]
 b := ![[], [6, 28, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [41, 19, 3, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![598259, 5332, -7998]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![13913, 124, -186]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-93857091630, -17704010957, -3339460008]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-93857091630, -17704010957, -3339460008]] 
 ![![47, 0, 0], ![0, 47, 0], ![4, 2, 1]] where
  M :=![![![-93857091630, -17704010957, -3339460008], ![-497579541192, -93857091630, -17704010957], ![-2637897632593, -497579541192, -93857091630]]]
  hmulB := by decide  
  f := ![![![-323748, 7242, 10153]], ![![1512797, -323748, 7242]], ![![59780, 19027, -5716]]]
  g := ![![![-1712750034, -234576403, -3339460008], ![-9080074412, -1243597228, -17704010957], ![-48137643959, -6592879956, -93857091630]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [1, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 46], [0, 1]]
 g := ![![[32, 1], [32, 1], [15, 6], [8, 37], [1]], ![[0, 46], [0, 46], [11, 41], [46, 10], [1]]]
 h' := ![![[15, 46], [15, 46], [32, 1], [39, 37], [46, 15], [0, 1]], ![[0, 1], [0, 1], [0, 46], [30, 10], [36, 32], [15, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [9, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [1, 32, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1751, 53, 97]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29, -3, 97]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![323748, -7242, -10153]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![323748, -7242, -10153]] 
 ![![47, 0, 0], ![45, 1, 0], ![43, 0, 1]] where
  M :=![![![323748, -7242, -10153], ![-1512797, 323748, -7242], ![-1079058, -1512797, 323748]]]
  hmulB := by decide  
  f := ![![![93857091630, 17704010957, 3339460008]], ![![100449971586, 18947608185, 3574036411]], ![![141994735589, 26784085369, 5052210042]]]
  g := ![![![23111, -7242, -10153], ![-335533, 323748, -7242], ![1129269, -1512797, 323748]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-93857091630, -17704010957, -3339460008]] ![![323748, -7242, -10153]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-11, 25, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-11, 25, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![42, 25, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-11, 25, 1], ![149, -11, 25], ![3725, 149, -11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -25, 53]], ![![-1, 0, 1], ![-17, -12, 25], ![79, 8, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [37, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 52], [0, 1]]
 g := ![![[23, 43], [37], [5, 6], [42], [50, 1]], ![[0, 10], [37], [40, 47], [42], [47, 52]]]
 h' := ![![[50, 52], [49, 34], [27, 39], [8, 18], [5, 25], [0, 1]], ![[0, 1], [0, 19], [16, 14], [7, 35], [36, 28], [50, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [29, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [37, 3, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-853, 1346, -14]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5, 32, -14]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-25, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-25, 1, 0]] 
 ![![53, 0, 0], ![28, 1, 0], ![11, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-25, 1, 0], ![0, -25, 1], ![149, 0, -25]]]
  hmulB := by decide  
  f := ![![![676, -27, 0], ![1431, 0, 0]], ![![376, -15, 0], ![796, 0, 0]], ![![162, -6, 0], ![343, 1, 0]]]
  g := ![![![1, 0, 0], ![-28, 53, 0], ![-11, 0, 53]], ![![-1, 1, 0], ![13, -25, 1], ![8, 0, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-11, 25, 1]] ![![53, 0, 0], ![-25, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-1325, 53, 0]], ![![-583, 1325, 53], ![424, -636, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-25, 1, 0]]], ![![![-11, 25, 1]], ![![8, -12, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![12, -22, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![12, -22, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![12, 37, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![12, -22, 1], ![149, 12, -22], ![-3278, 149, 12]]]
  hmulB := by decide  
  f := ![![![-11, 22, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -37, 59]], ![![0, -1, 1], ![7, 14, -22], ![-58, -5, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [7, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 58], [0, 1]]
 g := ![![[52, 17], [40, 4], [27], [44, 35], [49, 1]], ![[0, 42], [0, 55], [27], [48, 24], [39, 58]]]
 h' := ![![[49, 58], [15, 31], [39, 57], [46, 26], [11, 34], [0, 1]], ![[0, 1], [0, 28], [0, 2], [22, 33], [25, 25], [49, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [31, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [7, 10, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![305, 139, -9]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7, 8, -9]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![22, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![22, 1, 0]] 
 ![![59, 0, 0], ![22, 1, 0], ![47, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![22, 1, 0], ![0, 22, 1], ![149, 0, 22]]]
  hmulB := by decide  
  f := ![![![463, 21, 0], ![-1239, 0, 0]], ![![154, 7, 0], ![-412, 0, 0]], ![![383, 17, 0], ![-1025, 1, 0]]]
  g := ![![![1, 0, 0], ![-22, 59, 0], ![-47, 0, 59]], ![![0, 1, 0], ![-9, 22, 1], ![-15, 0, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![12, -22, 1]] ![![59, 0, 0], ![22, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![1298, 59, 0]], ![![708, -1298, 59], ![413, -472, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![22, 1, 0]]], ![![![12, -22, 1]], ![![7, -8, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![22, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![22, 1, 0]] 
 ![![61, 0, 0], ![22, 1, 0], ![4, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![22, 1, 0], ![0, 22, 1], ![149, 0, 22]]]
  hmulB := by decide  
  f := ![![![375, 17, 0], ![-1037, 0, 0]], ![![110, 5, 0], ![-304, 0, 0]], ![![8, 0, 0], ![-22, 1, 0]]]
  g := ![![![1, 0, 0], ![-22, 61, 0], ![-4, 0, 61]], ![![0, 1, 0], ![-8, 22, 1], ![1, 0, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-19, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-19, 1, 0]] 
 ![![61, 0, 0], ![42, 1, 0], ![5, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-19, 1, 0], ![0, -19, 1], ![149, 0, -19]]]
  hmulB := by decide  
  f := ![![![1008, -53, 0], ![3233, 0, 0]], ![![704, -37, 0], ![2258, 0, 0]], ![![82, -4, 0], ![263, 1, 0]]]
  g := ![![![1, 0, 0], ![-42, 61, 0], ![-5, 0, 61]], ![![-1, 1, 0], ![13, -19, 1], ![4, 0, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-42432047882154, -8003843157585, -1509743424808]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-42432047882154, -8003843157585, -1509743424808]] 
 ![![61, 0, 0], ![58, 1, 0], ![52, 0, 1]] where
  M :=![![![-42432047882154, -8003843157585, -1509743424808], ![-224951770296392, -42432047882154, -8003843157585], ![-1192572630480165, -224951770296392, -42432047882154]]]
  hmulB := by decide  
  f := ![![![-58746396, 5545354, 1044207]], ![![-53306625, 4309576, 1083760]], ![![-36533686, 7277791, -72912]]]
  g := ![![![8201598579472, -8003843157585, -1509743424808], ![43480440181360, -42432047882154, -8003843157585], ![230509779288239, -224951770296392, -42432047882154]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![22, 1, 0]] ![![61, 0, 0], ![-19, 1, 0]]
  ![![-58746396, 5545354, 1044207]] where
 M := ![![![3721, 0, 0], ![-1159, 61, 0]], ![![1342, 61, 0], ![-418, 3, 1]]]
 hmul := by decide  
 g := ![![![![-2588354920811394, -488234432612685, -92094348913288]], ![![581257139464534, 109640972111961, 20681281913767]]], ![![![-1158456823703780, -218516597349024, -41218198503361]], ![![260150296284771, 49071451244716, 9256215970735]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![-58746396, 5545354, 1044207]] ![![-42432047882154, -8003843157585, -1509743424808]]
  ![![61, 0, 0]] where
 M := ![![![61, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![27, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![27, 1, 0]] 
 ![![67, 0, 0], ![27, 1, 0], ![8, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![27, 1, 0], ![0, 27, 1], ![149, 0, 27]]]
  hmulB := by decide  
  f := ![![![82, 3, 0], ![-201, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-16, -1, 0], ![40, 1, 0]]]
  g := ![![![1, 0, 0], ![-27, 67, 0], ![-8, 0, 67]], ![![0, 1, 0], ![-11, 27, 1], ![-1, 0, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-21, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-21, 1, 0]] 
 ![![67, 0, 0], ![46, 1, 0], ![28, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-21, 1, 0], ![0, -21, 1], ![149, 0, -21]]]
  hmulB := by decide  
  f := ![![![505, -24, 0], ![1608, 0, 0]], ![![358, -17, 0], ![1140, 0, 0]], ![![238, -11, 0], ![758, 1, 0]]]
  g := ![![![1, 0, 0], ![-46, 67, 0], ![-28, 0, 67]], ![![-1, 1, 0], ![14, -21, 1], ![11, 0, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![-6, 1, 0]] 
 ![![67, 0, 0], ![61, 1, 0], ![31, 0, 1]] where
  M :=![![![-6, 1, 0], ![0, -6, 1], ![149, 0, -6]]]
  hmulB := by decide  
  f := ![![![-36, -6, -1]], ![![-35, -6, -1]], ![![-30, -5, -1]]]
  g := ![![![-1, 1, 0], ![5, -6, 1], ![5, 0, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![27, 1, 0]] ![![67, 0, 0], ![-21, 1, 0]]
  ![![36, 6, 1]] where
 M := ![![![4489, 0, 0], ![-1407, 67, 0]], ![![1809, 67, 0], ![-567, 6, 1]]]
 hmul := by decide  
 g := ![![![![402, -67, 0]], ![![-126, 27, -1]]], ![![![162, -21, -1]], ![![-53, 9, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![36, 6, 1]] ![![-6, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![-67, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-50324843360, -9492639957, -1790571164]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-50324843360, -9492639957, -1790571164]] 
 ![![71, 0, 0], ![0, 71, 0], ![16, 67, 1]] where
  M :=![![![-50324843360, -9492639957, -1790571164], ![-266795103436, -50324843360, -9492639957], ![-1414403353593, -266795103436, -50324843360]]]
  hmulB := by decide  
  f := ![![![-204188, 45296, -1279]], ![![-190571, -204188, 45296]], ![![-130791, -185161, 39580]]]
  g := ![![![-305291616, 1555994761, -1790571164], ![-1618491044, 8249042729, -9492639957], ![-8580364223, 43731963404, -50324843360]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [67, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 70], [0, 1]]
 g := ![![[51, 4], [1, 6], [41, 40], [45], [10], [1]], ![[15, 67], [18, 65], [36, 31], [45], [10], [1]]]
 h' := ![![[62, 70], [4, 2], [22, 19], [50, 53], [56, 51], [4, 62], [0, 1]], ![[0, 1], [57, 69], [64, 52], [70, 18], [23, 20], [14, 9], [62, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [57, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [67, 9, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5739, 358, 372]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, -346, 372]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![204188, -45296, 1279]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![204188, -45296, 1279]] 
 ![![71, 0, 0], ![4, 1, 0], ![55, 0, 1]] where
  M :=![![![204188, -45296, 1279], ![190571, 204188, -45296], ![-6749104, 190571, 204188]]]
  hmulB := by decide  
  f := ![![![50324843360, 9492639957, 1790571164]], ![![6592879956, 1243597228, 234576403]], ![![58905207583, 11111131001, 2095862780]]]
  g := ![![![4437, -45296, 1279], ![26269, 204188, -45296], ![-263968, 190571, 204188]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-50324843360, -9492639957, -1790571164]] ![![204188, -45296, 1279]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![6, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![6, 1, 0]] 
 ![![73, 0, 0], ![6, 1, 0], ![37, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![6, 1, 0], ![0, 6, 1], ![149, 0, 6]]]
  hmulB := by decide  
  f := ![![![307, 51, 0], ![-3723, 0, 0]], ![![18, 3, 0], ![-218, 0, 0]], ![![151, 25, 0], ![-1831, 1, 0]]]
  g := ![![![1, 0, 0], ![-6, 73, 0], ![-37, 0, 73]], ![![0, 1, 0], ![-1, 6, 1], ![-1, 0, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16, 3, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-16, 3, 0]] 
 ![![73, 0, 0], ![19, 1, 0], ![4, 0, 1]] where
  M :=![![![-16, 3, 0], ![0, -16, 3], ![447, 0, -16]]]
  hmulB := by decide  
  f := ![![![-256, -48, -9]], ![![-85, -16, -3]], ![![-112, -21, -4]]]
  g := ![![![-1, 3, 0], ![4, -16, 3], ![7, 0, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-25, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-25, 1, 0]] 
 ![![73, 0, 0], ![48, 1, 0], ![32, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-25, 1, 0], ![0, -25, 1], ![149, 0, -25]]]
  hmulB := by decide  
  f := ![![![1251, -50, 0], ![3650, 0, 0]], ![![826, -33, 0], ![2410, 0, 0]], ![![584, -23, 0], ![1704, 1, 0]]]
  g := ![![![1, 0, 0], ![-48, 73, 0], ![-32, 0, 73]], ![![-1, 1, 0], ![16, -25, 1], ![13, 0, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![6, 1, 0]] ![![-16, 3, 0]]
  ![![73, 0, 0], ![-32, 25, 1]] where
 M := ![![![-1168, 219, 0]], ![![-96, 2, 3]]]
 hmul := by decide  
 g := ![![![![16, -22, -1], ![73, 0, 0]]], ![![![0, -1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-32, 25, 1]] ![![73, 0, 0], ![-25, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1825, 73, 0]], ![![-2336, 1825, 73], ![949, -657, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-25, 1, 0]]], ![![![-32, 25, 1]], ![![13, -9, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [7, 1, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 29, 58], [78, 49, 21], [0, 1]]
 g := ![![[68, 18, 65], [13, 57, 11], [22, 67, 18], [29, 60, 64], [76, 1], []], ![[50, 44, 33, 30], [24, 12, 13, 6], [9, 61, 56, 33], [55, 32, 15, 74], [48, 31], [66, 46]], ![[31, 67, 25, 13], [28, 72], [28, 0, 72, 65], [63, 61, 28, 46], [7, 51], [24, 46]]]
 h' := ![![[77, 29, 58], [67, 78, 12], [4, 33, 66], [34, 71, 27], [21, 75, 8], [0, 0, 1], [0, 1]], ![[78, 49, 21], [24, 6, 56], [46, 4, 13], [8, 64, 69], [78, 39, 2], [16, 49, 49], [77, 29, 58]], ![[0, 1], [39, 74, 11], [9, 42], [36, 23, 62], [32, 44, 69], [70, 30, 29], [78, 49, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 53], []]
 b := ![[], [46, 1, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [7, 1, 3, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18170, -4029, 1343]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-230, -51, 17]
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



lemma PB220I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB220I1 : PrimesBelowBoundCertificateInterval O 31 79 220 where
  m := 11
  g := ![3, 2, 1, 2, 2, 2, 3, 3, 2, 3, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB220I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1, I73N2]
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
    · exact ![37, 37, 37]
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![61, 61, 61]
    · exact ![67, 67, 67]
    · exact ![5041, 71]
    · exact ![73, 73, 73]
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
      exact NI37N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
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
  β := ![I37N0, I37N1, I37N2, I41N1, I47N1, I53N1, I59N1, I61N0, I61N1, I61N2, I67N0, I67N1, I67N2, I71N1, I73N0, I73N1, I73N2]
  Il := ![[I37N0, I37N1, I37N2], [I41N1], [], [I47N1], [I53N1], [I59N1], [I61N0, I61N1, I61N2], [I67N0, I67N1, I67N2], [I71N1], [I73N0, I73N1, I73N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
