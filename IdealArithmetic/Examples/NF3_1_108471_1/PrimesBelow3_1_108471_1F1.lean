
import IdealArithmetic.Examples.NF3_1_108471_1.RI3_1_108471_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-2, 18, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-2, 18, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![35, 18, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-2, 18, 1], ![-75, -28, 93], ![-1425, 171, 65]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -18, 37]], ![![-1, 0, 1], ![-90, -46, 93], ![-100, -27, 65]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [32, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 36], [0, 1]]
 g := ![![[12, 9], [11], [5, 4], [11], [1]], ![[34, 28], [11], [23, 33], [11], [1]]]
 h' := ![![[23, 36], [14, 34], [25, 23], [6, 2], [5, 23], [0, 1]], ![[0, 1], [19, 3], [36, 14], [15, 35], [16, 14], [23, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [27, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [32, 14, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1168, -1032, 621]
  a := ![0, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-619, -330, 621]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![18, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![18, 1, 0]] 
 ![![37, 0, 0], ![18, 1, 0], ![9, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![18, 1, 0], ![0, 16, 5], ![-75, 10, 21]]]
  hmulB := by decide  
  f := ![![![523, 29, 0], ![-1073, 0, 0]], ![![234, 13, 0], ![-480, 0, 0]], ![![99, -1, -2], ![-203, 15, 0]]]
  g := ![![![1, 0, 0], ![-18, 37, 0], ![-9, 0, 37]], ![![0, 1, 0], ![-9, 16, 5], ![-12, 10, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-2, 18, 1]] ![![37, 0, 0], ![18, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![666, 37, 0]], ![![-74, 666, 37], ![-111, 296, 111]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![18, 1, 0]]], ![![![-2, 18, 1]], ![![-3, 8, 3]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-9, 12, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-9, 12, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![32, 12, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-9, 12, 1], ![-75, -23, 63], ![-975, 111, 40]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -12, 41]], ![![-1, 0, 1], ![-51, -19, 63], ![-55, -9, 40]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [23, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 40], [0, 1]]
 g := ![![[12, 25], [40], [20], [5, 39], [1]], ![[0, 16], [40], [20], [24, 2], [1]]]
 h' := ![![[11, 40], [14, 36], [14, 9], [8, 15], [18, 11], [0, 1]], ![[0, 1], [0, 5], [31, 32], [9, 26], [16, 30], [11, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [23, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [23, 30, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-681, -1593, 1169]
  a := ![-1, -4, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-929, -381, 1169]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![19, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![19, 1, 0]] 
 ![![41, 0, 0], ![19, 1, 0], ![1, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![19, 1, 0], ![0, 17, 5], ![-75, 10, 22]]]
  hmulB := by decide  
  f := ![![![96, 5, 0], ![-205, 0, 0]], ![![38, 2, 0], ![-81, 0, 0]], ![![-6, -14, -4], ![13, 33, 0]]]
  g := ![![![1, 0, 0], ![-19, 41, 0], ![-1, 0, 41]], ![![0, 1, 0], ![-8, 17, 5], ![-7, 10, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-9, 12, 1]] ![![41, 0, 0], ![19, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![779, 41, 0]], ![![-369, 492, 41], ![-246, 205, 82]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![19, 1, 0]]], ![![![-9, 12, 1]], ![![-6, 5, 2]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-3, 13, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-3, 13, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![40, 13, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-3, 13, 1], ![-75, -19, 68], ![-1050, 121, 49]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-40, -13, 43]], ![![-1, 0, 1], ![-65, -21, 68], ![-70, -12, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [23, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 42], [0, 1]]
 g := ![![[38, 15], [17, 35], [21], [7, 24], [1]], ![[0, 28], [0, 8], [21], [15, 19], [1]]]
 h' := ![![[29, 42], [39, 12], [25, 11], [11, 8], [20, 29], [0, 1]], ![[0, 1], [0, 31], [0, 32], [28, 35], [1, 14], [29, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [4, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [23, 14, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3223, -192, 273]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-179, -87, 273]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![18, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![18, 1, 0]] 
 ![![43, 0, 0], ![18, 1, 0], ![37, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![18, 1, 0], ![0, 16, 5], ![-75, 10, 21]]]
  hmulB := by decide  
  f := ![![![73, 4, 0], ![-172, 0, 0]], ![![18, 1, 0], ![-42, 0, 0]], ![![67, -6, -3], ![-158, 26, 0]]]
  g := ![![![1, 0, 0], ![-18, 43, 0], ![-37, 0, 43]], ![![0, 1, 0], ![-11, 16, 5], ![-24, 10, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-3, 13, 1]] ![![43, 0, 0], ![18, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![774, 43, 0]], ![![-129, 559, 43], ![-129, 215, 86]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![18, 1, 0]]], ![![![-3, 13, 1]], ![![-3, 5, 2]]]]
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
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-599, -13, 35]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-599, -13, 35]] 
 ![![47, 0, 0], ![0, 47, 0], ![46, 5, 1]] where
  M :=![![![-599, -13, 35], ![-2625, -223, 40], ![-1650, -445, -183]]]
  hmulB := by decide  
  f := ![![![1247, -382, 155]], ![![-11625, 3561, -1445]], ![![346, -106, 43]]]
  g := ![![![-47, -4, 35], ![-95, -9, 40], ![144, 10, -183]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [40, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 46], [0, 1]]
 g := ![![[8, 14], [19, 3], [38, 17], [9, 34], [1]], ![[40, 33], [46, 44], [3, 30], [33, 13], [1]]]
 h' := ![![[9, 46], [39, 25], [31, 12], [16, 39], [7, 9], [0, 1]], ![[0, 1], [29, 22], [45, 35], [38, 8], [41, 38], [9, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [10, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [40, 38, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1721, -2346, 1157]
  a := ![1, 5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1169, -173, 1157]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1247, 382, -155]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-1247, 382, -155]] 
 ![![47, 0, 0], ![19, 1, 0], ![20, 0, 1]] where
  M :=![![![-1247, 382, -155], ![11625, -3561, 1445], ![-17025, 5215, -2116]]]
  hmulB := by decide  
  f := ![![![599, 13, -35]], ![![298, 10, -15]], ![![290, 15, -11]]]
  g := ![![![-115, 382, -155], ![1072, -3561, 1445], ![-1570, 5215, -2116]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-599, -13, 35]] ![![-1247, 382, -155]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1558, 13, 123]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-1558, 13, 123]] 
 ![![53, 0, 0], ![0, 53, 0], ![5, 7, 1]] where
  M :=![![![-1558, 13, 123], ![-9225, -354, 434], ![-10200, -977, 80]]]
  hmulB := by decide  
  f := ![![![-7466, 2287, -928]], ![![69600, -21320, 8651]], ![![6565, -2011, 816]]]
  g := ![![![-41, -16, 123], ![-215, -64, 434], ![-200, -29, 80]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [33, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 52], [0, 1]]
 g := ![![[30, 43], [25], [28, 40], [28], [17, 1]], ![[19, 10], [25], [19, 13], [28], [34, 52]]]
 h' := ![![[17, 52], [22, 19], [30, 48], [37, 27], [22, 44], [0, 1]], ![[0, 1], [27, 34], [51, 5], [19, 26], [28, 9], [17, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [18, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [33, 36, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1167, -966, 445]
  a := ![0, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-64, -77, 445]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7466, -2287, 928]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![7466, -2287, 928]] 
 ![![53, 0, 0], ![15, 1, 0], ![14, 0, 1]] where
  M :=![![![7466, -2287, 928], ![-69600, 21320, -8651], ![101925, -31222, 12669]]]
  hmulB := by decide  
  f := ![![![1558, -13, -123]], ![![615, 3, -43]], ![![604, 15, -34]]]
  g := ![![![543, -2287, 928], ![-5062, 21320, -8651], ![7413, -31222, 12669]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-1558, 13, 123]] ![![7466, -2287, 928]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, 9, -4]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-31, 9, -4]] 
 ![![59, 0, 0], ![0, 59, 0], ![52, 42, 1]] where
  M :=![![![-31, 9, -4], ![300, -89, 33], ![-375, 126, -56]]]
  hmulB := by decide  
  f := ![![![-14, 0, 1]], ![![-75, -4, 3]], ![![-67, -3, 3]]]
  g := ![![![3, 3, -4], ![-24, -25, 33], ![43, 42, -56]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [46, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 58], [0, 1]]
 g := ![![[27, 9], [37, 26], [15], [18, 12], [56, 1]], ![[0, 50], [18, 33], [15], [41, 47], [53, 58]]]
 h' := ![![[56, 58], [9, 3], [22, 12], [57, 30], [20, 22], [0, 1]], ![[0, 1], [0, 56], [45, 47], [26, 29], [13, 37], [56, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [28, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [46, 3, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-92950, -61623, 44675]
  a := ![1, -21, 62]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-40950, -32847, 44675]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14, 0, 1]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-14, 0, 1]] 
 ![![59, 0, 0], ![23, 1, 0], ![45, 0, 1]] where
  M :=![![![-14, 0, 1], ![-75, -4, 3], ![-75, -9, -1]]]
  hmulB := by decide  
  f := ![![![-31, 9, -4]], ![![-7, 2, -1]], ![![-30, 9, -4]]]
  g := ![![![-1, 0, 1], ![-2, -4, 3], ![3, -9, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-31, 9, -4]] ![![-14, 0, 1]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [58, 56, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 10, 39], [16, 50, 22], [0, 1]]
 g := ![![[24, 16, 57], [17, 19], [49, 16, 34], [29, 6, 58], [1]], ![[54, 7, 2, 39], [54, 45], [46, 28, 44, 12], [56, 41, 57, 45], [41, 25, 60, 27]], ![[4, 44, 40, 48], [32, 5], [53, 19, 26, 9], [12, 55, 10, 42], [29, 19, 13, 34]]]
 h' := ![![[11, 10, 39], [5, 36, 39], [25, 54, 18], [26, 50, 41], [3, 5, 27], [0, 1]], ![[16, 50, 22], [52, 5, 60], [45, 43, 17], [48, 22, 35], [51, 6, 20], [11, 10, 39]], ![[0, 1], [44, 20, 23], [3, 25, 26], [55, 50, 46], [35, 50, 14], [16, 50, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 20], []]
 b := ![[], [0, 9, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [58, 56, 34, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6710, -24583, 11102]
  a := ![-1, -1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![110, -403, 182]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![364, -111, 45]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![364, -111, 45]] 
 ![![67, 0, 0], ![0, 67, 0], ![20, 2, 1]] where
  M :=![![![364, -111, 45], ![-3375, 1036, -420], ![4950, -1515, 616]]]
  hmulB := by decide  
  f := ![![![28, 3, 0]], ![![0, 22, 15]], ![![5, 2, 1]]]
  g := ![![![-8, -3, 45], ![75, 28, -420], ![-110, -41, 616]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [47, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 66], [0, 1]]
 g := ![![[6, 10], [62, 14], [62], [39], [62], [1]], ![[0, 57], [0, 53], [62], [39], [62], [1]]]
 h' := ![![[53, 66], [34, 12], [59, 9], [62, 53], [32, 46], [20, 53], [0, 1]], ![[0, 1], [0, 55], [0, 58], [57, 14], [58, 21], [15, 14], [53, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [15, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [47, 14, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2878, -2941, 2114]
  a := ![0, -5, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-674, -107, 2114]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28, -3, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-28, -3, 0]] 
 ![![67, 0, 0], ![54, 1, 0], ![28, 0, 1]] where
  M :=![![![-28, -3, 0], ![0, -22, -15], ![225, -30, -37]]]
  hmulB := by decide  
  f := ![![![-364, 111, -45]], ![![-243, 74, -30]], ![![-226, 69, -28]]]
  g := ![![![2, -3, 0], ![24, -22, -15], ![43, -30, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![364, -111, 45]] ![![-28, -3, 0]]
  ![![67, 0, 0]] where
 M := ![![![-67, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-42, 17, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-42, 17, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![29, 17, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-42, 17, 1], ![-75, -66, 88], ![-1350, 161, 22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -17, 71]], ![![-1, 0, 1], ![-37, -22, 88], ![-28, -3, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [41, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 70], [0, 1]]
 g := ![![[1, 48], [39, 8], [42, 2], [37], [48], [1]], ![[21, 23], [66, 63], [31, 69], [37], [48], [1]]]
 h' := ![![[30, 70], [34, 30], [53, 47], [54, 59], [68, 45], [30, 30], [0, 1]], ![[0, 1], [11, 41], [43, 24], [49, 12], [69, 26], [7, 41], [30, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [23, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [41, 41, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11873, -5802, 3760]
  a := ![2, 6, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1703, -982, 3760]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-17, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-17, 1, 0]] 
 ![![71, 0, 0], ![54, 1, 0], ![49, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-17, 1, 0], ![0, -19, 5], ![-75, 10, -14]]]
  hmulB := by decide  
  f := ![![![851, -50, 0], ![3550, 0, 0]], ![![630, -37, 0], ![2628, 0, 0]], ![![583, -19, -4], ![2432, 57, 0]]]
  g := ![![![1, 0, 0], ![-54, 71, 0], ![-49, 0, 71]], ![![-1, 1, 0], ![11, -19, 5], ![1, 10, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-42, 17, 1]] ![![71, 0, 0], ![-17, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1207, 71, 0]], ![![-2982, 1207, 71], ![639, -355, 71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-17, 1, 0]]], ![![![-42, 17, 1]], ![![9, -5, 1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19306831, 5914113, -2399772]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-19306831, 5914113, -2399772]] 
 ![![73, 0, 0], ![0, 73, 0], ![24, 59, 1]] where
  M :=![![![-19306831, 5914113, -2399772], ![179982900, -55132777, 22371249], ![-263575575, 80739078, -32761528]]]
  hmulB := by decide  
  f := ![![![7742, 624, -141]], ![![10575, 5084, 2697]], ![![10596, 4417, 2240]]]
  g := ![![![524489, 2020557, -2399772], ![-4889412, -18836116, 22371249], ![7160289, 27584510, -32761528]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [63, 59, 1] where
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
 g := ![![[16, 4], [35], [54], [65, 12], [50], [1]], ![[72, 69], [35], [54], [14, 61], [50], [1]]]
 h' := ![![[14, 72], [10, 71], [5, 53], [66, 45], [16, 31], [10, 14], [0, 1]], ![[0, 1], [55, 2], [17, 20], [39, 28], [12, 42], [60, 59], [14, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [18, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [63, 59, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![999, -163, 215]
  a := ![13, -1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-57, -176, 215]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7742, 624, -141]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![7742, 624, -141]] 
 ![![73, 0, 0], ![67, 1, 0], ![5, 0, 1]] where
  M :=![![![7742, 624, -141], ![10575, 5084, 2697], ![-36225, 7509, 7781]]]
  hmulB := by decide  
  f := ![![![-19306831, 5914113, -2399772]], ![![-15254449, 4672778, -1896075]], ![![-4933010, 1511091, -613156]]]
  g := ![![![-457, 624, -141], ![-4706, 5084, 2697], ![-7921, 7509, 7781]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-19306831, 5914113, -2399772]] ![![7742, 624, -141]]
  ![![73, 0, 0]] where
 M := ![![![73, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-20, 12, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-20, 12, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![59, 12, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-20, 12, 1], ![-75, -34, 63], ![-975, 111, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-59, -12, 79]], ![![-1, 0, 1], ![-48, -10, 63], ![-34, -3, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [43, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 78], [0, 1]]
 g := ![![[54, 64], [68, 62], [42, 38], [73, 73], [13], [1]], ![[45, 15], [42, 17], [49, 41], [22, 6], [13], [1]]]
 h' := ![![[48, 78], [78, 8], [11, 33], [21, 14], [26, 51], [36, 48], [0, 1]], ![[0, 1], [67, 71], [15, 46], [61, 65], [25, 28], [49, 31], [48, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [31, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [43, 31, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6300, -4515, 2764]
  a := ![1, 6, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2144, -477, 2764]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![16, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![16, 1, 0]] 
 ![![79, 0, 0], ![16, 1, 0], ![50, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![16, 1, 0], ![0, 14, 5], ![-75, 10, 19]]]
  hmulB := by decide  
  f := ![![![49, 3, 0], ![-237, 0, 0]], ![![-16, -1, 0], ![80, 0, 0]], ![![46, 0, -1], ![-224, 16, 0]]]
  g := ![![![1, 0, 0], ![-16, 79, 0], ![-50, 0, 79]], ![![0, 1, 0], ![-6, 14, 5], ![-15, 10, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-20, 12, 1]] ![![79, 0, 0], ![16, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![1264, 79, 0]], ![![-1580, 948, 79], ![-395, 158, 79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![16, 1, 0]]], ![![![-20, 12, 1]], ![![-5, 2, 1]]]]
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


lemma PB94I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB94I1 : PrimesBelowBoundCertificateInterval O 31 79 94 where
  m := 11
  g := ![2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB94I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
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
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![5041, 71]
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
      exact NI37N1
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
      exact NI79N1
  β := ![I37N1, I41N1, I43N1, I47N1, I53N1, I59N1, I67N1, I71N1, I73N1, I79N1]
  Il := ![[I37N1], [I41N1], [I43N1], [I47N1], [I53N1], [I59N1], [], [I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
