
import IdealArithmetic.Examples.NF3_1_408807_1.RI3_1_408807_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![28, -8, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![28, -8, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![28, 29, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![28, -8, 1], ![105, 7, -24], ![-840, 203, 7]]]
  hmulB := by decide  
  f := ![![![-27, 8, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -29, 37]], ![![0, -1, 1], ![21, 19, -24], ![-28, 0, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [23, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 36], [0, 1]]
 g := ![![[15, 12], [30], [29, 27], [33], [1]], ![[19, 25], [30], [1, 10], [33], [1]]]
 h' := ![![[25, 36], [14, 7], [36, 20], [29, 8], [14, 25], [0, 1]], ![[0, 1], [4, 30], [18, 17], [7, 29], [10, 12], [25, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [14, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [23, 12, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![233, -19, -30]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29, 23, -30]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-13, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-13, 1, 0]] 
 ![![37, 0, 0], ![24, 1, 0], ![30, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-13, 1, 0], ![0, -13, 3], ![105, -21, -13]]]
  hmulB := by decide  
  f := ![![![339, -26, 0], ![962, 0, 0]], ![![222, -17, 0], ![630, 0, 0]], ![![284, -13, -2], ![806, 25, 0]]]
  g := ![![![1, 0, 0], ![-24, 37, 0], ![-30, 0, 37]], ![![-1, 1, 0], ![6, -13, 3], ![27, -21, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![28, -8, 1]] ![![37, 0, 0], ![-13, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-481, 37, 0]], ![![1036, -296, 37], ![-259, 111, -37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-13, 1, 0]]], ![![![28, -8, 1]], ![![-7, 3, -1]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [22, 11, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 27, 31], [32, 13, 10], [0, 1]]
 g := ![![[39, 31, 40], [0, 10], [5, 2], [25, 35, 1], []], ![[38, 16, 39, 36], [25, 20], [11, 39], [35, 16, 23, 32], [8, 18]], ![[29, 30, 14, 23], [38, 18], [29, 5], [1, 13, 12, 33], [29, 18]]]
 h' := ![![[3, 27, 31], [20, 31, 9], [15, 7, 16], [24, 21, 17], [0, 0, 1], [0, 1]], ![[32, 13, 10], [4, 30, 12], [29, 39, 15], [36, 13, 11], [38, 6, 13], [3, 27, 31]], ![[0, 1], [17, 21, 20], [19, 36, 10], [1, 7, 13], [17, 35, 27], [32, 13, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 17], []]
 b := ![[], [38, 9, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [22, 11, 6, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![212011, -57523, 3444]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5171, -1403, 84]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![29, 19, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![29, 19, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![29, 19, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![29, 19, 1], ![105, 8, 57], ![1995, -364, 8]]]
  hmulB := by decide  
  f := ![![![-28, -19, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -19, 43]], ![![0, 0, 1], ![-36, -25, 57], ![41, -12, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [30, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 42], [0, 1]]
 g := ![![[26, 35], [33, 9], [15], [15, 36], [1]], ![[31, 8], [22, 34], [15], [14, 7], [1]]]
 h' := ![![[37, 42], [42, 11], [36, 3], [23, 31], [13, 37], [0, 1]], ![[0, 1], [19, 32], [18, 40], [9, 12], [6, 6], [37, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [40, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [30, 6, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3532, -45, 104]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12, -47, 104]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-14, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-14, 1, 0]] 
 ![![43, 0, 0], ![29, 1, 0], ![35, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-14, 1, 0], ![0, -14, 3], ![105, -21, -14]]]
  hmulB := by decide  
  f := ![![![589, -42, 0], ![1806, 0, 0]], ![![407, -29, 0], ![1248, 0, 0]], ![![497, -26, -2], ![1524, 29, 0]]]
  g := ![![![1, 0, 0], ![-29, 43, 0], ![-35, 0, 43]], ![![-1, 1, 0], ![7, -14, 3], ![28, -21, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![29, 19, 1]] ![![43, 0, 0], ![-14, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-602, 43, 0]], ![![1247, 817, 43], ![-301, -258, 43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-14, 1, 0]]], ![![![29, 19, 1]], ![![-7, -6, 1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![25, -8, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![25, -8, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![25, 39, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![25, -8, 1], ![105, 4, -24], ![-840, 203, 4]]]
  hmulB := by decide  
  f := ![![![-24, 8, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -39, 47]], ![![0, -1, 1], ![15, 20, -24], ![-20, 1, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [21, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 46], [0, 1]]
 g := ![![[28, 9], [37, 27], [26, 7], [15, 12], [1]], ![[0, 38], [0, 20], [46, 40], [9, 35], [1]]]
 h' := ![![[23, 46], [22, 44], [18, 36], [14, 17], [26, 23], [0, 1]], ![[0, 1], [0, 3], [0, 11], [29, 30], [38, 24], [23, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [16, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [21, 24, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-584, 467, -264]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![128, 229, -264]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-23, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-23, 1, 0]] 
 ![![47, 0, 0], ![24, 1, 0], ![43, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-23, 1, 0], ![0, -23, 3], ![105, -21, -23]]]
  hmulB := by decide  
  f := ![![![1082, -47, 0], ![2209, 0, 0]], ![![576, -25, 0], ![1176, 0, 0]], ![![986, -35, -1], ![2013, 16, 0]]]
  g := ![![![1, 0, 0], ![-24, 47, 0], ![-43, 0, 47]], ![![-1, 1, 0], ![9, -23, 3], ![34, -21, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![25, -8, 1]] ![![47, 0, 0], ![-23, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-1081, 47, 0]], ![![1175, -376, 47], ![-470, 188, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-23, 1, 0]]], ![![![25, -8, 1]], ![![-10, 4, -1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-12, -25, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-12, -25, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![41, 28, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-12, -25, 1], ![105, -33, -75], ![-2625, 560, -33]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -28, 53]], ![![-1, -1, 1], ![60, 39, -75], ![-24, 28, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [3, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 52], [0, 1]]
 g := ![![[22, 16], [46], [29, 13], [49], [40, 1]], ![[26, 37], [46], [19, 40], [49], [27, 52]]]
 h' := ![![[40, 52], [11, 49], [19, 24], [49, 15], [39, 7], [0, 1]], ![[0, 1], [10, 4], [25, 29], [13, 38], [1, 46], [40, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [33, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [3, 13, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![213, -20, -31]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![28, 16, -31]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![22, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![22, 1, 0]] 
 ![![53, 0, 0], ![22, 1, 0], ![33, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![22, 1, 0], ![0, 22, 3], ![105, -21, 22]]]
  hmulB := by decide  
  f := ![![![375, 17, 0], ![-901, 0, 0]], ![![154, 7, 0], ![-370, 0, 0]], ![![231, 3, -1], ![-555, 18, 0]]]
  g := ![![![1, 0, 0], ![-22, 53, 0], ![-33, 0, 53]], ![![0, 1, 0], ![-11, 22, 3], ![-3, -21, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-12, -25, 1]] ![![53, 0, 0], ![22, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![1166, 53, 0]], ![![-636, -1325, 53], ![-159, -583, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![22, 1, 0]]], ![![![-12, -25, 1]], ![![-3, -11, -1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![3, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![3, 1, 0]] 
 ![![59, 0, 0], ![3, 1, 0], ![56, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![3, 1, 0], ![0, 3, 3], ![105, -21, 3]]]
  hmulB := by decide  
  f := ![![![55, 18, 0], ![-1062, 0, 0]], ![![-3, -1, 0], ![60, 0, 0]], ![![52, 16, -1], ![-1004, 20, 0]]]
  g := ![![![1, 0, 0], ![-3, 59, 0], ![-56, 0, 59]], ![![0, 1, 0], ![-3, 3, 3], ![0, -21, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![26, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![26, 1, 0]] 
 ![![59, 0, 0], ![26, 1, 0], ![50, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![26, 1, 0], ![0, 26, 3], ![105, -21, 26]]]
  hmulB := by decide  
  f := ![![![443, 17, 0], ![-1003, 0, 0]], ![![182, 7, 0], ![-412, 0, 0]], ![![334, 4, -1], ![-756, 20, 0]]]
  g := ![![![1, 0, 0], ![-26, 59, 0], ![-50, 0, 59]], ![![0, 1, 0], ![-14, 26, 3], ![-11, -21, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-29, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-29, 1, 0]] 
 ![![59, 0, 0], ![30, 1, 0], ![54, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-29, 1, 0], ![0, -29, 3], ![105, -21, -29]]]
  hmulB := by decide  
  f := ![![![1712, -59, 0], ![3481, 0, 0]], ![![900, -31, 0], ![1830, 0, 0]], ![![1562, -44, -1], ![3176, 20, 0]]]
  g := ![![![1, 0, 0], ![-30, 59, 0], ![-54, 0, 59]], ![![-1, 1, 0], ![12, -29, 3], ![39, -21, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![3, 1, 0]] ![![59, 0, 0], ![26, 1, 0]]
  ![![59, 0, 0], ![26, -10, 1]] where
 M := ![![![3481, 0, 0], ![1534, 59, 0]], ![![177, 59, 0], ![78, 29, 3]]]
 hmul := by decide  
 g := ![![![![33, 10, -1], ![59, 0, 0]], ![![0, 11, -1], ![59, 0, 0]]], ![![![-23, 11, -1], ![59, 0, 0]], ![![0, 1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![26, -10, 1]] ![![59, 0, 0], ![-29, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1711, 59, 0]], ![![1534, -590, 59], ![-649, 295, -59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-29, 1, 0]]], ![![![26, -10, 1]], ![![-11, 5, -1]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [15, 38, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 22, 29], [33, 38, 32], [0, 1]]
 g := ![![[17, 45, 39], [26, 34], [20, 33, 9], [36, 9, 57], [1]], ![[39, 52, 39, 59], [40, 34], [49, 27, 31, 2], [6, 4, 43, 6], [19, 28, 59, 50]], ![[32, 25, 37, 7], [10, 14], [59, 19, 49, 21], [21, 38], [15, 22, 41, 11]]]
 h' := ![![[50, 22, 29], [1, 60, 10], [5, 46, 20], [9, 3, 3], [46, 23, 22], [0, 1]], ![[33, 38, 32], [37, 3, 46], [37, 25, 20], [14, 43, 18], [31, 12, 39], [50, 22, 29]], ![[0, 1], [58, 59, 5], [56, 51, 21], [13, 15, 40], [27, 26], [33, 38, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37], []]
 b := ![[], [6, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [15, 38, 39, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2206248, -324520, -17080]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![36168, -5320, -280]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![15, -20, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![15, -20, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![15, 47, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![15, -20, 1], ![105, -6, -60], ![-2100, 455, -6]]]
  hmulB := by decide  
  f := ![![![-14, 20, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -47, 67]], ![![0, -1, 1], ![15, 42, -60], ![-30, 11, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [60, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 66], [0, 1]]
 g := ![![[21, 19], [65, 62], [39], [17], [35], [1]], ![[0, 48], [0, 5], [39], [17], [35], [1]]]
 h' := ![![[13, 66], [53, 32], [19, 14], [58, 46], [26, 34], [7, 13], [0, 1]], ![[0, 1], [0, 35], [0, 53], [53, 21], [66, 33], [42, 54], [13, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [47, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [60, 54, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-623, 317, -46]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1, 37, -46]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-7, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-7, 1, 0]] 
 ![![67, 0, 0], ![60, 1, 0], ![6, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-7, 1, 0], ![0, -7, 3], ![105, -21, -7]]]
  hmulB := by decide  
  f := ![![![365, -52, 0], ![3484, 0, 0]], ![![330, -47, 0], ![3150, 0, 0]], ![![40, -1, -2], ![382, 45, 0]]]
  g := ![![![1, 0, 0], ![-60, 67, 0], ![-6, 0, 67]], ![![-1, 1, 0], ![6, -7, 3], ![21, -21, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![15, -20, 1]] ![![67, 0, 0], ![-7, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-469, 67, 0]], ![![1005, -1340, 67], ![0, 134, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-7, 1, 0]]], ![![![15, -20, 1]], ![![0, 2, -1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![29, 11, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![29, 11, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![29, 11, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![29, 11, 1], ![105, 8, 33], ![1155, -196, 8]]]
  hmulB := by decide  
  f := ![![![-28, -11, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -11, 71]], ![![0, 0, 1], ![-12, -5, 33], ![13, -4, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [46, 62, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 70], [0, 1]]
 g := ![![[60, 8], [22, 10], [62, 5], [3], [10], [1]], ![[61, 63], [41, 61], [36, 66], [3], [10], [1]]]
 h' := ![![[9, 70], [53, 24], [59, 62], [36, 17], [23, 43], [25, 9], [0, 1]], ![[0, 1], [56, 47], [49, 9], [47, 54], [55, 28], [35, 62], [9, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [33, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [46, 62, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![466, 118, 43]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11, -5, 43]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-33, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-33, 1, 0]] 
 ![![71, 0, 0], ![38, 1, 0], ![63, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-33, 1, 0], ![0, -33, 3], ![105, -21, -33]]]
  hmulB := by decide  
  f := ![![![1387, -42, 0], ![2982, 0, 0]], ![![760, -23, 0], ![1634, 0, 0]], ![![1227, -26, -1], ![2638, 24, 0]]]
  g := ![![![1, 0, 0], ![-38, 71, 0], ![-63, 0, 71]], ![![-1, 1, 0], ![15, -33, 3], ![42, -21, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![29, 11, 1]] ![![71, 0, 0], ![-33, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-2343, 71, 0]], ![![2059, 781, 71], ![-852, -355, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-33, 1, 0]]], ![![![29, 11, 1]], ![![-12, -5, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-20, -20, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-20, -20, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![53, 53, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-20, -20, 1], ![105, -41, -60], ![-2100, 455, -41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-53, -53, 73]], ![![-1, -1, 1], ![45, 43, -60], ![1, 36, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [4, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 72], [0, 1]]
 g := ![![[40, 55], [71], [2], [7, 16], [50], [1]], ![[0, 18], [71], [2], [2, 57], [50], [1]]]
 h' := ![![[59, 72], [7, 37], [46, 12], [45, 41], [35, 69], [69, 59], [0, 1]], ![[0, 1], [0, 36], [24, 61], [55, 32], [18, 4], [46, 14], [59, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [64, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [4, 14, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4164, 800, 252]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-240, -172, 252]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-13, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-13, 1, 0]] 
 ![![73, 0, 0], ![60, 1, 0], ![41, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-13, 1, 0], ![0, -13, 3], ![105, -21, -13]]]
  hmulB := by decide  
  f := ![![![664, -51, 0], ![3723, 0, 0]], ![![560, -43, 0], ![3140, 0, 0]], ![![374, -20, -2], ![2097, 49, 0]]]
  g := ![![![1, 0, 0], ![-60, 73, 0], ![-41, 0, 73]], ![![-1, 1, 0], ![9, -13, 3], ![26, -21, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-20, -20, 1]] ![![73, 0, 0], ![-13, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-949, 73, 0]], ![![-1460, -1460, 73], ![365, 219, -73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-13, 1, 0]]], ![![![-20, -20, 1]], ![![5, 3, -1]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [51, 76, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 29, 29], [35, 49, 50], [0, 1]]
 g := ![![[72, 68, 49], [54, 10, 38], [8, 17, 10], [48, 24, 65], [76, 1], []], ![[50, 77, 23, 69], [69, 21, 27, 71], [13, 19, 27, 17], [73, 43, 77, 60], [31, 31], [28, 51]], ![[34, 56, 28, 46], [9, 58, 25, 5], [19, 27, 15, 2], [38, 37, 61, 51], [9, 51], [7, 51]]]
 h' := ![![[41, 29, 29], [11, 58, 72], [66, 27, 14], [1, 51, 57], [74, 19, 12], [0, 0, 1], [0, 1]], ![[35, 49, 50], [65, 48, 75], [54, 22, 47], [2, 34, 6], [18, 68, 33], [16, 19, 49], [41, 29, 29]], ![[0, 1], [73, 52, 11], [49, 30, 18], [70, 73, 16], [16, 71, 34], [78, 60, 29], [35, 49, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67, 30], []]
 b := ![[], [40, 0, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [51, 76, 3, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4898, 158, -158]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![62, 2, -2]
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



lemma PB181I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB181I1 : PrimesBelowBoundCertificateInterval O 31 79 181 where
  m := 11
  g := ![2, 1, 2, 2, 2, 3, 1, 2, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB181I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
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
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
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
      exact NI59N2
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
  β := ![I37N1, I43N1, I47N1, I53N1, I59N0, I59N1, I59N2, I67N1, I71N1, I73N1]
  Il := ![[I37N1], [], [I43N1], [I47N1], [I53N1], [I59N0, I59N1, I59N2], [], [I67N1], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
