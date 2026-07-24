
import IdealArithmetic.Examples.NF3_1_412776_3.RI3_1_412776_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-18, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-18, 1, 0]] 
 ![![37, 0, 0], ![19, 1, 0], ![23, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-18, 1, 0], ![0, -18, 2], ![112, -21, -18]]]
  hmulB := by decide  
  f := ![![![667, -37, 0], ![1369, 0, 0]], ![![361, -20, 0], ![741, 0, 0]], ![![437, -15, -1], ![897, 19, 0]]]
  g := ![![![1, 0, 0], ![-19, 37, 0], ![-23, 0, 37]], ![![-1, 1, 0], ![8, -18, 2], ![25, -21, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-14, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-14, 1, 0]] 
 ![![37, 0, 0], ![23, 1, 0], ![13, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-14, 1, 0], ![0, -14, 2], ![112, -21, -14]]]
  hmulB := by decide  
  f := ![![![197, -14, 0], ![518, 0, 0]], ![![127, -9, 0], ![334, 0, 0]], ![![73, 2, -1], ![192, 19, 0]]]
  g := ![![![1, 0, 0], ![-23, 37, 0], ![-13, 0, 37]], ![![-1, 1, 0], ![8, -14, 2], ![21, -21, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-5, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-5, 1, 0]] 
 ![![37, 0, 0], ![32, 1, 0], ![6, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-5, 1, 0], ![0, -5, 2], ![112, -21, -5]]]
  hmulB := by decide  
  f := ![![![96, -19, 0], ![703, 0, 0]], ![![76, -15, 0], ![556, 0, 0]], ![![18, -1, -1], ![132, 19, 0]]]
  g := ![![![1, 0, 0], ![-32, 37, 0], ![-6, 0, 37]], ![![-1, 1, 0], ![4, -5, 2], ![22, -21, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-18, 1, 0]] ![![37, 0, 0], ![-14, 1, 0]]
  ![![37, 0, 0], ![15, -16, 1]] where
 M := ![![![1369, 0, 0], ![-518, 37, 0]], ![![-666, 37, 0], ![252, -32, 2]]]
 hmul := by decide  
 g := ![![![![22, 16, -1], ![37, 0, 0]], ![![-14, 1, 0], ![0, 0, 0]]], ![![![-18, 1, 0], ![0, 0, 0]], ![![-9, 16, -1], ![39, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![15, -16, 1]] ![![37, 0, 0], ![-5, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-185, 37, 0]], ![![555, -592, 37], ![37, 74, -37]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-5, 1, 0]]], ![![![15, -16, 1]], ![![1, 2, -1]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![25, 17, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![25, 17, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![25, 17, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![25, 17, 1], ![112, 4, 34], ![1904, -301, 4]]]
  hmulB := by decide  
  f := ![![![-24, -17, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -17, 41]], ![![0, 0, 1], ![-18, -14, 34], ![44, -9, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [30, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 40], [0, 1]]
 g := ![![[11, 9], [37], [37], [30, 4], [1]], ![[34, 32], [37], [37], [22, 37], [1]]]
 h' := ![![[39, 40], [39, 3], [1, 18], [2, 23], [11, 39], [0, 1]], ![[0, 1], [33, 38], [6, 23], [38, 18], [15, 2], [39, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [29, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [30, 2, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![254, 12, -21]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![19, 9, -21]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![7, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![7, 1, 0]] 
 ![![41, 0, 0], ![7, 1, 0], ![37, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![7, 1, 0], ![0, 7, 2], ![112, -21, 7]]]
  hmulB := by decide  
  f := ![![![29, 4, 0], ![-164, 0, 0]], ![![-7, -1, 0], ![42, 0, 0]], ![![33, 1, -1], ![-188, 21, 0]]]
  g := ![![![1, 0, 0], ![-7, 41, 0], ![-37, 0, 41]], ![![0, 1, 0], ![-3, 7, 2], ![0, -21, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![25, 17, 1]] ![![41, 0, 0], ![7, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![287, 41, 0]], ![![1025, 697, 41], ![287, 123, 41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![7, 1, 0]]], ![![![25, 17, 1]], ![![7, 3, 1]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![5, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![5, 1, 0]] 
 ![![43, 0, 0], ![5, 1, 0], ![9, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![5, 1, 0], ![0, 5, 2], ![112, -21, 5]]]
  hmulB := by decide  
  f := ![![![111, 22, 0], ![-946, 0, 0]], ![![5, 1, 0], ![-42, 0, 0]], ![![23, 2, -1], ![-196, 22, 0]]]
  g := ![![![1, 0, 0], ![-5, 43, 0], ![-9, 0, 43]], ![![0, 1, 0], ![-1, 5, 2], ![4, -21, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![13, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![13, 1, 0]] 
 ![![43, 0, 0], ![13, 1, 0], ![23, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![13, 1, 0], ![0, 13, 2], ![112, -21, 13]]]
  hmulB := by decide  
  f := ![![![105, 8, 0], ![-344, 0, 0]], ![![13, 1, 0], ![-42, 0, 0]], ![![61, -2, -1], ![-200, 22, 0]]]
  g := ![![![1, 0, 0], ![-13, 43, 0], ![-23, 0, 43]], ![![0, 1, 0], ![-5, 13, 2], ![2, -21, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-18, 1, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-18, 1, 0]] 
 ![![43, 0, 0], ![25, 1, 0], ![10, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-18, 1, 0], ![0, -18, 2], ![112, -21, -18]]]
  hmulB := by decide  
  f := ![![![361, -20, 0], ![860, 0, 0]], ![![199, -11, 0], ![474, 0, 0]], ![![94, 4, -1], ![224, 22, 0]]]
  g := ![![![1, 0, 0], ![-25, 43, 0], ![-10, 0, 43]], ![![-1, 1, 0], ![10, -18, 2], ![19, -21, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![5, 1, 0]] ![![43, 0, 0], ![13, 1, 0]]
  ![![43, 0, 0], ![11, 9, 1]] where
 M := ![![![1849, 0, 0], ![559, 43, 0]], ![![215, 43, 0], ![65, 18, 2]]]
 hmul := by decide  
 g := ![![![![32, -9, -1], ![43, 0, 0]], ![![2, -8, -1], ![43, 0, 0]]], ![![![-6, -8, -1], ![43, 0, 0]], ![![1, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![11, 9, 1]] ![![43, 0, 0], ![-18, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-774, 43, 0]], ![![473, 387, 43], ![-86, -172, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-18, 1, 0]]], ![![![11, 9, 1]], ![![-2, -4, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [21, 16, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 10, 34], [17, 36, 13], [0, 1]]
 g := ![![[45, 12, 4], [21, 22, 21], [32, 19, 2], [34, 12, 1], []], ![[12, 9, 11, 34], [40, 21, 1, 36], [11, 11, 1, 6], [20, 45, 4, 25], [29, 28]], ![[36, 20, 38, 23], [14, 21, 14, 13], [29, 38, 17, 11], [33, 6, 13, 31], [3, 28]]]
 h' := ![![[42, 10, 34], [29, 9, 45], [33, 16, 31], [38, 3, 7], [0, 0, 1], [0, 1]], ![[17, 36, 13], [24, 44, 46], [38, 27, 15], [24, 3, 25], [27, 23, 36], [42, 10, 34]], ![[0, 1], [12, 41, 3], [26, 4, 1], [26, 41, 15], [38, 24, 10], [17, 36, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4], []]
 b := ![[], [26, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [21, 16, 35, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![251591, -58656, -1598]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5353, -1248, -34]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-12, 13, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-12, 13, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![41, 13, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-12, 13, 1], ![112, -33, 26], ![1456, -217, -33]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -13, 53]], ![![-1, 0, 1], ![-18, -7, 26], ![53, 4, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [10, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 52], [0, 1]]
 g := ![![[41, 16], [37], [6, 16], [40], [14, 1]], ![[0, 37], [37], [18, 37], [40], [28, 52]]]
 h' := ![![[14, 52], [50, 4], [46, 14], [14, 49], [19, 27], [0, 1]], ![[0, 1], [0, 49], [30, 39], [11, 4], [26, 26], [14, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [13, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [10, 39, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1386, 9, 70]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28, -17, 70]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-26, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-26, 1, 0]] 
 ![![53, 0, 0], ![27, 1, 0], ![33, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-26, 1, 0], ![0, -26, 2], ![112, -21, -26]]]
  hmulB := by decide  
  f := ![![![1379, -53, 0], ![2809, 0, 0]], ![![729, -28, 0], ![1485, 0, 0]], ![![891, -21, -1], ![1815, 27, 0]]]
  g := ![![![1, 0, 0], ![-27, 53, 0], ![-33, 0, 53]], ![![-1, 1, 0], ![12, -26, 2], ![29, -21, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-12, 13, 1]] ![![53, 0, 0], ![-26, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-1378, 53, 0]], ![![-636, 689, 53], ![424, -371, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-26, 1, 0]]], ![![![-12, 13, 1]], ![![8, -7, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![16, -26, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![16, -26, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![16, 33, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![16, -26, 1], ![112, -5, -52], ![-2912, 602, -5]]]
  hmulB := by decide  
  f := ![![![-15, 26, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -33, 59]], ![![0, -1, 1], ![16, 29, -52], ![-48, 13, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [4, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 58], [0, 1]]
 g := ![![[3, 15], [31, 49], [4], [21, 12], [47, 1]], ![[0, 44], [33, 10], [4], [54, 47], [35, 58]]]
 h' := ![![[47, 58], [53, 29], [19, 52], [34, 57], [48, 22], [0, 1]], ![[0, 1], [0, 30], [44, 7], [58, 2], [20, 37], [47, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [46, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [4, 12, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-655, 644, -229]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![51, 139, -229]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-7, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-7, 1, 0]] 
 ![![59, 0, 0], ![52, 1, 0], ![5, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-7, 1, 0], ![0, -7, 2], ![112, -21, -7]]]
  hmulB := by decide  
  f := ![![![148, -21, 0], ![1239, 0, 0]], ![![134, -19, 0], ![1122, 0, 0]], ![![18, 1, -1], ![151, 30, 0]]]
  g := ![![![1, 0, 0], ![-52, 59, 0], ![-5, 0, 59]], ![![-1, 1, 0], ![6, -7, 2], ![21, -21, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![16, -26, 1]] ![![59, 0, 0], ![-7, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-413, 59, 0]], ![![944, -1534, 59], ![0, 177, -59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-7, 1, 0]]], ![![![16, -26, 1]], ![![0, 3, -1]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![39, 3, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![39, 3, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![39, 3, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![39, 3, 1], ![112, 18, 6], ![336, -7, 18]]]
  hmulB := by decide  
  f := ![![![-38, -3, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -3, 61]], ![![0, 0, 1], ![-2, 0, 6], ![-6, -1, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [23, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 60], [0, 1]]
 g := ![![[21, 48], [42], [19, 13], [48, 4], [5, 1]], ![[17, 13], [42], [23, 48], [7, 57], [10, 60]]]
 h' := ![![[5, 60], [49, 32], [51, 15], [55, 14], [7, 2], [0, 1]], ![[0, 1], [26, 29], [4, 46], [3, 47], [17, 59], [5, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [50, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [23, 56, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![247, -42, -75]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![52, 3, -75]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-6, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-6, 1, 0]] 
 ![![61, 0, 0], ![55, 1, 0], ![43, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-6, 1, 0], ![0, -6, 2], ![112, -21, -6]]]
  hmulB := by decide  
  f := ![![![319, -53, 0], ![3233, 0, 0]], ![![289, -48, 0], ![2929, 0, 0]], ![![229, -35, -1], ![2321, 31, 0]]]
  g := ![![![1, 0, 0], ![-55, 61, 0], ![-43, 0, 61]], ![![-1, 1, 0], ![4, -6, 2], ![25, -21, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![39, 3, 1]] ![![61, 0, 0], ![-6, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-366, 61, 0]], ![![2379, 183, 61], ![-122, 0, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-6, 1, 0]]], ![![![39, 3, 1]], ![![-2, 0, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-14, -4, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-14, -4, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![53, 63, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-14, -4, 1], ![112, -35, -8], ![-448, 140, -35]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-53, -63, 67]], ![![-1, -1, 1], ![8, 7, -8], ![21, 35, -35]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [32, 54, 1] where
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
 g := ![![[31, 49], [19, 4], [22], [22], [35], [1]], ![[65, 18], [4, 63], [22], [22], [35], [1]]]
 h' := ![![[13, 66], [62, 7], [42, 2], [3, 42], [38, 25], [35, 13], [0, 1]], ![[0, 1], [19, 60], [1, 65], [13, 25], [28, 42], [3, 54], [13, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [33, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [32, 54, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4343, 322, 757]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-534, -707, 757]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![8, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![8, 1, 0]] 
 ![![67, 0, 0], ![8, 1, 0], ![35, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![8, 1, 0], ![0, 8, 2], ![112, -21, 8]]]
  hmulB := by decide  
  f := ![![![273, 34, 0], ![-2278, 0, 0]], ![![24, 3, 0], ![-200, 0, 0]], ![![145, 14, -1], ![-1210, 34, 0]]]
  g := ![![![1, 0, 0], ![-8, 67, 0], ![-35, 0, 67]], ![![0, 1, 0], ![-2, 8, 2], ![0, -21, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-14, -4, 1]] ![![67, 0, 0], ![8, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![536, 67, 0]], ![![-938, -268, 67], ![0, -67, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![8, 1, 0]]], ![![![-14, -4, 1]], ![![0, -1, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-59, 19, -2]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-59, 19, -2]] 
 ![![71, 0, 0], ![19, 1, 0], ![68, 0, 1]] where
  M :=![![![-59, 19, -2], ![-224, -17, 38], ![2128, -511, -17]]]
  hmulB := by decide  
  f := ![![![19707, 1345, 688]], ![![6359, 434, 222]], ![![20996, 1433, 733]]]
  g := ![![![-4, 19, -2], ![-35, -17, 38], ![183, -511, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21655, 1478, 756]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![21655, 1478, 756]] 
 ![![71, 0, 0], ![55, 1, 0], ![14, 0, 1]] where
  M :=![![![21655, 1478, 756], ![84672, 5779, 2956], ![165536, 11298, 5779]]]
  hmulB := by decide  
  f := ![![![-47, -74, 44]], ![![33, -71, 32]], ![![-126, 42, -5]]]
  g := ![![![-989, 1478, 756], ![-3867, 5779, 2956], ![-7560, 11298, 5779]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-3, 1, 0]] 
 ![![71, 0, 0], ![68, 1, 0], ![31, 0, 1]] where
  M :=![![![-3, 1, 0], ![0, -3, 2], ![112, -21, -3]]]
  hmulB := by decide  
  f := ![![![51, 3, 2]], ![![52, 3, 2]], ![![27, 2, 1]]]
  g := ![![![-1, 1, 0], ![2, -3, 2], ![23, -21, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-59, 19, -2]] ![![21655, 1478, 756]]
  ![![51, 3, 2]] where
 M := ![![![51, 3, 2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![51, 3, 2]] ![![-3, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![27, 21, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![27, 21, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![27, 21, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![27, 21, 1], ![112, 6, 42], ![2352, -385, 6]]]
  hmulB := by decide  
  f := ![![![-26, -21, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -21, 73]], ![![0, 0, 1], ![-14, -12, 42], ![30, -7, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [24, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 72], [0, 1]]
 g := ![![[52, 70], [32], [50], [27, 49], [49], [1]], ![[0, 3], [32], [50], [49, 24], [49], [1]]]
 h' := ![![[66, 72], [27, 56], [49, 55], [9, 59], [57, 66], [49, 66], [0, 1]], ![[0, 1], [0, 17], [29, 18], [34, 14], [33, 7], [25, 7], [66, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [25, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [24, 7, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-654, 197, -8]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6, 5, -8]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![31, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![31, 1, 0]] 
 ![![73, 0, 0], ![31, 1, 0], ![67, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![31, 1, 0], ![0, 31, 2], ![112, -21, 31]]]
  hmulB := by decide  
  f := ![![![652, 21, 0], ![-1533, 0, 0]], ![![248, 8, 0], ![-583, 0, 0]], ![![612, 4, -1], ![-1439, 37, 0]]]
  g := ![![![1, 0, 0], ![-31, 73, 0], ![-67, 0, 73]], ![![0, 1, 0], ![-15, 31, 2], ![-18, -21, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![27, 21, 1]] ![![73, 0, 0], ![31, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![2263, 73, 0]], ![![1971, 1533, 73], ![949, 657, 73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![31, 1, 0]]], ![![![27, 21, 1]], ![![13, 9, 1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![23, -1, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![23, -1, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![23, 78, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![23, -1, 1], ![112, 2, -2], ![-112, 77, 2]]]
  hmulB := by decide  
  f := ![![![-22, 1, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -78, 79]], ![![0, -1, 1], ![2, 2, -2], ![-2, -1, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [42, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 78], [0, 1]]
 g := ![![[66, 32], [73, 5], [39, 13], [62, 64], [49], [1]], ![[0, 47], [38, 74], [27, 66], [9, 15], [49], [1]]]
 h' := ![![[72, 78], [15, 36], [21, 59], [3, 48], [22, 8], [37, 72], [0, 1]], ![[0, 1], [0, 43], [3, 20], [62, 31], [45, 71], [7, 7], [72, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [14, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [42, 7, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![490, 147, -68]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![26, 69, -68]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![2, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![2, 1, 0]] 
 ![![79, 0, 0], ![2, 1, 0], ![77, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![2, 1, 0], ![0, 2, 2], ![112, -21, 2]]]
  hmulB := by decide  
  f := ![![![77, 38, 0], ![-3002, 0, 0]], ![![-2, -1, 0], ![80, 0, 0]], ![![75, 36, -1], ![-2924, 40, 0]]]
  g := ![![![1, 0, 0], ![-2, 79, 0], ![-77, 0, 79]], ![![0, 1, 0], ![-2, 2, 2], ![0, -21, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![23, -1, 1]] ![![79, 0, 0], ![2, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![158, 79, 0]], ![![1817, -79, 79], ![158, 0, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![2, 1, 0]]], ![![![23, -1, 1]], ![![2, 0, 0]]]]
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


lemma PB182I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB182I1 : PrimesBelowBoundCertificateInterval O 31 79 182 where
  m := 11
  g := ![3, 2, 3, 1, 2, 2, 2, 2, 3, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB182I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
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
    · exact ![43, 43, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![71, 71, 71]
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
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N0, I37N1, I37N2, I41N1, I43N0, I43N1, I43N2, I53N1, I59N1, I61N1, I67N1, I71N0, I71N1, I71N2, I73N1, I79N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N1], [I43N0, I43N1, I43N2], [], [I53N1], [I59N1], [I61N1], [I67N1], [I71N0, I71N1, I71N2], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
