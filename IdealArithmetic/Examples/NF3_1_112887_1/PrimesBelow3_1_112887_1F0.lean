
import IdealArithmetic.Examples.NF3_1_112887_1.RI3_1_112887_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0]] 
 ![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 3 2 1 [1, 1, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 1], [0, 1, 1], [0, 1]]
 g := ![![[]], ![[0, 1]], ![[0, 1]]]
 h' := ![![[0, 0, 1], [0, 1]], ![[0, 1, 1], [0, 0, 1]], ![[0, 1], [0, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1], []]
 b := ![[], [1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 3
  hpos := by decide
  P := [1, 1, 0, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![478, 764, -538]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![239, 382, -269]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 8 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def PBC2 : ContainsPrimesAboveP 2 ![I2N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![2, 0, 0]]) timesTableT_eq_Table B_one_repr 2 (by decide) 𝕀


def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -1, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![2, -1, 0]] 
 ![![3, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![2, -1, 0], ![0, 2, -1], ![-53, 21, 2]]]
  hmulB := by decide  
  f := ![![![-25, -2, -1]], ![![-26, -2, -1]], ![![-52, -5, -2]]]
  g := ![![![1, -1, 0], ![0, 2, -1], ![-26, 21, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![2, -1, 0]] ![![2, -1, 0]]
  ![![4, -4, 1]] where
 M := ![![![4, -4, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![4, -4, 1]] ![![2, -1, 0]]
  ![![3, 0, 0]] where
 M := ![![![-45, 9, 6]]]
 hmul := by decide  
 g := ![![![![-15, 3, 2]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![12, -1, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![12, -1, 1]] 
 ![![5, 0, 0], ![0, 5, 0], ![2, 4, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![12, -1, 1], ![53, -9, -1], ![-53, 74, -9]]]
  hmulB := by decide  
  f := ![![![-11, 1, -1], ![5, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -4, 5]], ![![2, -1, 1], ![11, -1, -1], ![-7, 22, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [4, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 4], [0, 1]]
 g := ![![[2, 4], [1]], ![[0, 1], [1]]]
 h' := ![![[2, 4], [1, 2], [0, 1]], ![[0, 1], [0, 3], [2, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [4, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [4, 3, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-634, 727, -182]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-54, 291, -182]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![1, 1, 0]] 
 ![![5, 0, 0], ![1, 1, 0], ![4, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![1, 1, 0], ![0, 1, 1], ![53, -21, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 0], ![4, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 5, 0], ![-4, 0, 5]], ![![0, 1, 0], ![-1, 1, 1], ![14, -21, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![12, -1, 1]] ![![5, 0, 0], ![1, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![5, 5, 0]], ![![60, -5, 5], ![65, -10, 0]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![1, 1, 0]]], ![![![12, -1, 1]], ![![13, -2, 0]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [4, 1, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 0, 1], [5, 6, 6], [0, 1]]
 g := ![![[2, 0, 2], [1]], ![[4, 1, 0, 4], [5, 5, 4, 1]], ![[5, 5, 6, 6], [1, 6, 0, 6]]]
 h' := ![![[6, 0, 1], [3, 6, 4], [0, 1]], ![[5, 6, 6], [0, 3, 2], [6, 0, 1]], ![[0, 1], [2, 5, 1], [5, 6, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 6], []]
 b := ![[], [6, 4, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [4, 1, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-235977, -2681, -8344]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33711, -383, -1192]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![19, -3, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![19, -3, 1]] 
 ![![11, 0, 0], ![0, 11, 0], ![8, 8, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![19, -3, 1], ![53, -2, -3], ![-159, 116, -2]]]
  hmulB := by decide  
  f := ![![![-18, 3, -1], ![11, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -8, 11]], ![![1, -1, 1], ![7, 2, -3], ![-13, 12, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [9, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 10], [0, 1]]
 g := ![![[2, 5], [3, 5], [1]], ![[0, 6], [1, 6], [1]]]
 h' := ![![[4, 10], [6, 4], [2, 4], [0, 1]], ![[0, 1], [0, 7], [7, 7], [4, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [2, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [9, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-301, 612, -215]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![129, 212, -215]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![3, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![3, 1, 0]] 
 ![![11, 0, 0], ![3, 1, 0], ![2, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![3, 1, 0], ![0, 3, 1], ![53, -21, 3]]]
  hmulB := by decide  
  f := ![![![7, 2, 0], ![-22, 0, 0]], ![![-3, -1, 0], ![12, 0, 0]], ![![-2, -1, 0], ![8, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 11, 0], ![-2, 0, 11]], ![![0, 1, 0], ![-1, 3, 1], ![10, -21, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![19, -3, 1]] ![![11, 0, 0], ![3, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![33, 11, 0]], ![![209, -33, 11], ![110, -11, 0]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![3, 1, 0]]], ![![![19, -3, 1]], ![![10, -1, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![17, -3, 1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![17, -3, 1]] 
 ![![13, 0, 0], ![0, 13, 0], ![4, 10, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![17, -3, 1], ![53, -4, -3], ![-159, 116, -4]]]
  hmulB := by decide  
  f := ![![![-16, 3, -1], ![13, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -10, 13]], ![![1, -1, 1], ![5, 2, -3], ![-11, 12, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [6, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 12], [0, 1]]
 g := ![![[5, 4], [9], [9, 1]], ![[2, 9], [9], [5, 12]]]
 h' := ![![[9, 12], [2, 2], [11, 10], [0, 1]], ![[0, 1], [7, 11], [10, 3], [9, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [7, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [6, 4, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![112, 7, -24]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16, 19, -24]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![3, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![3, 1, 0]] 
 ![![13, 0, 0], ![3, 1, 0], ![4, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![3, 1, 0], ![0, 3, 1], ![53, -21, 3]]]
  hmulB := by decide  
  f := ![![![16, 5, 0], ![-65, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![4, 1, 0], ![-16, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 13, 0], ![-4, 0, 13]], ![![0, 1, 0], ![-1, 3, 1], ![8, -21, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![17, -3, 1]] ![![13, 0, 0], ![3, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![39, 13, 0]], ![![221, -39, 13], ![104, -13, 0]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![3, 1, 0]]], ![![![17, -3, 1]], ![![8, -1, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![6, 6, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![6, 6, 1]] 
 ![![17, 0, 0], ![0, 17, 0], ![6, 6, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![6, 6, 1], ![53, -15, 6], ![318, -73, -15]]]
  hmulB := by decide  
  f := ![![![-5, -6, -1], ![17, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -6, 17]], ![![0, 0, 1], ![1, -3, 6], ![24, 1, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [1, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 16], [0, 1]]
 g := ![![[3, 1], [16], [9], [1]], ![[0, 16], [16], [9], [1]]]
 h' := ![![[14, 16], [14, 16], [9, 13], [16, 14], [0, 1]], ![[0, 1], [0, 1], [4, 4], [8, 3], [14, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [13, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [1, 3, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2019, -650, 345]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, -160, 345]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-6, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-6, 1, 0]] 
 ![![17, 0, 0], ![11, 1, 0], ![15, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-6, 1, 0], ![0, -6, 1], ![53, -21, -6]]]
  hmulB := by decide  
  f := ![![![31, -5, 0], ![85, 0, 0]], ![![25, -4, 0], ![69, 0, 0]], ![![33, -5, 0], ![91, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 17, 0], ![-15, 0, 17]], ![![-1, 1, 0], ![3, -6, 1], ![22, -21, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![6, 6, 1]] ![![17, 0, 0], ![-6, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![-102, 17, 0]], ![![102, 102, 17], ![17, -51, 0]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![-6, 1, 0]]], ![![![6, 6, 1]], ![![1, -3, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-8, 1, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-8, 1, 0]] 
 ![![19, 0, 0], ![11, 1, 0], ![12, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-8, 1, 0], ![0, -8, 1], ![53, -21, -8]]]
  hmulB := by decide  
  f := ![![![129, -16, 0], ![304, 0, 0]], ![![73, -9, 0], ![172, 0, 0]], ![![84, -10, 0], ![198, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 19, 0], ![-12, 0, 19]], ![![-1, 1, 0], ![4, -8, 1], ![20, -21, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-7, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-7, 1, 0]] 
 ![![19, 0, 0], ![12, 1, 0], ![8, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-7, 1, 0], ![0, -7, 1], ![53, -21, -7]]]
  hmulB := by decide  
  f := ![![![106, -15, 0], ![285, 0, 0]], ![![64, -9, 0], ![172, 0, 0]], ![![52, -7, 0], ![140, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 19, 0], ![-8, 0, 19]], ![![-1, 1, 0], ![4, -7, 1], ![19, -21, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-4, 1, 0]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-4, 1, 0]] 
 ![![19, 0, 0], ![15, 1, 0], ![3, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-4, 1, 0], ![0, -4, 1], ![53, -21, -4]]]
  hmulB := by decide  
  f := ![![![29, -7, 0], ![133, 0, 0]], ![![25, -6, 0], ![115, 0, 0]], ![![5, -1, 0], ![23, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 19, 0], ![-3, 0, 19]], ![![-1, 1, 0], ![3, -4, 1], ![20, -21, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![-8, 1, 0]] ![![19, 0, 0], ![-7, 1, 0]]
  ![![19, 0, 0], ![18, 4, 1]] where
 M := ![![![361, 0, 0], ![-133, 19, 0]], ![![-152, 19, 0], ![56, -15, 1]]]
 hmul := by decide  
 g := ![![![![1, -4, -1], ![19, 0, 0]], ![![-7, 1, 0], ![0, 0, 0]]], ![![![-8, 1, 0], ![0, 0, 0]], ![![-16, -5, -1], ![20, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![18, 4, 1]] ![![19, 0, 0], ![-4, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-76, 19, 0]], ![![342, 76, 19], ![-19, -19, 0]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-4, 1, 0]]], ![![![18, 4, 1]], ![![-1, -1, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![24, 7, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![24, 7, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![1, 7, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![24, 7, 1], ![53, 3, 7], ![371, -94, 3]]]
  hmulB := by decide  
  f := ![![![-23, -7, -1], ![23, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -7, 23]], ![![1, 0, 1], ![2, -2, 7], ![16, -5, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [8, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 22], [0, 1]]
 g := ![![[3, 3], [2, 2], [15, 1], [1]], ![[0, 20], [0, 21], [14, 22], [1]]]
 h' := ![![[22, 22], [7, 7], [18, 18], [15, 22], [0, 1]], ![[0, 1], [0, 16], [0, 5], [16, 1], [22, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [3, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [8, 1, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-310, 176, -11]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13, 11, -11]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-7, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-7, 1, 0]] 
 ![![23, 0, 0], ![16, 1, 0], ![20, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-7, 1, 0], ![0, -7, 1], ![53, -21, -7]]]
  hmulB := by decide  
  f := ![![![99, -14, 0], ![322, 0, 0]], ![![78, -11, 0], ![254, 0, 0]], ![![94, -13, 0], ![306, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 23, 0], ![-20, 0, 23]], ![![-1, 1, 0], ![4, -7, 1], ![23, -21, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![24, 7, 1]] ![![23, 0, 0], ![-7, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![-161, 23, 0]], ![![552, 161, 23], ![-115, -46, 0]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![-7, 1, 0]]], ![![![24, 7, 1]], ![![-5, -2, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![16, -13, 1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![16, -13, 1]] 
 ![![29, 0, 0], ![0, 29, 0], ![16, 16, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![16, -13, 1], ![53, -5, -13], ![-689, 326, -5]]]
  hmulB := by decide  
  f := ![![![-15, 13, -1], ![29, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -16, 29]], ![![0, -1, 1], ![9, 7, -13], ![-21, 14, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [6, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 28], [0, 1]]
 g := ![![[15, 5], [4], [23, 9], [26, 1]], ![[0, 24], [4], [25, 20], [23, 28]]]
 h' := ![![[26, 28], [25, 18], [7, 27], [18, 3], [0, 1]], ![[0, 1], [0, 11], [13, 2], [9, 26], [26, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [6, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [6, 3, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![218, 131, -77]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![50, 47, -77]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![13, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![13, 1, 0]] 
 ![![29, 0, 0], ![13, 1, 0], ![5, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![13, 1, 0], ![0, 13, 1], ![53, -21, 13]]]
  hmulB := by decide  
  f := ![![![66, 5, 0], ![-145, 0, 0]], ![![26, 2, 0], ![-57, 0, 0]], ![![6, 0, 0], ![-13, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 29, 0], ![-5, 0, 29]], ![![0, 1, 0], ![-6, 13, 1], ![9, -21, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![16, -13, 1]] ![![29, 0, 0], ![13, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![377, 29, 0]], ![![464, -377, 29], ![261, -174, 0]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![13, 1, 0]]], ![![![16, -13, 1]], ![![9, -6, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22, 1, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![22, 1, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![22, 1, 1]] where
  M :=![![![22, 1, 1], ![53, 1, 1], ![53, 32, 1]]]
  hmulB := by decide  
  f := ![![![-1, 1, 0]], ![![0, -1, 1]], ![![1, 0, 0]]]
  g := ![![![0, 0, 1], ![1, 0, 1], ![1, 1, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [26, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 30], [0, 1]]
 g := ![![[29, 5], [7, 8], [26, 20], [21, 1]], ![[10, 26], [20, 23], [12, 11], [11, 30]]]
 h' := ![![[21, 30], [4, 6], [6, 15], [12, 12], [0, 1]], ![[0, 1], [6, 25], [11, 16], [16, 19], [21, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [18, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [26, 10, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2070, 912, 44]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-98, 28, 44]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-1, 1, 0]] 
 ![![31, 0, 0], ![30, 1, 0], ![30, 0, 1]] where
  M :=![![![-1, 1, 0], ![0, -1, 1], ![53, -21, -1]]]
  hmulB := by decide  
  f := ![![![22, 1, 1]], ![![23, 1, 1]], ![![23, 2, 1]]]
  g := ![![![-1, 1, 0], ![0, -1, 1], ![23, -21, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![22, 1, 1]] ![![-1, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![31, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)


lemma PB96I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB96I0 : PrimesBelowBoundCertificateInterval O 1 31 96 where
  m := 11
  g := ![1, 3, 2, 1, 2, 2, 2, 3, 2, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB96I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N1]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![8]
    · exact ![3, 3, 3]
    · exact ![25, 5]
    · exact ![343]
    · exact ![121, 11]
    · exact ![169, 13]
    · exact ![289, 17]
    · exact ![19, 19, 19]
    · exact ![529, 23]
    · exact ![841, 29]
    · exact ![961, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I3N0, I5N0, I5N1, I11N1, I13N1, I17N1, I19N0, I19N1, I19N2, I23N1, I29N1, I31N1]
  Il := ![[I2N0], [I3N0, I3N0, I3N0], [I5N0, I5N1], [], [I11N1], [I13N1], [I17N1], [I19N0, I19N1, I19N2], [I23N1], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
