
import IdealArithmetic.Examples.NF3_1_466796_1.RI3_1_466796_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![1, 1, 0]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![1, 1, 0], ![0, 1, 1], ![-679, 137, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![1, -1, 0]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![-1, 0, 2]], ![![0, 1, 0], ![-1, 1, 1], ![-409, 137, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0], ![-93, 6, 1]] where
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![2, 2, 0], ![1, 2, 1]]]
 hmul := by decide  
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0]]], ![![![1, 1, 0], ![0, 0, 0]], ![![47, -2, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![-93, 6, 1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![-186, 12, 2], ![-772, 50, 8]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![1, 1, 0]]], ![![![-93, 6, 1]], ![![-386, 25, 4]]]]
 hle2 := by decide  

def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [1, 2, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 1], [1, 1], [0, 1]]
 g := ![![[1]], ![[1]], ![[1]]]
 h' := ![![[2, 1], [0, 1]], ![[1, 1], [2, 1]], ![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], []]
 b := ![[], [2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [1, 2, 0, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9507, 95856, -17028]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3169, 31952, -5676]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 27 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def PBC3 : ContainsPrimesAboveP 3 ![I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![3, 0, 0]]) timesTableT_eq_Table B_one_repr 3 (by decide) 𝕀

instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0]] 
 ![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [1, 2, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 4, 4], [3, 0, 1], [0, 1]]
 g := ![![[3, 0, 1], []], ![[0, 4], [2, 1]], ![[3, 4, 2, 1], [0, 1]]]
 h' := ![![[2, 4, 4], [0, 0, 1], [0, 1]], ![[3, 0, 1], [2, 1], [2, 4, 4]], ![[0, 1], [4, 4, 4], [3, 0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 3], []]
 b := ![[], [1, 3, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [1, 2, 0, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12441315, -5009660, 504310]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2488263, -1001932, 100862]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 125 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def PBC5 : ContainsPrimesAboveP 5 ![I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![5, 0, 0]]) timesTableT_eq_Table B_one_repr 5 (by decide) 𝕀

instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![0, 1, 0]] 
 ![![7, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![0, 0, 1], ![-679, 137, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![0, 0, 1], ![-97, 137, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-95, 6, 1]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-95, 6, 1]] 
 ![![7, 0, 0], ![0, 7, 0], ![3, 6, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-95, 6, 1], ![-679, 42, 7], ![-4753, 280, 49]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![14, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -6, 7]], ![![-14, 0, 1], ![-100, 0, 7], ![-700, -2, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [1, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 6], [0, 1]]
 g := ![![[3, 1], [4, 1]], ![[0, 6], [1, 6]]]
 h' := ![![[4, 6], [3, 1], [0, 1]], ![[0, 1], [0, 6], [4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [5, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [1, 3, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2032, -5695, 1222]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-814, -1861, 1222]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![0, 1, 0]] ![![7, 0, 0], ![-95, 6, 1]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![-665, 42, 7]], ![![0, 7, 0], ![-679, 42, 7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![-95, 6, 1]]], ![![![0, 1, 0]], ![![-97, 6, 1]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![1, 1, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![1, 1, 0]] 
 ![![11, 0, 0], ![1, 1, 0], ![10, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![1, 1, 0], ![0, 1, 1], ![-679, 137, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![11, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 0], ![10, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 11, 0], ![-10, 0, 11]], ![![0, 1, 0], ![-1, 1, 1], ![-76, 137, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-3, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-3, 1, 0]] 
 ![![11, 0, 0], ![8, 1, 0], ![2, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-3, 1, 0], ![0, -3, 1], ![-679, 137, -2]]]
  hmulB := by decide  
  f := ![![![19, -6, 0], ![66, 0, 0]], ![![16, -5, 0], ![56, 0, 0]], ![![4, -1, 0], ![14, 1, 0]]]
  g := ![![![1, 0, 0], ![-8, 11, 0], ![-2, 0, 11]], ![![-1, 1, 0], ![2, -3, 1], ![-161, 137, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![1, 1, 0]] ![![11, 0, 0], ![1, 1, 0]]
  ![![11, 0, 0], ![-98, 2, 1]] where
 M := ![![![121, 0, 0], ![11, 11, 0]], ![![11, 11, 0], ![1, 2, 1]]]
 hmul := by decide  
 g := ![![![![11, 0, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0]]], ![![![1, 1, 0], ![0, 0, 0]], ![![9, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI11N1 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![-98, 2, 1]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![-33, 11, 0]], ![![-1078, 22, 11], ![-385, 33, 0]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![-3, 1, 0]]], ![![![-98, 2, 1]], ![![-35, 3, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-92, 2, 1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-92, 2, 1]] 
 ![![13, 0, 0], ![0, 13, 0], ![12, 2, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-92, 2, 1], ![-679, 45, 3], ![-2037, -268, 48]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![8, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -2, 13]], ![![-8, 0, 1], ![-55, 3, 3], ![-201, -28, 48]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [2, 4, 1] where
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
 g := ![![[2, 1], [1], [9, 1]], ![[11, 12], [1], [5, 12]]]
 h' := ![![[9, 12], [10, 12], [8, 1], [0, 1]], ![[0, 1], [1, 1], [4, 12], [9, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [6, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [2, 4, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2035, -272, 137]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-283, -42, 137]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-3, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-3, 1, 0]] 
 ![![13, 0, 0], ![10, 1, 0], ![4, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-3, 1, 0], ![0, -3, 1], ![-679, 137, -2]]]
  hmulB := by decide  
  f := ![![![34, -11, 0], ![143, 0, 0]], ![![28, -9, 0], ![118, 0, 0]], ![![10, -3, 0], ![42, 1, 0]]]
  g := ![![![1, 0, 0], ![-10, 13, 0], ![-4, 0, 13]], ![![-1, 1, 0], ![2, -3, 1], ![-157, 137, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![-92, 2, 1]] ![![13, 0, 0], ![-3, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![-39, 13, 0]], ![![-1196, 26, 13], ![-403, 39, 0]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![-3, 1, 0]]], ![![![-92, 2, 1]], ![![-31, 3, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-91, 13, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-91, 13, 1]] 
 ![![17, 0, 0], ![0, 17, 0], ![11, 13, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-91, 13, 1], ![-679, 46, 14], ![-9506, 1239, 60]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![6, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -13, 17]], ![![-6, 0, 1], ![-49, -8, 14], ![-598, 27, 60]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [1, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 16], [0, 1]]
 g := ![![[13, 1], [8], [16], [1]], ![[0, 16], [8], [16], [1]]]
 h' := ![![[4, 16], [13, 1], [2, 5], [16, 4], [0, 1]], ![[0, 1], [0, 16], [5, 12], [15, 13], [4, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [6, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [1, 13, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26466, 4949, 552]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1914, -131, 552]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![3, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![3, 1, 0]] 
 ![![17, 0, 0], ![3, 1, 0], ![8, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![3, 1, 0], ![0, 3, 1], ![-679, 137, 4]]]
  hmulB := by decide  
  f := ![![![13, 4, 0], ![-68, 0, 0]], ![![-3, -1, 0], ![18, 0, 0]], ![![4, 1, 0], ![-20, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 17, 0], ![-8, 0, 17]], ![![0, 1, 0], ![-1, 3, 1], ![-66, 137, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![-91, 13, 1]] ![![17, 0, 0], ![3, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![51, 17, 0]], ![![-1547, 221, 17], ![-952, 85, 17]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![3, 1, 0]]], ![![![-91, 13, 1]], ![![-56, 5, 1]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-85, 9, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-85, 9, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![10, 9, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-85, 9, 1], ![-679, 52, 10], ![-6790, 691, 62]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![5, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -9, 19]], ![![-5, 0, 1], ![-41, -2, 10], ![-390, 7, 62]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [17, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 18], [0, 1]]
 g := ![![[12, 9], [2, 11], [6], [1]], ![[0, 10], [0, 8], [6], [1]]]
 h' := ![![[5, 18], [4, 3], [16, 12], [2, 5], [0, 1]], ![[0, 1], [0, 16], [0, 7], [8, 14], [5, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [18, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [17, 14, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3399, -1328, 129]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![111, -131, 129]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![9, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![9, 1, 0]] 
 ![![19, 0, 0], ![9, 1, 0], ![14, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![9, 1, 0], ![0, 9, 1], ![-679, 137, 10]]]
  hmulB := by decide  
  f := ![![![46, 5, 0], ![-95, 0, 0]], ![![18, 2, 0], ![-37, 0, 0]], ![![32, 3, 0], ![-66, 1, 0]]]
  g := ![![![1, 0, 0], ![-9, 19, 0], ![-14, 0, 19]], ![![0, 1, 0], ![-5, 9, 1], ![-108, 137, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![-85, 9, 1]] ![![19, 0, 0], ![9, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![171, 19, 0]], ![![-1615, 171, 19], ![-1444, 133, 19]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![9, 1, 0]]], ![![![-85, 9, 1]], ![![-76, 7, 1]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [13, 14, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 20, 1], [22, 2, 22], [0, 1]]
 g := ![![[0, 3, 9], [19, 20, 12], [10, 22, 1], []], ![[16, 17, 2, 18], [17, 12, 5, 3], [4, 2, 2, 4], [16, 1]], ![[22, 10, 16, 17], [11, 16, 10, 20], [1, 12, 0, 14], [18, 1]]]
 h' := ![![[0, 20, 1], [6, 21, 20], [8, 11, 14], [0, 0, 1], [0, 1]], ![[22, 2, 22], [9, 4, 15], [17, 7, 16], [22, 16, 2], [0, 20, 1]], ![[0, 1], [17, 21, 11], [1, 5, 16], [20, 7, 20], [22, 2, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 7], []]
 b := ![[], [4, 18, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [13, 14, 1, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1059932, -978397, 139150]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![46084, -42539, 6050]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀

instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-105, 19, 1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-105, 19, 1]] 
 ![![29, 0, 0], ![0, 29, 0], ![11, 19, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-105, 19, 1], ![-679, 32, 20], ![-13580, 2061, 52]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![4, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -19, 29]], ![![-4, 0, 1], ![-31, -12, 20], ![-488, 37, 52]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [22, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 28], [0, 1]]
 g := ![![[21, 4], [9], [28, 5], [2, 1]], ![[0, 25], [9], [9, 24], [4, 28]]]
 h' := ![![[2, 28], [25, 2], [22, 26], [14, 11], [0, 1]], ![[0, 1], [0, 27], [16, 3], [7, 18], [2, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [20, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [22, 27, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24524, -7958, 674]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![590, -716, 674]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![9, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![9, 1, 0]] 
 ![![29, 0, 0], ![9, 1, 0], ![6, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![9, 1, 0], ![0, 9, 1], ![-679, 137, 10]]]
  hmulB := by decide  
  f := ![![![82, 9, 0], ![-261, 0, 0]], ![![18, 2, 0], ![-57, 0, 0]], ![![12, 1, 0], ![-38, 1, 0]]]
  g := ![![![1, 0, 0], ![-9, 29, 0], ![-6, 0, 29]], ![![0, 1, 0], ![-3, 9, 1], ![-68, 137, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![-105, 19, 1]] ![![29, 0, 0], ![9, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![261, 29, 0]], ![![-3045, 551, 29], ![-1624, 203, 29]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![9, 1, 0]]], ![![![-105, 19, 1]], ![![-56, 7, 1]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![3, 1, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![3, 1, 0]] 
 ![![31, 0, 0], ![3, 1, 0], ![22, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![3, 1, 0], ![0, 3, 1], ![-679, 137, 4]]]
  hmulB := by decide  
  f := ![![![52, 17, 0], ![-527, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![34, 11, 0], ![-344, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 31, 0], ![-22, 0, 31]], ![![0, 1, 0], ![-1, 3, 1], ![-38, 137, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![4, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![4, 1, 0]] 
 ![![31, 0, 0], ![4, 1, 0], ![15, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![4, 1, 0], ![0, 4, 1], ![-679, 137, 5]]]
  hmulB := by decide  
  f := ![![![25, 6, 0], ![-186, 0, 0]], ![![-4, -1, 0], ![32, 0, 0]], ![![9, 2, 0], ![-66, 1, 0]]]
  g := ![![![1, 0, 0], ![-4, 31, 0], ![-15, 0, 31]], ![![0, 1, 0], ![-1, 4, 1], ![-42, 137, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, -1, 0]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![8, -1, 0]] 
 ![![31, 0, 0], ![23, 1, 0], ![29, 0, 1]] where
  M :=![![![8, -1, 0], ![0, 8, -1], ![679, -137, 7]]]
  hmulB := by decide  
  f := ![![![-81, 7, 1]], ![![-82, 7, 1]], ![![-251, 20, 3]]]
  g := ![![![1, -1, 0], ![-5, 8, -1], ![117, -137, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![3, 1, 0]] ![![31, 0, 0], ![4, 1, 0]]
  ![![-81, 7, 1]] where
 M := ![![![961, 0, 0], ![124, 31, 0]], ![![93, 31, 0], ![12, 7, 1]]]
 hmul := by decide  
 g := ![![![![248, -31, 0]], ![![32, 4, -1]]], ![![![24, 5, -1]], ![![25, -3, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-81, 7, 1]] ![![8, -1, 0]]
  ![![31, 0, 0]] where
 M := ![![![31, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)


lemma PB194I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB194I0 : PrimesBelowBoundCertificateInterval O 1 31 194 where
  m := 11
  g := ![3, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB194I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0]
    · exact ![I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1, I31N2]
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
    · exact ![2, 2, 2]
    · exact ![27]
    · exact ![125]
    · exact ![7, 49]
    · exact ![11, 11, 11]
    · exact ![169, 13]
    · exact ![289, 17]
    · exact ![361, 19]
    · exact ![12167]
    · exact ![841, 29]
    · exact ![31, 31, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N0
      exact NI2N0
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
  β := ![I2N0, I3N0, I5N0, I7N0, I7N1, I11N0, I11N1, I13N0, I13N1, I17N1, I19N1, I29N1, I31N0, I31N1, I31N2]
  Il := ![[I2N0, I2N0, I2N0], [I3N0], [I5N0], [I7N0, I7N1], [I11N0, I11N0, I11N1], [I13N0, I13N1], [I17N1], [I19N1], [], [I29N1], [I31N0, I31N1, I31N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
