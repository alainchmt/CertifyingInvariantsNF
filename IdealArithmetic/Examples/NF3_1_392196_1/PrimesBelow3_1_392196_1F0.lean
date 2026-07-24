
import IdealArithmetic.Examples.NF3_1_392196_1.RI3_1_392196_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![14, 1, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![14, 1, 1]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![14, 1, 1], ![82, -10, 8], ![126, -16, -5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![-14, 12, 6], ![-7, 0, 1]], ![![-7, -13, -7], ![10, 0, -1]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![7, 1, 1], ![41, -10, 8], ![63, -16, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![15, 0, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![15, 0, 1]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![15, 0, 1], ![80, -7, 2], ![46, 6, -6]]]
  hmulB := by decide  
  f := ![![![-14, 0, -1], ![2, 0, 0]], ![![-10, 4, 1], ![-4, 1, 0]], ![![-7, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![-1, 0, 2]], ![![7, 0, 1], ![39, -7, 2], ![26, 6, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![14, 1, 1]] ![![2, 0, 0], ![14, 1, 1]]
  ![![2, 0, 0], ![14, 0, 1]] where
 M := ![![![4, 0, 0], ![28, 2, 2]], ![![28, 2, 2], ![404, -12, 17]]]
 hmul := by decide  
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![2, 0, 0]]], ![![![0, 1, 0], ![2, 0, 0]], ![![-1, -6, -6], ![29, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![14, 0, 1]] ![![2, 0, 0], ![15, 0, 1]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![30, 0, 2]], ![![28, 0, 2], ![256, 6, 8]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![15, 0, 1]]], ![![![14, 0, 1]], ![![128, 3, 4]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![14, 0, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![14, 0, 1]] 
 ![![3, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![14, 0, 1], ![80, -8, 2], ![46, 6, -7]]]
  hmulB := by decide  
  f := ![![![-13, 0, -1], ![3, 0, 0]], ![![-3, 3, 1], ![-5, 1, 0]], ![![-4, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![-1, 3, 0], ![-2, 0, 3]], ![![4, 0, 1], ![28, -8, 2], ![18, 6, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![15, -1, 1]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![15, -1, 1]] 
 ![![3, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![15, -1, 1], ![78, -5, -4], ![-34, 28, -8]]]
  hmulB := by decide  
  f := ![![![-6, -51, 11], ![15, 0, 6]], ![![-12, -16, 3], ![7, 0, 2]], ![![-2, -17, 4], ![5, 0, 2]]]
  g := ![![![1, 0, 0], ![-1, 3, 0], ![-1, 0, 3]], ![![5, -1, 1], ![29, -5, -4], ![-18, 28, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![14, 0, 1]] ![![3, 0, 0], ![15, -1, 1]]
  ![![3, 0, 0], ![1, 1, 0]] where
 M := ![![![9, 0, 0], ![45, -3, 3]], ![![42, 0, 3], ![176, 14, 6]]]
 hmul := by decide  
 g := ![![![![2, -1, 0], ![3, 0, 0]], ![![13, -3, 1], ![6, 0, 0]]], ![![![12, -2, 1], ![6, 0, 0]], ![![52, -2, 2], ![20, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![15, -1, 1]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![45, -3, 3]], ![![3, 3, 0], ![93, -6, -3]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![15, -1, 1]]], ![![![1, 1, 0]], ![![31, -2, -1]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [2, 1, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 3, 2], [1, 1, 3], [0, 1]]
 g := ![![[0, 1, 1], []], ![[2, 2, 4, 2], [1, 4]], ![[3, 0, 3, 2], [0, 4]]]
 h' := ![![[0, 3, 2], [0, 0, 1], [0, 1]], ![[1, 1, 3], [3, 1, 1], [0, 3, 2]], ![[0, 1], [1, 4, 3], [1, 1, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 4], []]
 b := ![[], [2, 0, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [2, 1, 4, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13540, 7020, -13650]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2708, 1404, -2730]
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


def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![0, 1, 0]] 
 ![![7, 0, 0], ![0, 1, 0], ![5, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![2, -2, 6], ![80, -22, 2]]]
  hmulB := by decide  
  f := ![![![-7, 7, -24], ![7, 28, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-5, 5, -17], ![5, 20, 0]]]
  g := ![![![1, 0, 0], ![0, 7, 0], ![-5, 0, 7]], ![![0, 1, 0], ![-4, -2, 6], ![10, -22, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![0, 1, 0]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0], ![12, 2, 1]] where
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![0, 7, 0], ![2, -2, 6]]]
 hmul := by decide  
 g := ![![![![-5, -2, -1], ![7, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-10, -2, 0], ![6, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![12, 2, 1]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![84, 14, 7], ![84, -14, 14]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![0, 1, 0]]], ![![![12, 2, 1]], ![![12, -2, 2]]]]
 hle2 := by decide  

def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N0, I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N0
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0]] 
 ![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [7, 7, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 1, 2], [10, 9, 9], [0, 1]]
 g := ![![[9, 2, 3], [8, 2, 1], []], ![[10, 0, 4, 8], [5, 9, 10, 8], [1, 4]], ![[5, 10, 6, 4], [5, 10, 10, 9], [5, 4]]]
 h' := ![![[3, 1, 2], [10, 7, 6], [0, 0, 1], [0, 1]], ![[10, 9, 9], [10, 9, 2], [2, 4, 9], [3, 1, 2]], ![[0, 1], [8, 6, 3], [10, 7, 1], [10, 9, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10], []]
 b := ![[], [10, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [7, 7, 9, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1011307, -368819, 93467]
  a := ![2, -5, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![91937, -33529, 8497]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [10, 7, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 0, 4], [1, 12, 9], [0, 1]]
 g := ![![[1, 12, 10], [8, 3], [1]], ![[0, 8, 1, 3], [0, 10], [6, 5, 9, 12]], ![[3, 8, 11, 4], [9, 4], [6, 9, 8, 1]]]
 h' := ![![[3, 0, 4], [7, 2, 6], [3, 6, 4], [0, 1]], ![[1, 12, 9], [10, 5, 2], [6, 12, 7], [3, 0, 4]], ![[0, 1], [11, 6, 5], [6, 8, 2], [1, 12, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 12], []]
 b := ![[], [0, 7, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [10, 7, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![781375465, 609680474, -1056500731]
  a := ![-65, 2, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![60105805, 46898498, -81269287]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![0, 1, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![0, 1, 0]] 
 ![![17, 0, 0], ![0, 1, 0], ![6, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![0, 1, 0], ![2, -2, 6], ![80, -22, 2]]]
  hmulB := by decide  
  f := ![![![-17, 17, -54], ![17, 153, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-6, 6, -19], ![6, 54, 0]]]
  g := ![![![1, 0, 0], ![0, 17, 0], ![-6, 0, 17]], ![![0, 1, 0], ![-2, -2, 6], ![4, -22, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![10, -6, 1]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![10, -6, 1]] 
 ![![17, 0, 0], ![0, 17, 0], ![10, 11, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![10, -6, 1], ![68, 0, -34], ![-434, 138, -23]]]
  hmulB := by decide  
  f := ![![![-9, 6, -1], ![17, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -11, 17]], ![![0, -1, 1], ![24, 22, -34], ![-12, 23, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [10, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 16], [0, 1]]
 g := ![![[], [], [], [1]], ![[], [], [], [1]]]
 h' := ![![[0, 16], [4], [15], [7], [0, 1]], ![[0, 1], [4], [15], [7], [0, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [0, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [10, 0, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2180, 1478, -1017]
  a := ![-2, 4, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![470, 745, -1017]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![0, 1, 0]] ![![17, 0, 0], ![10, -6, 1]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![170, -102, 17]], ![![0, 17, 0], ![68, 0, -34]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![10, -6, 1]]], ![![![0, 1, 0]], ![![4, 0, -2]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![19, -2, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![19, -2, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![0, 17, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![19, -2, 1], ![76, 1, -10], ![-114, 50, -6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -17, 19]], ![![1, -1, 1], ![4, 9, -10], ![-6, 8, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [8, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 18], [0, 1]]
 g := ![![[3, 6], [6, 11], [6], [1]], ![[11, 13], [8, 8], [6], [1]]]
 h' := ![![[14, 18], [9, 5], [16, 12], [11, 14], [0, 1]], ![[0, 1], [3, 14], [13, 7], [17, 5], [14, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [17, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [8, 5, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![418, 54, -198]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![22, 180, -198]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-9, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-9, 1, 0]] 
 ![![19, 0, 0], ![10, 1, 0], ![6, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-9, 1, 0], ![2, -11, 6], ![80, -22, -7]]]
  hmulB := by decide  
  f := ![![![-37, 306, -168], ![38, 532, 0]], ![![-18, 153, -84], ![20, 266, 0]], ![![-6, 96, -53], ![24, 168, 0]]]
  g := ![![![1, 0, 0], ![-10, 19, 0], ![-6, 0, 19]], ![![-1, 1, 0], ![4, -11, 6], ![18, -22, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![19, -2, 1]] ![![19, 0, 0], ![-9, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-171, 19, 0]], ![![361, -38, 19], ![-95, 19, -19]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-9, 1, 0]]], ![![![19, -2, 1]], ![![-5, 1, -1]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![2, 1, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![2, 1, 0]] 
 ![![23, 0, 0], ![2, 1, 0], ![8, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![2, 1, 0], ![2, 0, 6], ![80, -22, 4]]]
  hmulB := by decide  
  f := ![![![525, -2, 1584], ![46, -6072, 0]], ![![42, -1, 132], ![24, -506, 0]], ![![182, -1, 551], ![23, -2112, 0]]]
  g := ![![![1, 0, 0], ![-2, 23, 0], ![-8, 0, 23]], ![![0, 1, 0], ![-2, 0, 6], ![4, -22, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-4, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-4, 1, 0]] 
 ![![23, 0, 0], ![19, 1, 0], ![4, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-4, 1, 0], ![2, -6, 6], ![80, -22, -2]]]
  hmulB := by decide  
  f := ![![![133, -407, 408], ![-23, -1564, 0]], ![![109, -335, 336], ![-22, -1288, 0]], ![![24, -71, 71], ![1, -272, 0]]]
  g := ![![![1, 0, 0], ![-19, 23, 0], ![-4, 0, 23]], ![![-1, 1, 0], ![4, -6, 6], ![22, -22, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![2, 1, 0]] ![![23, 0, 0], ![2, 1, 0]]
  ![![23, 0, 0], ![24, 8, 1]] where
 M := ![![![529, 0, 0], ![46, 23, 0]], ![![46, 23, 0], ![6, 2, 6]]]
 hmul := by decide  
 g := ![![![![-1, -8, -1], ![23, 0, 0]], ![![-22, -7, -1], ![23, 0, 0]]], ![![![-22, -7, -1], ![23, 0, 0]], ![![-6, -2, 0], ![6, 0, 0]]]]
 hle2 := by decide  
def MulI23N1 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![24, 8, 1]] ![![23, 0, 0], ![-4, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![-92, 23, 0]], ![![552, 184, 23], ![0, -46, 46]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![-4, 1, 0]]], ![![![24, 8, 1]], ![![0, -2, 2]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![4, 1, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![4, 1, 0]] 
 ![![29, 0, 0], ![4, 1, 0], ![28, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![4, 1, 0], ![2, 2, 6], ![80, -22, 6]]]
  hmulB := by decide  
  f := ![![![857, 874, 2640], ![174, -12760, 0]], ![![116, 119, 360], ![30, -1740, 0]], ![![828, 844, 2549], ![164, -12320, 0]]]
  g := ![![![1, 0, 0], ![-4, 29, 0], ![-28, 0, 29]], ![![0, 1, 0], ![-6, 2, 6], ![0, -22, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-8, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-8, 1, 0]] 
 ![![29, 0, 0], ![21, 1, 0], ![16, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-8, 1, 0], ![2, -10, 6], ![80, -22, -6]]]
  hmulB := by decide  
  f := ![![![549, -3052, 1836], ![-232, -8874, 0]], ![![395, -2204, 1326], ![-173, -6409, 0]], ![![304, -1684, 1013], ![-124, -4896, 0]]]
  g := ![![![1, 0, 0], ![-21, 29, 0], ![-16, 0, 29]], ![![-1, 1, 0], ![4, -10, 6], ![22, -22, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![4, 1, 0]] ![![29, 0, 0], ![4, 1, 0]]
  ![![29, 0, 0], ![3, 1, 1]] where
 M := ![![![841, 0, 0], ![116, 29, 0]], ![![116, 29, 0], ![18, 6, 6]]]
 hmul := by decide  
 g := ![![![![26, -1, -1], ![29, 0, 0]], ![![1, 0, -1], ![29, 0, 0]]], ![![![1, 0, -1], ![29, 0, 0]], ![![0, 0, 0], ![6, 0, 0]]]]
 hle2 := by decide  
def MulI29N1 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![3, 1, 1]] ![![29, 0, 0], ![-8, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![-232, 29, 0]], ![![87, 29, 29], ![58, -29, 0]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![-8, 1, 0]]], ![![![3, 1, 1]], ![![2, -1, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![11, 1, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![11, 1, 0]] 
 ![![31, 0, 0], ![11, 1, 0], ![20, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![11, 1, 0], ![2, 9, 6], ![80, -22, 13]]]
  hmulB := by decide  
  f := ![![![-147, -763, -510], ![-62, 2635, 0]], ![![-60, -270, -180], ![1, 930, 0]], ![![-92, -492, -329], ![-48, 1700, 0]]]
  g := ![![![1, 0, 0], ![-11, 31, 0], ![-20, 0, 31]], ![![0, 1, 0], ![-7, 9, 6], ![2, -22, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-6, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-6, 1, 0]] 
 ![![31, 0, 0], ![25, 1, 0], ![13, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-6, 1, 0], ![2, -8, 6], ![80, -22, -4]]]
  hmulB := by decide  
  f := ![![![-177, 758, -570], ![62, 2945, 0]], ![![-139, 606, -456], ![63, 2356, 0]], ![![-69, 317, -239], ![53, 1235, 0]]]
  g := ![![![1, 0, 0], ![-25, 31, 0], ![-13, 0, 31]], ![![-1, 1, 0], ![4, -8, 6], ![22, -22, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-5, 1, 0]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-5, 1, 0]] 
 ![![31, 0, 0], ![26, 1, 0], ![10, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-5, 1, 0], ![2, -7, 6], ![80, -22, -3]]]
  hmulB := by decide  
  f := ![![![-205, 754, -648], ![62, 3348, 0]], ![![-169, 628, -540], ![63, 2790, 0]], ![![-65, 243, -209], ![27, 1080, 0]]]
  g := ![![![1, 0, 0], ![-26, 31, 0], ![-10, 0, 31]], ![![-1, 1, 0], ![4, -7, 6], ![22, -22, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![11, 1, 0]] ![![31, 0, 0], ![-6, 1, 0]]
  ![![31, 0, 0], ![10, -15, 1]] where
 M := ![![![961, 0, 0], ![-186, 31, 0]], ![![341, 31, 0], ![-64, 3, 6]]]
 hmul := by decide  
 g := ![![![![21, 15, -1], ![31, 0, 0]], ![![-6, 1, 0], ![0, 0, 0]]], ![![![1, 16, -1], ![31, 0, 0]], ![![-4, 3, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![10, -15, 1]] ![![31, 0, 0], ![-5, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![-155, 31, 0]], ![![310, -465, 31], ![0, 93, -93]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![-5, 1, 0]]], ![![![10, -15, 1]], ![![0, 3, -3]]]]
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


lemma PB178I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB178I0 : PrimesBelowBoundCertificateInterval O 1 31 178 where
  m := 11
  g := ![3, 3, 1, 3, 1, 1, 2, 2, 3, 3, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB178I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1]
    · exact ![I3N0, I3N1, I3N1]
    · exact ![I5N0]
    · exact ![I7N0, I7N0, I7N0]
    · exact ![I11N0]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N0, I23N1]
    · exact ![I29N0, I29N0, I29N1]
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
    · exact ![3, 3, 3]
    · exact ![125]
    · exact ![7, 7, 7]
    · exact ![1331]
    · exact ![2197]
    · exact ![17, 289]
    · exact ![361, 19]
    · exact ![23, 23, 23]
    · exact ![29, 29, 29]
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
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
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
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I7N0, I17N0, I19N1, I23N0, I23N1, I29N0, I29N1, I31N0, I31N1, I31N2]
  Il := ![[I2N0, I2N0, I2N1], [I3N0, I3N1, I3N1], [I5N0], [I7N0, I7N0, I7N0], [], [], [I17N0], [I19N1], [I23N0, I23N0, I23N1], [I29N0, I29N0, I29N1], [I31N0, I31N1, I31N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
