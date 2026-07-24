
import IdealArithmetic.Examples.NF3_1_662796_1.RI3_1_662796_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![15, 0, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![15, 0, 1]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![15, 0, 1], ![84, -8, -2], ![-29, 13, -7]]]
  hmulB := by decide  
  f := ![![![-14, 0, -1], ![2, 0, 0]], ![![-7, 7, -3], ![-1, 0, -1]], ![![-7, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![-1, 0, 2]], ![![7, 0, 1], ![43, -8, -2], ![-11, 13, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![15, 0, 1]] ![![2, 0, 0], ![15, 0, 1]]
  ![![2, 0, 0], ![0, 1, 0]] where
 M := ![![![4, 0, 0], ![30, 0, 2]], ![![30, 0, 2], ![196, 13, 8]]]
 hmul := by decide  
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![15, 0, 1], ![0, 0, 0]]], ![![![15, 0, 1], ![0, 0, 0]], ![![97, 10, 9], ![-5, -1, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![15, 0, 1]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![30, 0, 2]], ![![0, 2, 0], ![84, -8, -2]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![15, 0, 1]]], ![![![0, 1, 0]], ![![42, -4, -1]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![1, 1, 0]] 
 ![![3, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![1, 1, 0], ![-2, 3, 10], ![84, -23, -1]]]
  hmulB := by decide  
  f := ![![![3, -3, -10], ![0, 3, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![1, -1, -3], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 3, 0], ![-1, 0, 3]], ![![0, 1, 0], ![-5, 3, 10], ![36, -23, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![3, 0, 0], ![14, 1, 1]] where
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![3, 3, 0], ![-1, 4, 10]]]
 hmul := by decide  
 g := ![![![![-11, -1, -1], ![3, 0, 0]], ![![-13, 0, -1], ![3, 0, 0]]], ![![![-13, 0, -1], ![3, 0, 0]], ![![-5, 1, 3], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![14, 1, 1]] ![![3, 0, 0], ![1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![42, 3, 3], ![96, -6, 9]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![1, 1, 0]]], ![![![14, 1, 1]], ![![32, -2, 3]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![1, 1, 0]] 
 ![![5, 0, 0], ![1, 1, 0], ![3, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![1, 1, 0], ![-2, 3, 10], ![84, -23, -1]]]
  hmulB := by decide  
  f := ![![![164, -51, -2], ![25, 0, -10]], ![![0, 0, 0], ![1, 0, 0]], ![![98, -31, -1], ![17, 0, -6]]]
  g := ![![![1, 0, 0], ![-1, 5, 0], ![-3, 0, 5]], ![![0, 1, 0], ![-7, 3, 10], ![22, -23, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![15, 0, 1]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![15, 0, 1]] 
 ![![5, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![15, 0, 1], ![84, -8, -2], ![-29, 13, -7]]]
  hmulB := by decide  
  f := ![![![-5, -8, -8], ![30, -5, 0]], ![![1, -3, -3], ![11, -2, 0]], ![![-3, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![-2, 5, 0], ![0, 0, 5]], ![![3, 0, 1], ![20, -8, -2], ![-11, 13, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1

def I5N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![17, 0, 1]] i)))

def SI5N2: IdealEqSpanCertificate' Table ![![5, 0, 0], ![17, 0, 1]] 
 ![![5, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![17, 0, 1], ![84, -6, -2], ![-29, 13, -5]]]
  hmulB := by decide  
  f := ![![![-16, 0, -1], ![5, 0, 0]], ![![-9, 5, 5], ![-17, 4, 0]], ![![-3, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![-2, 5, 0], ![-2, 0, 5]], ![![3, 0, 1], ![20, -6, -2], ![-9, 13, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N2 : Nat.card (O ⧸ I5N2) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N2)

lemma isPrimeI5N2 : Ideal.IsPrime I5N2 := prime_ideal_of_norm_prime hp5.out _ NI5N2
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![1, 1, 0]] ![![5, 0, 0], ![15, 0, 1]]
  ![![5, 0, 0], ![16, -2, 1]] where
 M := ![![![25, 0, 0], ![75, 0, 5]], ![![5, 5, 0], ![99, -8, -1]]]
 hmul := by decide  
 g := ![![![![-11, 2, -1], ![5, 0, 0]], ![![-1, 2, 0], ![5, 0, 0]]], ![![![-15, 3, -1], ![5, 0, 0]], ![![-9, 2, -2], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![16, -2, 1]] ![![5, 0, 0], ![17, 0, 1]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![85, 0, 5]], ![![80, -10, 5], ![75, 25, 15]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![17, 0, 1]]], ![![![16, -2, 1]], ![![15, 5, 3]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1, I5N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
    exact isPrimeI5N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![13, 2, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![13, 2, 1]] 
 ![![7, 0, 0], ![0, 7, 0], ![6, 2, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![13, 2, 1], ![80, -6, 18], ![139, -33, -13]]]
  hmulB := by decide  
  f := ![![![-12, -2, -1], ![7, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -2, 7]], ![![1, 0, 1], ![-4, -6, 18], ![31, -1, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [3, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 6], [0, 1]]
 g := ![![[4, 1], [2, 1]], ![[6, 6], [4, 6]]]
 h' := ![![[2, 6], [1, 1], [0, 1]], ![[0, 1], [3, 6], [2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [5, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [3, 5, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![956, -141, -585]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![638, 147, -585]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![3, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![3, 1, 0]] 
 ![![7, 0, 0], ![3, 1, 0], ![6, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![3, 1, 0], ![-2, 5, 10], ![84, -23, 1]]]
  hmulB := by decide  
  f := ![![![58, -151, -300], ![7, 210, 0]], ![![21, -61, -120], ![8, 84, 0]], ![![48, -130, -257], ![10, 180, 0]]]
  g := ![![![1, 0, 0], ![-3, 7, 0], ![-6, 0, 7]], ![![0, 1, 0], ![-11, 5, 10], ![21, -23, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![13, 2, 1]] ![![7, 0, 0], ![3, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![21, 7, 0]], ![![91, 14, 7], ![119, 0, 21]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![3, 1, 0]]], ![![![13, 2, 1]], ![![17, 0, 3]]]]
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
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![0, 1, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![0, 1, 0]] 
 ![![11, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![0, 1, 0], ![-2, 2, 10], ![84, -23, -2]]]
  hmulB := by decide  
  f := ![![![-11, 11, 60], ![11, -66, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-2, 2, 11], ![2, -12, 0]]]
  g := ![![![1, 0, 0], ![0, 11, 0], ![-2, 0, 11]], ![![0, 1, 0], ![-2, 2, 10], ![8, -23, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![5, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![5, 1, 0]] 
 ![![11, 0, 0], ![5, 1, 0], ![4, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![5, 1, 0], ![-2, 7, 10], ![84, -23, 3]]]
  hmulB := by decide  
  f := ![![![117, -443, -630], ![22, 693, 0]], ![![51, -197, -280], ![12, 308, 0]], ![![43, -161, -229], ![7, 252, 0]]]
  g := ![![![1, 0, 0], ![-5, 11, 0], ![-4, 0, 11]], ![![0, 1, 0], ![-7, 7, 10], ![17, -23, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-5, 1, 0]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-5, 1, 0]] 
 ![![11, 0, 0], ![6, 1, 0], ![6, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-5, 1, 0], ![-2, -3, 10], ![84, -23, -7]]]
  hmulB := by decide  
  f := ![![![2, -7, 20], ![11, -22, 0]], ![![-1, -3, 10], ![1, -11, 0]], ![![2, -4, 11], ![8, -12, 0]]]
  g := ![![![1, 0, 0], ![-6, 11, 0], ![-6, 0, 11]], ![![-1, 1, 0], ![-4, -3, 10], ![24, -23, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![0, 1, 0]] ![![11, 0, 0], ![5, 1, 0]]
  ![![11, 0, 0], ![13, 4, 1]] where
 M := ![![![121, 0, 0], ![55, 11, 0]], ![![0, 11, 0], ![-2, 7, 10]]]
 hmul := by decide  
 g := ![![![![-2, -4, -1], ![11, 0, 0]], ![![-8, -3, -1], ![11, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-12, -3, 0], ![10, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![13, 4, 1]] ![![11, 0, 0], ![-5, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![-55, 11, 0]], ![![143, 44, 11], ![11, -22, 33]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![-5, 1, 0]]], ![![![13, 4, 1]], ![![1, -2, 3]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![2, 1, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![2, 1, 0]] 
 ![![13, 0, 0], ![2, 1, 0], ![12, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![2, 1, 0], ![-2, 4, 10], ![84, -23, 0]]]
  hmulB := by decide  
  f := ![![![69, -141, -350], ![13, 455, 0]], ![![10, -20, -50], ![1, 65, 0]], ![![64, -130, -323], ![10, 420, 0]]]
  g := ![![![1, 0, 0], ![-2, 13, 0], ![-12, 0, 13]], ![![0, 1, 0], ![-10, 4, 10], ![10, -23, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![3, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![3, 1, 0]] 
 ![![13, 0, 0], ![3, 1, 0], ![10, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![3, 1, 0], ![-2, 5, 10], ![84, -23, 1]]]
  hmulB := by decide  
  f := ![![![160, -406, -810], ![13, 1053, 0]], ![![33, -91, -180], ![14, 234, 0]], ![![124, -312, -623], ![6, 810, 0]]]
  g := ![![![1, 0, 0], ![-3, 13, 0], ![-10, 0, 13]], ![![0, 1, 0], ![-9, 5, 10], ![11, -23, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-5, 1, 0]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-5, 1, 0]] 
 ![![13, 0, 0], ![8, 1, 0], ![10, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-5, 1, 0], ![-2, -3, 10], ![84, -23, -7]]]
  hmulB := by decide  
  f := ![![![-14, -31, 100], ![13, -130, 0]], ![![-6, -19, 60], ![14, -78, 0]], ![![-10, -24, 77], ![12, -100, 0]]]
  g := ![![![1, 0, 0], ![-8, 13, 0], ![-10, 0, 13]], ![![-1, 1, 0], ![-6, -3, 10], ![26, -23, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![2, 1, 0]] ![![13, 0, 0], ![3, 1, 0]]
  ![![13, 0, 0], ![16, 2, 1]] where
 M := ![![![169, 0, 0], ![39, 13, 0]], ![![26, 13, 0], ![4, 7, 10]]]
 hmul := by decide  
 g := ![![![![-3, -2, -1], ![13, 0, 0]], ![![-13, -1, -1], ![13, 0, 0]]], ![![![-14, -1, -1], ![13, 0, 0]], ![![-12, -1, 0], ![10, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![16, 2, 1]] ![![13, 0, 0], ![-5, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![-65, 13, 0]], ![![208, 26, 13], ![0, -13, 13]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![-5, 1, 0]]], ![![![16, 2, 1]], ![![0, -1, 1]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![3, 1, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![3, 1, 0]] 
 ![![17, 0, 0], ![3, 1, 0], ![0, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![3, 1, 0], ![-2, 5, 10], ![84, -23, 1]]]
  hmulB := by decide  
  f := ![![![-2, -1, 0], ![17, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -4, -7], ![8, 12, 0]]]
  g := ![![![1, 0, 0], ![-3, 17, 0], ![0, 0, 17]], ![![0, 1, 0], ![-1, 5, 10], ![9, -23, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-6, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-6, 1, 0]] 
 ![![17, 0, 0], ![11, 1, 0], ![11, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-6, 1, 0], ![-2, -4, 10], ![84, -23, -8]]]
  hmulB := by decide  
  f := ![![![313, 676, -1680], ![-68, 2856, 0]], ![![205, 434, -1080], ![-33, 1836, 0]], ![![205, 437, -1087], ![-37, 1848, 0]]]
  g := ![![![1, 0, 0], ![-11, 17, 0], ![-11, 0, 17]], ![![-1, 1, 0], ![-4, -4, 10], ![25, -23, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![3, 1, 0]] ![![17, 0, 0], ![3, 1, 0]]
  ![![17, 0, 0], ![16, -6, 1]] where
 M := ![![![289, 0, 0], ![51, 17, 0]], ![![51, 17, 0], ![7, 8, 10]]]
 hmul := by decide  
 g := ![![![![1, 6, -1], ![17, 0, 0]], ![![-13, 7, -1], ![17, 0, 0]]], ![![![-13, 7, -1], ![17, 0, 0]], ![![-9, 4, 0], ![10, 0, 0]]]]
 hle2 := by decide  
def MulI17N1 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![16, -6, 1]] ![![17, 0, 0], ![-6, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![-102, 17, 0]], ![![272, -102, 17], ![0, 17, -68]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![-6, 1, 0]]], ![![![16, -6, 1]], ![![0, 1, -4]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![0, 1, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![0, 1, 0]] 
 ![![19, 0, 0], ![0, 1, 0], ![15, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![0, 1, 0], ![-2, 2, 10], ![84, -23, -2]]]
  hmulB := by decide  
  f := ![![![-19, 19, 100], ![19, -190, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-15, 15, 79], ![15, -150, 0]]]
  g := ![![![1, 0, 0], ![0, 19, 0], ![-15, 0, 19]], ![![0, 1, 0], ![-8, 2, 10], ![6, -23, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![0, 1, 0]] ![![19, 0, 0], ![0, 1, 0]]
  ![![19, 0, 0], ![15, 4, 1]] where
 M := ![![![361, 0, 0], ![0, 19, 0]], ![![0, 19, 0], ![-2, 2, 10]]]
 hmul := by decide  
 g := ![![![![4, -4, -1], ![19, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-8, -2, 0], ![10, 0, 0]]]]
 hle2 := by decide  
def MulI19N1 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![15, 4, 1]] ![![19, 0, 0], ![0, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![0, 19, 0]], ![![285, 76, 19], ![76, 0, 38]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![0, 1, 0]]], ![![![15, 4, 1]], ![![4, 0, 2]]]]
 hle2 := by decide  

def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N0, I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N0
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
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


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [10, 5, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 22, 7], [6, 0, 16], [0, 1]]
 g := ![![[7, 20, 6], [14, 15, 16], [20, 5, 1], []], ![[16, 12, 10, 7], [18, 13, 19, 11], [14, 10], [1, 3]], ![[5, 1, 8, 4], [5, 20, 6, 3], [19, 18, 13, 16], [15, 3]]]
 h' := ![![[22, 22, 7], [21, 13, 12], [7, 11, 19], [0, 0, 1], [0, 1]], ![[6, 0, 16], [15, 5, 22], [9, 6, 8], [14, 13], [22, 22, 7]], ![[0, 1], [19, 5, 12], [0, 6, 19], [1, 10, 22], [6, 0, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 4], []]
 b := ![[], [18, 2, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [10, 5, 18, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4696094, -1582308, 1137304]
  a := ![-3, 0, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![204178, -68796, 49448]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0]] 
 ![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [10, 19, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 23, 10], [8, 5, 19], [0, 1]]
 g := ![![[9, 1, 7], [22, 16], [12, 22, 25], [1]], ![[14, 3, 27, 2], [25, 23], [3, 17, 8, 27], [6, 22, 10, 14]], ![[20, 6, 10, 18], [17, 25], [26, 16, 8, 12], [17, 18, 9, 15]]]
 h' := ![![[26, 23, 10], [28, 2, 6], [25, 0, 4], [19, 10, 5], [0, 1]], ![[8, 5, 19], [12, 10, 21], [28, 5, 20], [0, 26, 9], [26, 23, 10]], ![[0, 1], [5, 17, 2], [28, 24, 5], [23, 22, 15], [8, 5, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 12], []]
 b := ![[], [12, 19, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [10, 19, 24, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1045095301, -282669844, -110570649]
  a := ![1, -64, -69]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![36037769, -9747236, -3812781]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![23, -12, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![23, -12, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![23, 19, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![23, -12, 1], ![108, -24, -122], ![-1037, 289, 25]]]
  hmulB := by decide  
  f := ![![![-22, 12, -1], ![31, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -19, 31]], ![![0, -1, 1], ![94, 74, -122], ![-52, -6, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [20, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 30], [0, 1]]
 g := ![![[25, 14], [15, 1], [9, 16], [27, 1]], ![[0, 17], [11, 30], [7, 15], [23, 30]]]
 h' := ![![[27, 30], [10, 18], [6, 30], [18, 27], [0, 1]], ![[0, 1], [0, 13], [10, 1], [3, 4], [27, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [2, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [20, 4, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3293, 1896, -4498]
  a := ![3, -1, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3231, 2818, -4498]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-2, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-2, 1, 0]] 
 ![![31, 0, 0], ![29, 1, 0], ![6, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-2, 1, 0], ![-2, 0, 10], ![84, -23, -4]]]
  hmulB := by decide  
  f := ![![![-895, -2, 4500], ![62, -13950, 0]], ![![-835, -2, 4200], ![63, -13020, 0]], ![![-172, -1, 871], ![31, -2700, 0]]]
  g := ![![![1, 0, 0], ![-29, 31, 0], ![-6, 0, 31]], ![![-1, 1, 0], ![-2, 0, 10], ![25, -23, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![23, -12, 1]] ![![31, 0, 0], ![-2, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![-62, 31, 0]], ![![713, -372, 31], ![62, 0, -124]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![-2, 1, 0]]], ![![![23, -12, 1]], ![![2, 0, -4]]]]
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


lemma PB231I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB231I0 : PrimesBelowBoundCertificateInterval O 1 31 231 where
  m := 11
  g := ![3, 3, 3, 2, 3, 3, 3, 3, 1, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB231I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N1, I5N2]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N0, I17N1]
    · exact ![I19N0, I19N0, I19N0]
    · exact ![I23N0]
    · exact ![I29N0]
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
    · exact ![2, 2, 2]
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![49, 7]
    · exact ![11, 11, 11]
    · exact ![13, 13, 13]
    · exact ![17, 17, 17]
    · exact ![19, 19, 19]
    · exact ![12167]
    · exact ![24389]
    · exact ![961, 31]
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
      exact NI3N0
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
      exact NI5N2
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N2
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N0
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I3N0, I5N0, I5N1, I5N2, I7N0, I7N1, I11N0, I11N1, I11N2, I13N0, I13N1, I13N2, I17N0, I17N1, I19N0, I31N1]
  Il := ![[I2N0, I2N0, I2N0], [I3N0, I3N0, I3N0], [I5N0, I5N1, I5N2], [I7N0, I7N1], [I11N0, I11N1, I11N2], [I13N0, I13N1, I13N2], [I17N0, I17N0, I17N1], [I19N0, I19N0, I19N0], [], [], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
