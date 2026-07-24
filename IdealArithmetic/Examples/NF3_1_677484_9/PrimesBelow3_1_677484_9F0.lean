
import IdealArithmetic.Examples.NF3_1_677484_9.RI3_1_677484_9
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-24, -1, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![-24, -1, 1]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![-24, -1, 1], ![258, 12, -6], ![-258, 7, 12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![9, -8, -1], ![-10, 0, 1]], ![![3, 9, 1], ![11, 0, -1]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![-12, -1, 1], ![129, 12, -6], ![-129, 7, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![-24, -1, 1]] ![![2, 0, 0], ![-24, -1, 1]]
  ![![2, 0, 0], ![0, 1, 0]] where
 M := ![![![4, 0, 0], ![-48, -2, 2]], ![![-48, -2, 2], ![60, 19, -6]]]
 hmul := by decide  
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![-24, -1, 1], ![0, 0, 0]]], ![![![-24, -1, 1], ![0, 0, 0]], ![![30, 7, -3], ![5, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![-24, -1, 1]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![-48, -2, 2]], ![![0, 2, 0], ![258, 12, -6]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![-24, -1, 1]]], ![![![0, 1, 0]], ![![129, 6, -3]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-24, -1, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-24, -1, 1]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-24, -1, 1], ![258, 12, -6], ![-258, 7, 12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![8, -23, -2], ![-42, 0, 4]], ![![4, 12, 1], ![22, 0, -2]]]
  g := ![![![1, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-8, -1, 1], ![86, 12, -6], ![-86, 7, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![-24, -1, 1]] ![![3, 0, 0], ![-24, -1, 1]]
  ![![3, 0, 0], ![0, 1, 0]] where
 M := ![![![9, 0, 0], ![-72, -3, 3]], ![![-72, -3, 3], ![60, 19, -6]]]
 hmul := by decide  
 g := ![![![![3, 0, 0], ![0, 0, 0]], ![![-24, -1, 1], ![0, 0, 0]]], ![![![-24, -1, 1], ![0, 0, 0]], ![![20, 5, -2], ![4, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![-24, -1, 1]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![-72, -3, 3]], ![![0, 3, 0], ![258, 12, -6]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![-24, -1, 1]]], ![![![0, 1, 0]], ![![86, 4, -2]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0]] 
 ![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [4, 1, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 0, 2], [0, 4, 3], [0, 1]]
 g := ![![[3, 3, 1], []], ![[2, 4, 3, 2], [2, 4]], ![[0, 2], [1, 4]]]
 h' := ![![[3, 0, 2], [0, 0, 1], [0, 1]], ![[0, 4, 3], [1, 2, 4], [3, 0, 2]], ![[0, 1], [1, 3], [0, 4, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 3], []]
 b := ![[], [2, 0, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [4, 1, 2, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-39470, -7745, -2635]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7894, -1549, -527]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [1, 0, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2, 6], [1, 4, 1], [0, 1]]
 g := ![![[5, 6, 2], [1]], ![[6, 3, 3, 3], [1, 3, 3, 6]], ![[2, 0, 0, 1], [4, 5, 1, 1]]]
 h' := ![![[2, 2, 6], [6, 0, 3], [0, 1]], ![[1, 4, 1], [0, 0, 5], [2, 2, 6]], ![[0, 1], [4, 0, 6], [1, 4, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2], []]
 b := ![[], [3, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [1, 0, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-217490, 21133, 29169]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-31070, 3019, 4167]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-26, 3, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-26, 3, 1]] 
 ![![11, 0, 0], ![0, 11, 0], ![7, 3, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-26, 3, 1], ![258, 10, 18], ![774, 151, 10]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![3, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -3, 11]], ![![-3, 0, 1], ![12, -4, 18], ![64, 11, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [6, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 10], [0, 1]]
 g := ![![[9, 9], [0, 1], [1]], ![[7, 2], [1, 10], [1]]]
 h' := ![![[1, 10], [0, 8], [5, 1], [0, 1]], ![[0, 1], [8, 3], [6, 10], [1, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [10, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [6, 10, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2946, -147, 160]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![166, -57, 160]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![4, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![4, 1, 0]] 
 ![![11, 0, 0], ![4, 1, 0], ![1, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![4, 1, 0], ![0, 4, 6], ![258, 36, 4]]]
  hmulB := by decide  
  f := ![![![5, 1, 0], ![-11, 0, 0]], ![![-4, -1, 0], ![12, 0, 0]], ![![-1, -1, -1], ![3, 2, 0]]]
  g := ![![![1, 0, 0], ![-4, 11, 0], ![-1, 0, 11]], ![![0, 1, 0], ![-2, 4, 6], ![10, 36, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![-26, 3, 1]] ![![11, 0, 0], ![4, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![44, 11, 0]], ![![-286, 33, 11], ![154, 22, 22]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![4, 1, 0]]], ![![![-26, 3, 1]], ![![14, 2, 2]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-30, -1, 1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-30, -1, 1]] 
 ![![13, 0, 0], ![0, 13, 0], ![9, 12, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-30, -1, 1], ![258, 6, -6], ![-258, 7, 6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![3, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -12, 13]], ![![-3, -1, 1], ![24, 6, -6], ![-24, -5, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [1, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 12], [0, 1]]
 g := ![![[8, 1], [4], [5, 1]], ![[0, 12], [4], [10, 12]]]
 h' := ![![[5, 12], [8, 1], [8, 11], [0, 1]], ![[0, 1], [0, 12], [11, 2], [5, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [12, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [1, 8, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1538, 181, 300]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-326, -263, 300]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![6, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![6, 1, 0]] 
 ![![13, 0, 0], ![6, 1, 0], ![7, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![6, 1, 0], ![0, 6, 6], ![258, 36, 6]]]
  hmulB := by decide  
  f := ![![![19, 3, 0], ![-39, 0, 0]], ![![6, 1, 0], ![-12, 0, 0]], ![![13, -3, -5], ![-27, 11, 0]]]
  g := ![![![1, 0, 0], ![-6, 13, 0], ![-7, 0, 13]], ![![0, 1, 0], ![-6, 6, 6], ![0, 36, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![-30, -1, 1]] ![![13, 0, 0], ![6, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![78, 13, 0]], ![![-390, -13, 13], ![78, 0, 0]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![6, 1, 0]]], ![![![-30, -1, 1]], ![![6, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![4, 1, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![4, 1, 0]] 
 ![![17, 0, 0], ![4, 1, 0], ![3, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![4, 1, 0], ![0, 4, 6], ![258, 36, 4]]]
  hmulB := by decide  
  f := ![![![29, 7, 0], ![-119, 0, 0]], ![![4, 1, 0], ![-16, 0, 0]], ![![-1, -1, -1], ![5, 3, 0]]]
  g := ![![![1, 0, 0], ![-4, 17, 0], ![-3, 0, 17]], ![![0, 1, 0], ![-2, 4, 6], ![6, 36, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-2, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-2, 1, 0]] 
 ![![17, 0, 0], ![15, 1, 0], ![5, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-2, 1, 0], ![0, -2, 6], ![258, 36, -2]]]
  hmulB := by decide  
  f := ![![![23, -11, 0], ![187, 0, 0]], ![![21, -10, 0], ![171, 0, 0]], ![![7, -3, -1], ![57, 3, 0]]]
  g := ![![![1, 0, 0], ![-15, 17, 0], ![-5, 0, 17]], ![![-1, 1, 0], ![0, -2, 6], ![-16, 36, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![4, 1, 0]] ![![17, 0, 0], ![-2, 1, 0]]
  ![![17, 0, 0], ![-24, 6, 1]] where
 M := ![![![289, 0, 0], ![-34, 17, 0]], ![![68, 17, 0], ![-8, 2, 6]]]
 hmul := by decide  
 g := ![![![![17, 0, 0], ![0, 0, 0]], ![![22, -5, -1], ![17, 0, 0]]], ![![![4, 1, 0], ![0, 0, 0]], ![![8, -2, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![-24, 6, 1]] ![![17, 0, 0], ![-2, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![-34, 17, 0]], ![![-408, 102, 17], ![306, 0, 34]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![-2, 1, 0]]], ![![![-24, 6, 1]], ![![18, 0, 2]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-31, -2, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-31, -2, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![7, 17, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-31, -2, 1], ![258, 5, -12], ![-516, -29, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -17, 19]], ![![-2, -1, 1], ![18, 11, -12], ![-29, -6, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [4, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 18], [0, 1]]
 g := ![![[15, 5], [17, 9], [9], [1]], ![[0, 14], [9, 10], [9], [1]]]
 h' := ![![[16, 18], [8, 9], [18, 16], [15, 16], [0, 1]], ![[0, 1], [0, 10], [8, 3], [5, 3], [16, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [14, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [4, 3, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![520, 112, 39]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![13, -29, 39]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-7, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-7, 1, 0]] 
 ![![19, 0, 0], ![12, 1, 0], ![14, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-7, 1, 0], ![0, -7, 6], ![258, 36, -7]]]
  hmulB := by decide  
  f := ![![![106, -15, 0], ![285, 0, 0]], ![![64, -9, 0], ![172, 0, 0]], ![![84, -6, -5], ![226, 16, 0]]]
  g := ![![![1, 0, 0], ![-12, 19, 0], ![-14, 0, 19]], ![![-1, 1, 0], ![0, -7, 6], ![-4, 36, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![-31, -2, 1]] ![![19, 0, 0], ![-7, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-133, 19, 0]], ![![-589, -38, 19], ![475, 19, -19]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-7, 1, 0]]], ![![![-31, -2, 1]], ![![25, 1, -1]]]]
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


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [22, 2, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 4, 12], [2, 18, 11], [0, 1]]
 g := ![![[4, 17, 4], [8, 14, 12], [11, 6, 1], []], ![[9, 13, 3, 9], [19, 22, 10, 13], [5, 21, 17, 1], [17, 6]], ![[22, 17, 18, 5], [8, 16, 10, 21], [14, 15, 3, 15], [18, 6]]]
 h' := ![![[4, 4, 12], [8, 4, 2], [11, 7, 9], [0, 0, 1], [0, 1]], ![[2, 18, 11], [21, 1, 15], [14, 18, 16], [10, 4, 18], [4, 4, 12]], ![[0, 1], [14, 18, 6], [16, 21, 21], [22, 19, 4], [2, 18, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 22], []]
 b := ![[], [10, 13, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [22, 2, 17, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11354364, 1866887, 294009]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![493668, 81169, 12783]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-16, 10, 1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-16, 10, 1]] 
 ![![29, 0, 0], ![0, 29, 0], ![13, 10, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-16, 10, 1], ![258, 20, 60], ![2580, 403, 20]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -10, 29]], ![![-1, 0, 1], ![-18, -20, 60], ![80, 7, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [22, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 28], [0, 1]]
 g := ![![[8, 4], [9], [1, 5], [27, 1]], ![[0, 25], [9], [20, 24], [25, 28]]]
 h' := ![![[27, 28], [25, 27], [7, 26], [15, 11], [0, 1]], ![[0, 1], [0, 2], [13, 3], [22, 18], [27, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [9, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [22, 2, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1527, -173, 90]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-93, -37, 90]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-2, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-2, 1, 0]] 
 ![![29, 0, 0], ![27, 1, 0], ![9, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-2, 1, 0], ![0, -2, 6], ![258, 36, -2]]]
  hmulB := by decide  
  f := ![![![35, -17, 0], ![493, 0, 0]], ![![33, -16, 0], ![465, 0, 0]], ![![11, -5, -1], ![155, 5, 0]]]
  g := ![![![1, 0, 0], ![-27, 29, 0], ![-9, 0, 29]], ![![-1, 1, 0], ![0, -2, 6], ![-24, 36, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![-16, 10, 1]] ![![29, 0, 0], ![-2, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![-58, 29, 0]], ![![-464, 290, 29], ![290, 0, 58]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![-2, 1, 0]]], ![![![-16, 10, 1]], ![![10, 0, 2]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3659389, -720257, -247579]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-3659389, -720257, -247579]] 
 ![![31, 0, 0], ![0, 31, 0], ![21, 5, 1]] where
  M :=![![![-3659389, -720257, -247579], ![-63875382, -12572233, -4321542], ![-185826306, -36575149, -12572233]]]
  hmulB := by decide  
  f := ![![![-1501, 310, -77]], ![![-19866, -4273, 1860]], ![![-1641, -226, 110]]]
  g := ![![![49670, 16698, -247579], ![867000, 291467, -4321542], ![2522277, 847936, -12572233]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [10, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 30], [0, 1]]
 g := ![![[0, 28], [0, 2], [0, 7], [0, 1]], ![[0, 3], [0, 29], [0, 24], [0, 30]]]
 h' := ![![[0, 30], [0, 11], [0, 23], [0, 21], [0, 1]], ![[0, 1], [0, 20], [0, 8], [0, 10], [0, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [0, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [10, 0, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1042, 316, 150]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-68, -14, 150]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1501, -310, 77]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![1501, -310, 77]] 
 ![![31, 0, 0], ![1, 1, 0], ![5, 0, 1]] where
  M :=![![![1501, -310, 77], ![19866, 4273, -1860], ![-79980, -7849, 4273]]]
  hmulB := by decide  
  f := ![![![3659389, 720257, 247579]], ![![2178541, 428790, 147391]], ![![6584621, 1296014, 445488]]]
  g := ![![![46, -310, 77], ![803, 4273, -1860], ![-3016, -7849, 4273]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-3659389, -720257, -247579]] ![![1501, -310, 77]]
  ![![31, 0, 0]] where
 M := ![![![-31, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB233I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB233I0 : PrimesBelowBoundCertificateInterval O 1 31 233 where
  m := 11
  g := ![3, 3, 1, 1, 2, 2, 3, 2, 1, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB233I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
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
    · exact ![2, 2, 2]
    · exact ![3, 3, 3]
    · exact ![125]
    · exact ![343]
    · exact ![121, 11]
    · exact ![169, 13]
    · exact ![17, 17, 17]
    · exact ![361, 19]
    · exact ![12167]
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
  β := ![I2N0, I3N0, I5N0, I11N0, I11N1, I13N0, I13N1, I17N0, I17N1, I19N1, I29N1, I31N1]
  Il := ![[I2N0, I2N0, I2N0], [I3N0, I3N0, I3N0], [I5N0], [], [I11N0, I11N1], [I13N0, I13N1], [I17N0, I17N1, I17N1], [I19N1], [], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
