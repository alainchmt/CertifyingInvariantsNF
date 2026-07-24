
import IdealArithmetic.Examples.NF3_1_662796_2.RI3_1_662796_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![-1, 1, 3], ![469, 76, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![1, 0, -1], ![-1, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![-1, 0, 2]], ![![0, 1, 0], ![-2, 1, 3], ![235, 76, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0], ![-51, -3, 1]] where
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![-1, 1, 3]]]
 hmul := by decide  
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![25, 2, 1], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![-51, -3, 1]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![-102, -6, 2], ![472, 22, -10]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![0, 1, 0]]], ![![![-51, -3, 1]], ![![236, 11, -5]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-52, -3, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-52, -3, 1]] 
 ![![3, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-52, -3, 1], ![472, 21, -10], ![-1745, -97, 28]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![37, 0, 3], ![-65, 0, 2]], ![![18, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![-1, 3, 0], ![-2, 0, 3]], ![![-17, -3, 1], ![157, 21, -10], ![-568, -97, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![-52, -3, 1]] ![![3, 0, 0], ![-52, -3, 1]]
  ![![3, 0, 0], ![1, 1, 0]] where
 M := ![![![9, 0, 0], ![-156, -9, 3]], ![![-156, -9, 3], ![-457, -4, 6]]]
 hmul := by decide  
 g := ![![![![2, -1, 0], ![3, 0, 0]], ![![-47, 2, 1], ![-15, 0, 0]]], ![![![-47, 2, 1], ![-15, 0, 0]], ![![-139, 12, 2], ![-40, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![-52, -3, 1]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![-156, -9, 3]], ![![3, 3, 0], ![420, 18, -9]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![-52, -3, 1]]], ![![![1, 1, 0]], ![![140, 6, -3]]]]
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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [4, 3, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 0, 1], [1, 4, 4], [0, 1]]
 g := ![![[3, 4, 1], []], ![[4, 4, 1, 1], [4, 1]], ![[1, 4], [1, 1]]]
 h' := ![![[3, 0, 1], [0, 0, 1], [0, 1]], ![[1, 4, 4], [3, 4, 4], [3, 0, 1]], ![[0, 1], [2, 1], [1, 4, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 4], []]
 b := ![[], [2, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [4, 3, 1, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2880470, -856335, -169980]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-576094, -171267, -33996]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-50, -3, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-50, -3, 1]] 
 ![![7, 0, 0], ![0, 7, 0], ![6, 4, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-50, -3, 1], ![472, 23, -10], ![-1745, -97, 30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![8, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -4, 7]], ![![-8, -1, 1], ![76, 9, -10], ![-275, -31, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [3, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 6], [0, 1]]
 g := ![![[3, 1], [5, 1]], ![[1, 6], [3, 6]]]
 h' := ![![[5, 6], [6, 1], [0, 1]], ![[0, 1], [4, 6], [5, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [3, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21626, 8384, 4896]
  a := ![-3, 0, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7286, -1600, 4896]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![3, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![3, 1, 0]] 
 ![![7, 0, 0], ![3, 1, 0], ![5, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![3, 1, 0], ![-1, 4, 3], ![469, 76, 2]]]
  hmulB := by decide  
  f := ![![![16, -60, -45], ![0, 105, 0]], ![![6, -24, -18], ![1, 42, 0]], ![![11, -43, -32], ![1, 75, 0]]]
  g := ![![![1, 0, 0], ![-3, 7, 0], ![-5, 0, 7]], ![![0, 1, 0], ![-4, 4, 3], ![33, 76, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![-50, -3, 1]] ![![7, 0, 0], ![3, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![21, 7, 0]], ![![-350, -21, 7], ![322, 14, -7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![3, 1, 0]]], ![![![-50, -3, 1]], ![![46, 2, -1]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0]] 
 ![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [2, 2, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 9, 3], [1, 1, 8], [0, 1]]
 g := ![![[4, 4, 4], [3, 4, 1], []], ![[4, 4, 3, 4], [7, 6, 4, 3], [2, 9]], ![[7, 0, 8, 2], [0, 10, 1, 10], [8, 9]]]
 h' := ![![[3, 9, 3], [5, 8, 2], [0, 0, 1], [0, 1]], ![[1, 1, 8], [6, 4, 4], [5, 10, 1], [3, 9, 3]], ![[0, 1], [5, 10, 5], [7, 1, 9], [1, 1, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 3], []]
 b := ![[], [1, 7, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [2, 2, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-41558244607, -11327007131, -2099564995]
  a := ![1, -64, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3778022237, -1029727921, -190869545]
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


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [3, 9, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 8, 12], [0, 4, 1], [0, 1]]
 g := ![![[2, 4, 1], [9, 10], [1]], ![[11, 0, 6, 12], [1, 4], [11, 9, 4, 12]], ![[0, 1], [3, 12], [2, 3, 6, 1]]]
 h' := ![![[7, 8, 12], [8, 8, 12], [10, 4, 7], [0, 1]], ![[0, 4, 1], [1, 4, 1], [11, 10, 11], [7, 8, 12]], ![[0, 1], [1, 1], [7, 12, 8], [0, 4, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 4], []]
 b := ![[], [12, 7, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [3, 9, 6, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-25240150, -11213397, -2788539]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1941550, -862569, -214503]
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


def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![5, 1, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![5, 1, 0]] 
 ![![17, 0, 0], ![5, 1, 0], ![1, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![5, 1, 0], ![-1, 6, 3], ![469, 76, 4]]]
  hmulB := by decide  
  f := ![![![-32, 167, 84], ![17, -476, 0]], ![![-8, 48, 24], ![1, -136, 0]], ![![-6, 9, 5], ![15, -28, 0]]]
  g := ![![![1, 0, 0], ![-5, 17, 0], ![-1, 0, 17]], ![![0, 1, 0], ![-2, 6, 3], ![5, 76, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![7, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![7, 1, 0]] 
 ![![17, 0, 0], ![7, 1, 0], ![15, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![7, 1, 0], ![-1, 8, 3], ![469, 76, 6]]]
  hmulB := by decide  
  f := ![![![-26, 159, 60], ![17, -340, 0]], ![![-8, 64, 24], ![1, -136, 0]], ![![-18, 141, 53], ![3, -300, 0]]]
  g := ![![![1, 0, 0], ![-7, 17, 0], ![-15, 0, 17]], ![![0, 1, 0], ![-6, 8, 3], ![-9, 76, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![5, 1, 0]] ![![17, 0, 0], ![5, 1, 0]]
  ![![17, 0, 0], ![-43, -2, 1]] where
 M := ![![![289, 0, 0], ![85, 17, 0]], ![![85, 17, 0], ![24, 11, 3]]]
 hmul := by decide  
 g := ![![![![17, 0, 0], ![0, 0, 0]], ![![5, 1, 0], ![0, 0, 0]]], ![![![5, 1, 0], ![0, 0, 0]], ![![9, 1, 0], ![3, 0, 0]]]]
 hle2 := by decide  
def MulI17N1 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![-43, -2, 1]] ![![17, 0, 0], ![7, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![119, 17, 0]], ![![-731, -34, 17], ![170, 17, 0]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![7, 1, 0]]], ![![![-43, -2, 1]], ![![10, 1, 0]]]]
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
 ![![19, 0, 0], ![0, 1, 0], ![6, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![0, 1, 0], ![-1, 1, 3], ![469, 76, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![6, -6, 0]]]
  g := ![![![1, 0, 0], ![0, 19, 0], ![-6, 0, 19]], ![![0, 1, 0], ![-1, 1, 3], ![25, 76, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![0, 1, 0]] ![![19, 0, 0], ![0, 1, 0]]
  ![![19, 0, 0], ![-51, -6, 1]] where
 M := ![![![361, 0, 0], ![0, 19, 0]], ![![0, 19, 0], ![-1, 1, 3]]]
 hmul := by decide  
 g := ![![![![19, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![8, 1, 0], ![3, 0, 0]]]]
 hle2 := by decide  
def MulI19N1 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![-51, -6, 1]] ![![19, 0, 0], ![0, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![0, 19, 0]], ![![-969, -114, 19], ![475, 19, -19]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![0, 1, 0]]], ![![![-51, -6, 1]], ![![25, 1, -1]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![5, 1, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![5, 1, 0]] 
 ![![23, 0, 0], ![5, 1, 0], ![5, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![5, 1, 0], ![-1, 6, 3], ![469, 76, 4]]]
  hmulB := by decide  
  f := ![![![-214, 1259, 630], ![23, -4830, 0]], ![![-50, 269, 135], ![24, -1035, 0]], ![![-50, 273, 137], ![21, -1050, 0]]]
  g := ![![![1, 0, 0], ![-5, 23, 0], ![-5, 0, 23]], ![![0, 1, 0], ![-2, 6, 3], ![3, 76, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-4, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-4, 1, 0]] 
 ![![23, 0, 0], ![19, 1, 0], ![11, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-4, 1, 0], ![-1, -3, 3], ![469, 76, -5]]]
  hmulB := by decide  
  f := ![![![-80, -256, 255], ![23, -1955, 0]], ![![-65, -211, 210], ![24, -1610, 0]], ![![-36, -123, 122], ![24, -935, 0]]]
  g := ![![![1, 0, 0], ![-19, 23, 0], ![-11, 0, 23]], ![![-1, 1, 0], ![1, -3, 3], ![-40, 76, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-1, 1, 0]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-1, 1, 0]] 
 ![![23, 0, 0], ![22, 1, 0], ![15, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-1, 1, 0], ![-1, 0, 3], ![469, 76, -2]]]
  hmulB := by decide  
  f := ![![![-482, -1, 1452], ![23, -11132, 0]], ![![-460, -1, 1386], ![24, -10626, 0]], ![![-314, -1, 947], ![23, -7260, 0]]]
  g := ![![![1, 0, 0], ![-22, 23, 0], ![-15, 0, 23]], ![![-1, 1, 0], ![-2, 0, 3], ![-51, 76, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![5, 1, 0]] ![![23, 0, 0], ![-4, 1, 0]]
  ![![23, 0, 0], ![-53, -7, 1]] where
 M := ![![![529, 0, 0], ![-92, 23, 0]], ![![115, 23, 0], ![-21, 2, 3]]]
 hmul := by decide  
 g := ![![![![23, 0, 0], ![0, 0, 0]], ![![49, 8, -1], ![23, 0, 0]]], ![![![5, 1, 0], ![0, 0, 0]], ![![6, 1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![-53, -7, 1]] ![![23, 0, 0], ![-1, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![-23, 23, 0]], ![![-1219, -161, 23], ![529, 23, -23]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![-1, 1, 0]]], ![![![-53, -7, 1]], ![![23, 1, -1]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)
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


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [5, 7, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 6, 3], [23, 22, 26], [0, 1]]
 g := ![![[3, 12, 28], [9, 24], [24, 23, 6], [1]], ![[18, 12, 22, 11], [15, 25], [26, 17, 9, 10], [12, 28, 1, 27]], ![[4, 1, 15, 2], [4, 5], [17, 2, 5, 14], [15, 0, 1, 2]]]
 h' := ![![[14, 6, 3], [0, 25, 12], [25, 3, 13], [24, 22, 8], [0, 1]], ![[23, 22, 26], [21, 7, 20], [3, 25, 5], [16, 27, 10], [14, 6, 3]], ![[0, 1], [25, 26, 26], [25, 1, 11], [28, 9, 11], [23, 22, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 1], []]
 b := ![[], [25, 2, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [5, 7, 21, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2828805, -814523, -156252]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-97545, -28087, -5388]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-40, -1, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-40, -1, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![22, 30, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-40, -1, 1], ![470, 35, -4], ![-807, 55, 38]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -30, 31]], ![![-2, -1, 1], ![18, 5, -4], ![-53, -35, 38]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [7, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 30], [0, 1]]
 g := ![![[20, 9], [2, 4], [22, 1], [15, 1]], ![[0, 22], [0, 27], [6, 30], [30, 30]]]
 h' := ![![[15, 30], [17, 3], [1, 2], [19, 1], [0, 1]], ![[0, 1], [0, 28], [0, 29], [3, 30], [15, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [7, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [7, 16, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![72935, 15599, 2443]
  a := ![-1, 21, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![619, -1861, 2443]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![4, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![4, 1, 0]] 
 ![![31, 0, 0], ![4, 1, 0], ![24, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![4, 1, 0], ![-1, 5, 3], ![469, 76, 3]]]
  hmulB := by decide  
  f := ![![![-99, 479, 288], ![31, -2976, 0]], ![![-12, 60, 36], ![1, -372, 0]], ![![-76, 371, 223], ![19, -2304, 0]]]
  g := ![![![1, 0, 0], ![-4, 31, 0], ![-24, 0, 31]], ![![0, 1, 0], ![-3, 5, 3], ![3, 76, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![-40, -1, 1]] ![![31, 0, 0], ![4, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![124, 31, 0]], ![![-1240, -31, 31], ![310, 31, 0]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![4, 1, 0]]], ![![![-40, -1, 1]], ![![10, 1, 0]]]]
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
  g := ![3, 3, 1, 2, 1, 1, 3, 3, 3, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB231I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0]
    · exact ![I17N0, I17N0, I17N1]
    · exact ![I19N0, I19N0, I19N0]
    · exact ![I23N0, I23N1, I23N2]
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
    · exact ![125]
    · exact ![49, 7]
    · exact ![1331]
    · exact ![2197]
    · exact ![17, 17, 17]
    · exact ![19, 19, 19]
    · exact ![23, 23, 23]
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
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
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
      exact NI23N1
      exact NI23N2
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I3N0, I5N0, I7N0, I7N1, I17N0, I17N1, I19N0, I23N0, I23N1, I23N2, I31N1]
  Il := ![[I2N0, I2N0, I2N0], [I3N0, I3N0, I3N0], [I5N0], [I7N0, I7N1], [], [], [I17N0, I17N0, I17N1], [I19N0, I19N0, I19N0], [I23N0, I23N1, I23N2], [], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
