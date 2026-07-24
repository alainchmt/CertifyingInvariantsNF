
import IdealArithmetic.Examples.NF3_1_42423_4.RI3_1_42423_4
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
  c := ![-5044, 2386, -2154]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2522, 1193, -1077]
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


def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![5, 1, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![5, 1, 1]] 
 ![![3, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![5, 1, 1], ![37, -1, 2], ![15, 8, -2]]]
  hmulB := by decide  
  f := ![![![11, 22, -18], ![30, 0, -12]], ![![2, 4, -3], ![5, 0, -2]], ![![2, 7, -6], ![11, 0, -4]]]
  g := ![![![1, 0, 0], ![-1, 3, 0], ![-1, 0, 3]], ![![1, 1, 1], ![12, -1, 2], ![3, 8, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![3, 1, 1]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![3, 1, 1]] 
 ![![3, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![3, 1, 1], ![37, -3, 2], ![15, 8, -4]]]
  hmulB := by decide  
  f := ![![![39, -18, -8], ![36, -6, 0]], ![![12, -6, -3], ![13, -2, 0]], ![![26, -12, -5], ![24, -4, 0]]]
  g := ![![![1, 0, 0], ![-1, 3, 0], ![-2, 0, 3]], ![![0, 1, 1], ![12, -3, 2], ![5, 8, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![5, 1, 1]] ![![3, 0, 0], ![5, 1, 1]]
  ![![3, 0, 0], ![4, 0, 1]] where
 M := ![![![9, 0, 0], ![15, 3, 3]], ![![15, 3, 3], ![77, 12, 5]]]
 hmul := by decide  
 g := ![![![![-1, 0, -1], ![3, 0, 0]], ![![1, 1, 0], ![3, 0, 0]]], ![![![1, 1, 0], ![3, 0, 0]], ![![7, 4, -3], ![14, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![4, 0, 1]] ![![3, 0, 0], ![3, 1, 1]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![9, 3, 3]], ![![12, 0, 3], ![27, 12, 0]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![3, 1, 1]]], ![![![4, 0, 1]], ![![9, 4, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 0, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-3, 0, 1]] 
 ![![5, 0, 0], ![0, 5, 0], ![2, 0, 1]] where
  M :=![![![-3, 0, 1], ![38, -10, -1], ![-23, 15, -9]]]
  hmulB := by decide  
  f := ![![![21, 3, 2]], ![![73, 10, 7]], ![![22, 3, 2]]]
  g := ![![![-1, 0, 1], ![8, -2, -1], ![-1, 3, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [2, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 4], [0, 1]]
 g := ![![[2, 1], [1]], ![[3, 4], [1]]]
 h' := ![![[1, 4], [3, 1], [0, 1]], ![[0, 1], [4, 4], [1, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [2, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [2, 4, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![218552, 11015, -23624]
  a := ![1, -64, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![53160, 2203, -23624]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, 3, 2]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![21, 3, 2]] 
 ![![5, 0, 0], ![1, 1, 0], ![4, 0, 1]] where
  M :=![![![21, 3, 2], ![73, 10, 7], ![68, 9, 6]]]
  hmulB := by decide  
  f := ![![![-3, 0, 1]], ![![7, -2, 0]], ![![-7, 3, -1]]]
  g := ![![![2, 3, 2], ![7, 10, 7], ![7, 9, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-3, 0, 1]] ![![21, 3, 2]]
  ![![5, 0, 0]] where
 M := ![![![5, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, -2, -1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![10, -2, -1]] 
 ![![7, 0, 0], ![3, 1, 0], ![5, 0, 1]] where
  M :=![![![10, -2, -1], ![-36, 15, -5], ![-53, -1, 18]]]
  hmulB := by decide  
  f := ![![![-265, -37, -25]], ![![-244, -34, -23]], ![![-308, -43, -29]]]
  g := ![![![3, -2, -1], ![-8, 15, -5], ![-20, -1, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-2, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-2, 1, 0]] 
 ![![7, 0, 0], ![5, 1, 0], ![6, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-2, 1, 0], ![-1, -1, 3], ![38, -7, -3]]]
  hmulB := by decide  
  f := ![![![-9, -13, 36], ![7, -84, 0]], ![![-7, -8, 24], ![1, -56, 0]], ![![-8, -11, 31], ![5, -72, 0]]]
  g := ![![![1, 0, 0], ![-5, 7, 0], ![-6, 0, 7]], ![![-1, 1, 0], ![-2, -1, 3], ![13, -7, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-1, 1, 0]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-1, 1, 0]] 
 ![![7, 0, 0], ![6, 1, 0], ![2, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-1, 1, 0], ![-1, 0, 3], ![38, -7, -2]]]
  hmulB := by decide  
  f := ![![![-34, -1, 108], ![7, -252, 0]], ![![-28, -1, 90], ![8, -210, 0]], ![![-9, -1, 31], ![7, -72, 0]]]
  g := ![![![1, 0, 0], ![-6, 7, 0], ![-2, 0, 7]], ![![-1, 1, 0], ![-1, 0, 3], ![12, -7, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![10, -2, -1]] ![![7, 0, 0], ![-2, 1, 0]]
  ![![7, 0, 0], ![7, 3, 1]] where
 M := ![![![70, -14, -7], ![-56, 19, -3]]]
 hmul := by decide  
 g := ![![![![3, -5, -2], ![7, 0, 0]], ![![-5, 4, 0], ![-3, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![7, 3, 1]] ![![7, 0, 0], ![-1, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![-7, 7, 0]], ![![49, 21, 7], ![28, 0, 7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![-1, 1, 0]]], ![![![7, 3, 1]], ![![4, 0, 1]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N2
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


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [7, 2, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 3, 3], [10, 7, 8], [0, 1]]
 g := ![![[1, 6, 9], [7, 3, 1], []], ![[3, 4, 2, 9], [8, 1, 10, 4], [1, 9]], ![[1, 7, 2, 6], [9, 6, 3, 6], [7, 9]]]
 h' := ![![[4, 3, 3], [6, 9, 8], [0, 0, 1], [0, 1]], ![[10, 7, 8], [4, 7, 6], [9, 3, 7], [4, 3, 3]], ![[0, 1], [9, 6, 8], [7, 8, 3], [10, 7, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 4], []]
 b := ![[], [4, 7, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [7, 2, 8, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-329802, 106777, -15653]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-29982, 9707, -1423]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![6, 1, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![6, 1, 0]] 
 ![![13, 0, 0], ![6, 1, 0], ![3, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![6, 1, 0], ![-1, 7, 3], ![38, -7, 5]]]
  hmulB := by decide  
  f := ![![![56, -385, -165], ![0, 715, 0]], ![![25, -175, -75], ![1, 325, 0]], ![![12, -89, -38], ![2, 165, 0]]]
  g := ![![![1, 0, 0], ![-6, 13, 0], ![-3, 0, 13]], ![![0, 1, 0], ![-4, 7, 3], ![5, -7, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-5, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-5, 1, 0]] 
 ![![13, 0, 0], ![8, 1, 0], ![6, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-5, 1, 0], ![-1, -4, 3], ![38, -7, -6]]]
  hmulB := by decide  
  f := ![![![-4, -20, 15], ![0, -65, 0]], ![![-2, -12, 9], ![1, -39, 0]], ![![2, -10, 7], ![10, -30, 0]]]
  g := ![![![1, 0, 0], ![-8, 13, 0], ![-6, 0, 13]], ![![-1, 1, 0], ![1, -4, 3], ![10, -7, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-1, 1, 0]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-1, 1, 0]] 
 ![![13, 0, 0], ![12, 1, 0], ![4, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-1, 1, 0], ![-1, 0, 3], ![38, -7, -2]]]
  hmulB := by decide  
  f := ![![![-142, -1, 432], ![13, -1872, 0]], ![![-130, -1, 396], ![14, -1716, 0]], ![![-43, -1, 133], ![13, -576, 0]]]
  g := ![![![1, 0, 0], ![-12, 13, 0], ![-4, 0, 13]], ![![-1, 1, 0], ![-1, 0, 3], ![10, -7, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![6, 1, 0]] ![![13, 0, 0], ![-5, 1, 0]]
  ![![13, 0, 0], ![7, 5, 1]] where
 M := ![![![169, 0, 0], ![-65, 13, 0]], ![![78, 13, 0], ![-31, 2, 3]]]
 hmul := by decide  
 g := ![![![![6, -5, -1], ![13, 0, 0]], ![![-5, 1, 0], ![0, 0, 0]]], ![![![-1, -4, -1], ![13, 0, 0]], ![![-4, -1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![7, 5, 1]] ![![13, 0, 0], ![-1, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![-13, 13, 0]], ![![91, 65, 13], ![26, 0, 13]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![-1, 1, 0]]], ![![![7, 5, 1]], ![![2, 0, 1]]]]
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
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [6, 4, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 14, 6], [13, 2, 11], [0, 1]]
 g := ![![[15, 13, 4], [15, 13], [8, 1], []], ![[14, 13, 1, 6], [15, 2], [16, 4], [14, 2]], ![[3, 15, 8, 14], [6, 9], [14, 9], [9, 2]]]
 h' := ![![[12, 14, 6], [4, 8, 2], [3, 13, 9], [0, 0, 1], [0, 1]], ![[13, 2, 11], [16, 2, 1], [2, 10, 11], [9, 13, 2], [12, 14, 6]], ![[0, 1], [15, 7, 14], [0, 11, 14], [13, 4, 14], [13, 2, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 4], []]
 b := ![[], [4, 1, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [6, 4, 9, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2822, 2839, -2703]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-166, 167, -159]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0]] 
 ![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [17, 18, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 7, 18], [4, 11, 1], [0, 1]]
 g := ![![[18, 11, 5], [14, 14, 6], [2, 1], []], ![[11, 12, 5, 13], [13, 17, 3, 2], [14, 7], [7, 1]], ![[16, 4, 6, 6], [5, 10, 6, 1], [3, 11], [5, 1]]]
 h' := ![![[17, 7, 18], [9, 1, 10], [4, 4, 5], [0, 0, 1], [0, 1]], ![[4, 11, 1], [16, 7, 14], [10, 9, 13], [18, 0, 11], [17, 7, 18]], ![[0, 1], [7, 11, 14], [17, 6, 1], [7, 0, 7], [4, 11, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 16], []]
 b := ![[], [6, 10, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [17, 18, 17, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![760874, 21204, -39786]
  a := ![-1, 21, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![40046, 1116, -2094]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-11, 1, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-11, 1, 0]] 
 ![![23, 0, 0], ![12, 1, 0], ![9, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-11, 1, 0], ![-1, -10, 3], ![38, -7, -12]]]
  hmulB := by decide  
  f := ![![![7, 60, -18], ![0, 138, 0]], ![![4, 30, -9], ![1, 69, 0]], ![![8, 23, -7], ![11, 54, 0]]]
  g := ![![![1, 0, 0], ![-12, 23, 0], ![-9, 0, 23]], ![![-1, 1, 0], ![4, -10, 3], ![10, -7, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-9, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-9, 1, 0]] 
 ![![23, 0, 0], ![14, 1, 0], ![14, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-9, 1, 0], ![-1, -8, 3], ![38, -7, -10]]]
  hmulB := by decide  
  f := ![![![41, 320, -120], ![0, 920, 0]], ![![25, 192, -72], ![1, 552, 0]], ![![32, 194, -73], ![18, 560, 0]]]
  g := ![![![1, 0, 0], ![-14, 23, 0], ![-14, 0, 23]], ![![-1, 1, 0], ![3, -8, 3], ![12, -7, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, 0]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![-3, 1, 0]] 
 ![![23, 0, 0], ![20, 1, 0], ![13, 0, 1]] where
  M :=![![![-3, 1, 0], ![-1, -2, 3], ![38, -7, -4]]]
  hmulB := by decide  
  f := ![![![29, 4, 3]], ![![30, 4, 3]], ![![20, 3, 2]]]
  g := ![![![-1, 1, 0], ![0, -2, 3], ![10, -7, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![-11, 1, 0]] ![![23, 0, 0], ![-9, 1, 0]]
  ![![29, 4, 3]] where
 M := ![![![529, 0, 0], ![-207, 23, 0]], ![![-253, 23, 0], ![98, -19, 3]]]
 hmul := by decide  
 g := ![![![![-69, 23, 0]], ![![26, -11, 3]]], ![![![32, -13, 3]], ![![-7, 5, -3]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![29, 4, 3]] ![![-3, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![23, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-244, -34, -23]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-244, -34, -23]] 
 ![![29, 0, 0], ![3, 1, 0], ![15, 0, 1]] where
  M :=![![![-244, -34, -23], ![-840, -117, -79], ![-763, -107, -72]]]
  hmulB := by decide  
  f := ![![![29, -13, 5]], ![![10, -2, -1]], ![![-6, -1, 3]]]
  g := ![![![7, -34, -23], ![24, -117, -79], ![22, -107, -72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![4, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![4, 1, 0]] 
 ![![29, 0, 0], ![4, 1, 0], ![22, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![4, 1, 0], ![-1, 5, 3], ![38, -7, 3]]]
  hmulB := by decide  
  f := ![![![-311, 1539, 924], ![29, -8932, 0]], ![![-46, 209, 126], ![30, -1218, 0]], ![![-234, 1168, 701], ![8, -6776, 0]]]
  g := ![![![1, 0, 0], ![-4, 29, 0], ![-22, 0, 29]], ![![0, 1, 0], ![-3, 5, 3], ![0, -7, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-7, 1, 0]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-7, 1, 0]] 
 ![![29, 0, 0], ![22, 1, 0], ![5, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-7, 1, 0], ![-1, -6, 3], ![38, -7, -8]]]
  hmulB := by decide  
  f := ![![![61, 360, -180], ![0, 1740, 0]], ![![46, 270, -135], ![1, 1305, 0]], ![![11, 62, -31], ![2, 300, 0]]]
  g := ![![![1, 0, 0], ![-22, 29, 0], ![-5, 0, 29]], ![![-1, 1, 0], ![4, -6, 3], ![8, -7, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-244, -34, -23]] ![![29, 0, 0], ![4, 1, 0]]
  ![![29, 0, 0], ![-6, -7, 1]] where
 M := ![![![-7076, -986, -667], ![-1816, -253, -171]]]
 hmul := by decide  
 g := ![![![![-232, -20, -25], ![58, 0, 0]], ![![-56, -1, -7], ![32, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![-6, -7, 1]] ![![29, 0, 0], ![-7, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![-203, 29, 0]], ![![-174, -203, 29], ![87, 29, -29]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![-7, 1, 0]]], ![![![-6, -7, 1]], ![![3, 1, -1]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0]] 
 ![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [10, 25, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 22, 16], [11, 8, 15], [0, 1]]
 g := ![![[8, 25, 20], [1, 20, 20], [18, 7, 18], [1]], ![[28, 19, 30, 14], [28, 17, 11, 8], [18, 23, 27, 25], [5, 11, 4, 4]], ![[29, 20, 5, 15], [6, 26, 30, 30], [21, 20, 20, 29], [3, 30, 3, 27]]]
 h' := ![![[13, 22, 16], [21, 28, 19], [6, 14, 19], [21, 6, 24], [0, 1]], ![[11, 8, 15], [12, 12, 11], [1, 14, 4], [8, 7, 9], [13, 22, 16]], ![[0, 1], [1, 22, 1], [18, 3, 8], [30, 18, 29], [11, 8, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 20], []]
 b := ![[], [8, 7, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [10, 25, 7, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-63178, 16647, 1798]
  a := ![1, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2038, 537, 58]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀



lemma PB59I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB59I0 : PrimesBelowBoundCertificateInterval O 1 31 59 where
  m := 11
  g := ![1, 3, 2, 3, 1, 3, 1, 1, 3, 3, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB59I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0, I3N0, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0]
    · exact ![I19N0]
    · exact ![I23N0, I23N1, I23N2]
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0]
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
    · exact ![7, 7, 7]
    · exact ![1331]
    · exact ![13, 13, 13]
    · exact ![4913]
    · exact ![6859]
    · exact ![23, 23, 23]
    · exact ![29, 29, 29]
    · exact ![29791]
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
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I3N0, I3N1, I5N0, I5N1, I7N0, I7N1, I7N2, I13N0, I13N1, I13N2, I23N0, I23N1, I23N2, I29N0, I29N1, I29N2]
  Il := ![[I2N0], [I3N0, I3N0, I3N1], [I5N0, I5N1], [I7N0, I7N1, I7N2], [], [I13N0, I13N1, I13N2], [], [], [I23N0, I23N1, I23N2], [I29N0, I29N1, I29N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
