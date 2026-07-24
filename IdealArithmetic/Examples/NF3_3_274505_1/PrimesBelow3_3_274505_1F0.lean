
import IdealArithmetic.Examples.NF3_3_274505_1.RI3_3_274505_1
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
  c := ![-43272, -29100, -4362]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21636, -14550, -2181]
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

instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 0, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-5, 0, 1]] 
 ![![3, 0, 0], ![0, 3, 0], ![1, 0, 1]] where
  M :=![![![-5, 0, 1], ![109, 51, 1], ![109, 165, 52]]]
  hmulB := by decide  
  f := ![![![-829, -55, 17]], ![![1853, 123, -38]], ![![-1657, -110, 34]]]
  g := ![![![-2, 0, 1], ![36, 17, 1], ![19, 55, 52]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2], [0, 1]]
 g := ![![[1, 1]], ![[2, 2]]]
 h' := ![![[1, 2], [0, 1]], ![[0, 1], [1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [2, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-326, 813, 505]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-277, 271, 505]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-829, -55, 17]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-829, -55, 17]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![-829, -55, 17], ![1853, 123, -38], ![-4142, -275, 85]]]
  hmulB := by decide  
  f := ![![![-5, 0, 1]], ![![33, 17, 1]], ![![33, 55, 18]]]
  g := ![![![-251, -55, 17], ![561, 123, -38], ![-1254, -275, 85]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-5, 0, 1]] ![![-829, -55, 17]]
  ![![3, 0, 0]] where
 M := ![![![3, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3367, -223, 69]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-3367, -223, 69]] 
 ![![5, 0, 0], ![1, 1, 0], ![4, 0, 1]] where
  M :=![![![-3367, -223, 69], ![7521, 497, -154], ![-16786, -1103, 343]]]
  hmulB := by decide  
  f := ![![![609, 382, 49]], ![![1190, 747, 96]], ![![9883, 6201, 796]]]
  g := ![![![-684, -223, 69], ![1528, 497, -154], ![-3411, -1103, 343]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39, -13, 2]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-39, -13, 2]] 
 ![![5, 0, 0], ![4, 1, 0], ![4, 0, 1]] where
  M :=![![![-39, -13, 2], ![218, 73, -11], ![-1199, -398, 62]]]
  hmulB := by decide  
  f := ![![![148, 10, -3]], ![![53, 4, -1]], ![![271, 21, -5]]]
  g := ![![![1, -13, 2], ![-6, 73, -11], ![29, -398, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-3367, -223, 69]] ![![-39, -13, 2]]
  ![![-32, 30, -3]] where
 M := ![![![-32, 30, -3]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-32, 30, -3]] ![![-39, -13, 2]]
  ![![5, 0, 0]] where
 M := ![![![11385, 3800, -580]]]
 hmul := by decide  
 g := ![![![![2277, 760, -116]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-91, -16, 3]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-91, -16, 3]] 
 ![![7, 0, 0], ![4, 1, 0], ![5, 0, 1]] where
  M :=![![![-91, -16, 3], ![327, 77, -13], ![-1417, -401, 64]]]
  hmulB := by decide  
  f := ![![![285, 179, 23]], ![![521, 327, 42]], ![![3349, 2102, 270]]]
  g := ![![![-6, -16, 3], ![12, 77, -13], ![-19, -401, 64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28, 17, 2]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![28, 17, 2]] 
 ![![7, 0, 0], ![5, 1, 0], ![3, 0, 1]] where
  M :=![![![28, 17, 2], ![218, 140, 19], ![2071, 1282, 159]]]
  hmulB := by decide  
  f := ![![![-2098, -139, 43]], ![![-829, -55, 17]], ![![-2394, -158, 49]]]
  g := ![![![-9, 17, 2], ![-77, 140, 19], ![-688, 1282, 159]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-91, -16, 3]] ![![-91, -16, 3]]
  ![![-1202, -979, 127]] where
 M := ![![![-1202, -979, 127]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![-1202, -979, 127]] ![![28, 17, 2]]
  ![![7, 0, 0]] where
 M := ![![![15939, 5320, -812]]]
 hmul := by decide  
 g := ![![![![2277, 760, -116]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1092, 69, -22]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![1092, 69, -22]] 
 ![![11, 0, 0], ![1, 1, 0], ![10, 0, 1]] where
  M :=![![![1092, 69, -22], ![-2398, -140, 47], ![5123, 234, -93]]]
  hmulB := by decide  
  f := ![![![2022, 1269, 163]], ![![1799, 1129, 145]], ![![16028, 10059, 1292]]]
  g := ![![![113, 69, -22], ![-248, -140, 47], ![529, 234, -93]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 8, 1]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![13, 8, 1]] 
 ![![11, 0, 0], ![10, 1, 0], ![10, 0, 1]] where
  M :=![![![13, 8, 1], ![109, 69, 9], ![981, 613, 78]]]
  hmulB := by decide  
  f := ![![![135, 11, -3]], ![![93, 7, -2]], ![![202, 21, -5]]]
  g := ![![![-7, 8, 1], ![-61, 69, 9], ![-539, 613, 78]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![1092, 69, -22]] ![![13, 8, 1]]
  ![![135, 11, -3]] where
 M := ![![![135, 11, -3]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![135, 11, -3]] ![![13, 8, 1]]
  ![![11, 0, 0]] where
 M := ![![![11, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)
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


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [5, 8, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 9, 3], [8, 3, 10], [0, 1]]
 g := ![![[0, 0, 3], [7, 12], [1]], ![[1, 10, 6, 1], [], [8, 12, 4, 1]], ![[3, 10, 10, 9], [12, 12], [9, 12, 8, 12]]]
 h' := ![![[0, 9, 3], [3, 3, 9], [8, 5, 8], [0, 1]], ![[8, 3, 10], [1, 1, 10], [12, 6], [0, 9, 3]], ![[0, 1], [6, 9, 7], [12, 2, 5], [8, 3, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 12], []]
 b := ![[], [4, 1, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [5, 8, 5, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-227565, -7436, -25155]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17505, -572, -1935]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-152, -53, 8]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-152, -53, 8]] 
 ![![17, 0, 0], ![0, 17, 0], ![15, 4, 1]] where
  M :=![![![-152, -53, 8], ![872, 296, -45], ![-4905, -1648, 251]]]
  hmulB := by decide  
  f := ![![![-8, -7, -1]], ![![-109, -64, -8]], ![![-84, -54, -7]]]
  g := ![![![-16, -5, 8], ![91, 28, -45], ![-510, -156, 251]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [15, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 16], [0, 1]]
 g := ![![[3, 8], [4], [2], [1]], ![[0, 9], [4], [2], [1]]]
 h' := ![![[6, 16], [4, 5], [8, 2], [2, 6], [0, 1]], ![[0, 1], [0, 12], [3, 15], [4, 11], [6, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [4, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [15, 11, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![354, 1162, 469]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-393, -42, 469]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, 7, 1]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![8, 7, 1]] 
 ![![17, 0, 0], ![12, 1, 0], ![9, 0, 1]] where
  M :=![![![8, 7, 1], ![109, 64, 8], ![872, 557, 72]]]
  hmulB := by decide  
  f := ![![![152, 53, -8]], ![![56, 20, -3]], ![![369, 125, -19]]]
  g := ![![![-5, 7, 1], ![-43, 64, 8], ![-380, 557, 72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-152, -53, 8]] ![![8, 7, 1]]
  ![![17, 0, 0]] where
 M := ![![![-17, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![81, 26, -4]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![81, 26, -4]] 
 ![![19, 0, 0], ![0, 19, 0], ![13, 3, 1]] where
  M :=![![![81, 26, -4], ![-436, -143, 22], ![2398, 796, -121]]]
  hmulB := by decide  
  f := ![![![11, 2, 0]], ![![0, 11, 2]], ![![19, 9, 1]]]
  g := ![![![7, 2, -4], ![-38, -11, 22], ![209, 61, -121]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [10, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 18], [0, 1]]
 g := ![![[17, 17], [], [1], [1]], ![[15, 2], [], [1], [1]]]
 h' := ![![[1, 18], [0, 6], [14], [9, 1], [0, 1]], ![[0, 1], [6, 13], [14], [10, 18], [1, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [18, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [10, 18, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![337, 259, 42]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11, 7, 42]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 2, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![11, 2, 0]] 
 ![![19, 0, 0], ![15, 1, 0], ![3, 0, 1]] where
  M :=![![![11, 2, 0], ![0, 11, 2], ![218, 112, 13]]]
  hmulB := by decide  
  f := ![![![81, 26, -4]], ![![41, 13, -2]], ![![139, 46, -7]]]
  g := ![![![-1, 2, 0], ![-9, 11, 2], ![-79, 112, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![81, 26, -4]] ![![11, 2, 0]]
  ![![19, 0, 0]] where
 M := ![![![19, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 1, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![3, 1, 0]] 
 ![![23, 0, 0], ![3, 1, 0], ![14, 0, 1]] where
  M :=![![![3, 1, 0], ![0, 3, 1], ![109, 56, 4]]]
  hmulB := by decide  
  f := ![![![44, 4, -1]], ![![1, 0, 0]], ![![41, 5, -1]]]
  g := ![![![0, 1, 0], ![-1, 3, 1], ![-5, 56, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, 3, -1]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![51, 3, -1]] 
 ![![23, 0, 0], ![16, 1, 0], ![20, 0, 1]] where
  M :=![![![51, 3, -1], ![-109, -5, 2], ![218, 3, -3]]]
  hmulB := by decide  
  f := ![![![9, 6, 1]], ![![11, 7, 1]], ![![41, 27, 4]]]
  g := ![![![1, 3, -1], ![-3, -5, 2], ![10, 3, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![3, 1, 0]] ![![3, 1, 0]]
  ![![9, 6, 1]] where
 M := ![![![9, 6, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI23N1 : IdealMulLeCertificate' Table 
  ![![9, 6, 1]] ![![51, 3, -1]]
  ![![23, 0, 0]] where
 M := ![![![23, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [2, 23, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 20, 12], [17, 8, 17], [0, 1]]
 g := ![![[28, 26, 4], [26, 5], [15, 11, 13], [1]], ![[10, 13, 4, 2], [2, 25], [13, 2, 2, 14], [20, 5, 2, 17]], ![[1, 11, 28, 2], [16, 7], [24, 0, 7, 27], [2, 27, 1, 12]]]
 h' := ![![[2, 20, 12], [7, 2, 2], [28, 14, 11], [27, 6, 19], [0, 1]], ![[17, 8, 17], [2, 23, 11], [21, 27, 24], [26, 2, 21], [2, 20, 12]], ![[0, 1], [13, 4, 16], [25, 17, 23], [8, 21, 18], [17, 8, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 3], []]
 b := ![[], [17, 18, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [2, 23, 10, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1299316, 800284, 90741]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![44804, 27596, 3129]
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


def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-305, -18, 6]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-305, -18, 6]] 
 ![![31, 0, 0], ![16, 1, 0], ![23, 0, 1]] where
  M :=![![![-305, -18, 6], ![654, 31, -12], ![-1308, -18, 19]]]
  hmulB := by decide  
  f := ![![![373, 234, 30]], ![![298, 187, 24]], ![![1205, 756, 97]]]
  g := ![![![-5, -18, 6], ![14, 31, -12], ![-47, -18, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1269, 84, -26]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![1269, 84, -26]] 
 ![![31, 0, 0], ![29, 1, 0], ![27, 0, 1]] where
  M :=![![![1269, 84, -26], ![-2834, -187, 58], ![6322, 414, -129]]]
  hmulB := by decide  
  f := ![![![111, 72, 10]], ![![139, 89, 12]], ![![385, 246, 33]]]
  g := ![![![-15, 84, -26], ![33, -187, 58], ![-71, 414, -129]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-305, -18, 6]] ![![-305, -18, 6]]
  ![![73405, 4824, -1500]] where
 M := ![![![73405, 4824, -1500]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI31N1 : IdealMulLeCertificate' Table 
  ![![73405, 4824, -1500]] ![![1269, 84, -26]]
  ![![31, 0, 0]] where
 M := ![![![69996729, 4642932, -1435238]]]
 hmul := by decide  
 g := ![![![![2257959, 149772, -46298]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)


lemma PB117I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB117I0 : PrimesBelowBoundCertificateInterval O 1 31 117 where
  m := 11
  g := ![1, 2, 3, 3, 3, 1, 2, 2, 3, 1, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB117I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0, I3N1]
    · exact ![I5N0, I5N1, I5N1]
    · exact ![I7N0, I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N1]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N0, I23N1]
    · exact ![I29N0]
    · exact ![I31N0, I31N0, I31N1]
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
    · exact ![9, 3]
    · exact ![5, 5, 5]
    · exact ![7, 7, 7]
    · exact ![11, 11, 11]
    · exact ![2197]
    · exact ![289, 17]
    · exact ![361, 19]
    · exact ![23, 23, 23]
    · exact ![24389]
    · exact ![31, 31, 31]
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
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I3N0, I3N1, I5N0, I5N1, I7N0, I7N1, I11N0, I11N1, I17N1, I19N1, I23N0, I23N1, I31N0, I31N1]
  Il := ![[I2N0], [I3N0, I3N1], [I5N0, I5N1, I5N1], [I7N0, I7N0, I7N1], [I11N0, I11N1, I11N1], [], [I17N1], [I19N1], [I23N0, I23N0, I23N1], [], [I31N0, I31N0, I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
