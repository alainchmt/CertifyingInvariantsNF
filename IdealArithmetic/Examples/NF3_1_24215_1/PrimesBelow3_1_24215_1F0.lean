
import IdealArithmetic.Examples.NF3_1_24215_1.RI3_1_24215_1
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
  c := ![482, -448, -278]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![241, -224, -139]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [2, 2, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [2, 1], [0, 1]]
 g := ![![[1]], ![[1]], ![[1]]]
 h' := ![![[1, 1], [0, 1]], ![[2, 1], [1, 1]], ![[0, 1], [2, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], []]
 b := ![[], [1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [2, 2, 0, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16860, -27909, 6951]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5620, -9303, 2317]
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


def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-70, -3, -4]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-70, -3, -4]] 
 ![![5, 0, 0], ![2, 1, 0], ![1, 0, 1]] where
  M :=![![![-70, -3, -4], ![-52, -2, -3], ![-39, -1, -2]]]
  hmulB := by decide  
  f := ![![![-1, 2, -1]], ![![-3, 4, 0]], ![![5, -9, 3]]]
  g := ![![![-12, -3, -4], ![-9, -2, -3], ![-7, -1, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-1, 1, 0]] 
 ![![5, 0, 0], ![4, 1, 0], ![4, 0, 1]] where
  M :=![![![-1, 1, 0], ![0, -1, 1], ![13, -17, -1]]]
  hmulB := by decide  
  f := ![![![-18, -1, -1]], ![![-17, -1, -1]], ![![-17, 0, -1]]]
  g := ![![![-1, 1, 0], ![0, -1, 1], ![17, -17, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-70, -3, -4]] ![![-1, 1, 0]]
  ![![18, 1, 1]] where
 M := ![![![18, 1, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![18, 1, 1]] ![![-1, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![-5, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1018, -43, -58]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-1018, -43, -58]] 
 ![![7, 0, 0], ![0, 7, 0], ![5, 4, 1]] where
  M :=![![![-1018, -43, -58], ![-754, -32, -43], ![-559, -23, -32]]]
  hmulB := by decide  
  f := ![![![-5, 6, 1]], ![![13, -22, 6]], ![![15, -21, 1]]]
  g := ![![![-104, 27, -58], ![-77, 20, -43], ![-57, 15, -32]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [5, 5, 1] where
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
 g := ![![[1, 1], [2, 1]], ![[3, 6], [4, 6]]]
 h' := ![![[2, 6], [4, 6], [0, 1]], ![[0, 1], [2, 1], [2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [6, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [5, 5, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3755, -76, 107]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![460, -72, 107]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -6, -1]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![5, -6, -1]] 
 ![![7, 0, 0], ![3, 1, 0], ![5, 0, 1]] where
  M :=![![![5, -6, -1], ![-13, 22, -6], ![-78, 89, 22]]]
  hmulB := by decide  
  f := ![![![1018, 43, 58]], ![![544, 23, 31]], ![![807, 34, 46]]]
  g := ![![![4, -6, -1], ![-7, 22, -6], ![-65, 89, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-1018, -43, -58]] ![![5, -6, -1]]
  ![![7, 0, 0]] where
 M := ![![![-7, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-281, -12, -16]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-281, -12, -16]] 
 ![![11, 0, 0], ![0, 11, 0], ![10, 9, 1]] where
  M :=![![![-281, -12, -16], ![-208, -9, -12], ![-156, -4, -9]]]
  hmulB := by decide  
  f := ![![![-3, 4, 0]], ![![0, -3, 4]], ![![2, -5, 3]]]
  g := ![![![-11, 12, -16], ![-8, 9, -12], ![-6, 7, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [10, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 10], [0, 1]]
 g := ![![[8, 1], [0, 9], [1]], ![[5, 10], [6, 2], [1]]]
 h' := ![![[8, 10], [0, 10], [1, 8], [0, 1]], ![[0, 1], [3, 1], [10, 3], [8, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [4, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [10, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-64, 224, -167]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![146, 157, -167]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -4, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![3, -4, 0]] 
 ![![11, 0, 0], ![2, 1, 0], ![7, 0, 1]] where
  M :=![![![3, -4, 0], ![0, 3, -4], ![-52, 68, 3]]]
  hmulB := by decide  
  f := ![![![281, 12, 16]], ![![70, 3, 4]], ![![193, 8, 11]]]
  g := ![![![1, -4, 0], ![2, 3, -4], ![-19, 68, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-281, -12, -16]] ![![3, -4, 0]]
  ![![11, 0, 0]] where
 M := ![![![-11, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 1, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![0, 1, 0]] 
 ![![13, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![0, 1, 0], ![0, 0, 1], ![13, -17, 0]]]
  hmulB := by decide  
  f := ![![![17, 0, 1]], ![![1, 0, 0]], ![![0, 1, 0]]]
  g := ![![![0, 1, 0], ![0, 0, 1], ![1, -17, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![544, 23, 31]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![544, 23, 31]] 
 ![![13, 0, 0], ![3, 1, 0], ![4, 0, 1]] where
  M :=![![![544, 23, 31], ![403, 17, 23], ![299, 12, 17]]]
  hmulB := by decide  
  f := ![![![13, -19, 2]], ![![5, -6, -1]], ![![-15, 21, -1]]]
  g := ![![![27, 23, 31], ![20, 17, 23], ![15, 12, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -2, -1]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![2, -2, -1]] 
 ![![13, 0, 0], ![10, 1, 0], ![4, 0, 1]] where
  M :=![![![2, -2, -1], ![-13, 19, -2], ![-26, 21, 19]]]
  hmulB := by decide  
  f := ![![![-403, -17, -23]], ![![-333, -14, -19]], ![![-141, -6, -8]]]
  g := ![![![2, -2, -1], ![-15, 19, -2], ![-24, 21, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![0, 1, 0]] ![![544, 23, 31]]
  ![![403, 17, 23]] where
 M := ![![![403, 17, 23]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![403, 17, 23]] ![![2, -2, -1]]
  ![![13, 0, 0]] where
 M := ![![![-13, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -3, -5]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![5, -3, -5]] 
 ![![17, 0, 0], ![0, 17, 0], ![16, 4, 1]] where
  M :=![![![5, -3, -5], ![-65, 90, -3], ![-39, -14, 90]]]
  hmulB := by decide  
  f := ![![![474, 20, 27]], ![![351, 15, 20]], ![![544, 23, 31]]]
  g := ![![![5, 1, -5], ![-1, 6, -3], ![-87, -22, 90]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [4, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 16], [0, 1]]
 g := ![![[12, 13], [9], [9], [1]], ![[0, 4], [9], [9], [1]]]
 h' := ![![[3, 16], [7, 9], [14, 3], [13, 3], [0, 1]], ![[0, 1], [0, 8], [6, 14], [5, 14], [3, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [2, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [4, 14, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![30, -35, -30]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![30, 5, -30]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-474, -20, -27]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-474, -20, -27]] 
 ![![17, 0, 0], ![13, 1, 0], ![1, 0, 1]] where
  M :=![![![-474, -20, -27], ![-351, -15, -20], ![-260, -11, -15]]]
  hmulB := by decide  
  f := ![![![-5, 3, 5]], ![![0, -3, 4]], ![![2, 1, -5]]]
  g := ![![![-11, -20, -27], ![-8, -15, -20], ![-6, -11, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![5, -3, -5]] ![![-474, -20, -27]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24, -25, -10]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![24, -25, -10]] 
 ![![19, 0, 0], ![0, 19, 0], ![9, 12, 1]] where
  M :=![![![24, -25, -10], ![-130, 194, -25], ![-325, 295, 194]]]
  hmulB := by decide  
  f := ![![![-2369, -100, -135]], ![![-1755, -74, -100]], ![![-2299, -97, -131]]]
  g := ![![![6, 5, -10], ![5, 26, -25], ![-109, -107, 194]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [18, 5, 1] where
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
 g := ![![[14, 7], [9, 4], [6], [1]], ![[17, 12], [8, 15], [6], [1]]]
 h' := ![![[14, 18], [9, 8], [7, 17], [1, 14], [0, 1]], ![[0, 1], [7, 11], [17, 2], [7, 5], [14, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [9, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [18, 5, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![518, -500, 351]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-139, -248, 351]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2369, 100, 135]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![2369, 100, 135]] 
 ![![19, 0, 0], ![7, 1, 0], ![8, 0, 1]] where
  M :=![![![2369, 100, 135], ![1755, 74, 100], ![1300, 55, 74]]]
  hmulB := by decide  
  f := ![![![-24, 25, 10]], ![![-2, -1, 5]], ![![7, -5, -6]]]
  g := ![![![31, 100, 135], ![23, 74, 100], ![17, 55, 74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![24, -25, -10]] ![![2369, 100, 135]]
  ![![19, 0, 0]] where
 M := ![![![-19, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [3, 11, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 20, 19], [18, 2, 4], [0, 1]]
 g := ![![[11, 12, 6], [9, 11, 6], [7, 8, 1], []], ![[12, 4, 8, 11], [20, 11, 19, 22], [5, 10, 16, 7], [14, 16]], ![[18, 5, 6, 18], [16, 13], [15, 6, 3, 13], [6, 16]]]
 h' := ![![[13, 20, 19], [19, 10, 12], [2, 14, 11], [0, 0, 1], [0, 1]], ![[18, 2, 4], [17, 14, 7], [17, 6, 12], [12, 19, 2], [13, 20, 19]], ![[0, 1], [7, 22, 4], [9, 3], [7, 4, 20], [18, 2, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 15], []]
 b := ![[], [10, 13, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [3, 11, 15, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2737, 3565, 207]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-119, 155, 9]
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


def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -1, -1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-17, -1, -1]] 
 ![![29, 0, 0], ![4, 1, 0], ![13, 0, 1]] where
  M :=![![![-17, -1, -1], ![-13, 0, -1], ![-13, 4, 0]]]
  hmulB := by decide  
  f := ![![![-4, 4, -1]], ![![-1, 1, 0]], ![![0, -1, 0]]]
  g := ![![![0, -1, -1], ![0, 0, -1], ![-1, 4, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-2, 1, 0]] 
 ![![29, 0, 0], ![27, 1, 0], ![25, 0, 1]] where
  M :=![![![-2, 1, 0], ![0, -2, 1], ![13, -17, -2]]]
  hmulB := by decide  
  f := ![![![-21, -2, -1]], ![![-20, -2, -1]], ![![-19, -1, -1]]]
  g := ![![![-1, 1, 0], ![1, -2, 1], ![18, -17, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-17, -1, -1]] ![![-2, 1, 0]]
  ![![21, 2, 1]] where
 M := ![![![21, 2, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![21, 2, 1]] ![![-2, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![-29, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18, -1, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![18, -1, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![18, 30, 1]] where
  M :=![![![18, -1, 1], ![13, 1, -1], ![-13, 30, 1]]]
  hmulB := by decide  
  f := ![![![1, 1, 0]], ![![0, 1, 1]], ![![1, 1, 1]]]
  g := ![![![0, -1, 1], ![1, 1, -1], ![-1, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [17, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 30], [0, 1]]
 g := ![![[15, 1], [28, 9], [14, 1], [24, 1]], ![[8, 30], [27, 22], [7, 30], [17, 30]]]
 h' := ![![[24, 30], [20, 30], [10, 3], [26, 1], [0, 1]], ![[0, 1], [27, 1], [20, 28], [19, 30], [24, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [2, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [17, 7, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![69, -9, -53]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![33, 51, -53]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![1, 1, 0]] 
 ![![31, 0, 0], ![1, 1, 0], ![30, 0, 1]] where
  M :=![![![1, 1, 0], ![0, 1, 1], ![13, -17, 1]]]
  hmulB := by decide  
  f := ![![![18, -1, 1]], ![![1, 0, 0]], ![![17, 0, 1]]]
  g := ![![![0, 1, 0], ![-1, 1, 1], ![0, -17, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![18, -1, 1]] ![![1, 1, 0]]
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


lemma PB45I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB45I0 : PrimesBelowBoundCertificateInterval O 1 31 45 where
  m := 11
  g := ![1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB45I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0]
    · exact ![I5N0, I5N1, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
    · exact ![I29N0, I29N1, I29N1]
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
    · exact ![27]
    · exact ![5, 5, 5]
    · exact ![49, 7]
    · exact ![121, 11]
    · exact ![13, 13, 13]
    · exact ![289, 17]
    · exact ![361, 19]
    · exact ![12167]
    · exact ![29, 29, 29]
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
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
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
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I3N0, I5N0, I5N1, I7N1, I11N1, I13N0, I13N1, I13N2, I17N1, I19N1, I29N0, I29N1, I31N1]
  Il := ![[I2N0], [I3N0], [I5N0, I5N1, I5N1], [I7N1], [I11N1], [I13N0, I13N1, I13N2], [I17N1], [I19N1], [], [I29N0, I29N1, I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
