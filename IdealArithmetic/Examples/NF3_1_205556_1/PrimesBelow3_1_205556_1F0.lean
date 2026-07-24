
import IdealArithmetic.Examples.NF3_1_205556_1.RI3_1_205556_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38872838, 14579701, 1412662]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![38872838, 14579701, 1412662]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![38872838, 14579701, 1412662], ![401196008, 150473136, 14579701], ![4140635084, 1552992387, 150473136]]]
  hmulB := by decide  
  f := ![![![-61791, -8142, 1369]], ![![194398, 23180, -4071]], ![![-1156164, -127211, 23180]]]
  g := ![![![19436419, 14579701, 1412662], ![200598004, 150473136, 14579701], ![2070317542, 1552992387, 150473136]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![1, 1, 0]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![1, 1, 0], ![0, 1, 1], ![284, 79, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![1, -1, 0]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![-1, 0, 2]], ![![0, 1, 0], ![-1, 1, 1], ![102, 79, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![38872838, 14579701, 1412662]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0], ![-52, -5, 1]] where
 M := ![![![77745676, 29159402, 2825324], ![440068846, 165052837, 15992363]]]
 hmul := by decide  
 g := ![![![![-933058, 10752211, 2178160], ![-1530996, 0, 0]], ![![-5281603, 60861416, 12329182], ![-8666001, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![-52, -5, 1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![-104, -10, 2], ![232, 22, -4]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![1, 1, 0]]], ![![![-52, -5, 1]], ![![116, 11, -2]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
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


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [1, 0, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 0, 1], [2, 2, 2], [0, 1]]
 g := ![![[1]], ![[0, 1, 1, 1]], ![[2, 2, 2, 2]]]
 h' := ![![[2, 0, 1], [0, 1]], ![[2, 2, 2], [2, 0, 1]], ![[0, 1], [2, 2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 2], []]
 b := ![[], [1, 1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [1, 0, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-147111, -63642, -7170]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-49037, -21214, -2390]
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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [4, 0, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1, 2], [0, 3, 3], [0, 1]]
 g := ![![[1, 1, 1], []], ![[4, 4, 4, 3], [3, 4]], ![[0, 4, 0, 3], [2, 4]]]
 h' := ![![[1, 1, 2], [0, 0, 1], [0, 1]], ![[0, 3, 3], [4, 1, 3], [1, 1, 2]], ![[0, 1], [2, 4, 1], [0, 3, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 3], []]
 b := ![[], [3, 3, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [4, 0, 4, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![960495, 885740, 156715]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![192099, 177148, 31343]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-54, -5, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-54, -5, 1]] 
 ![![7, 0, 0], ![0, 7, 0], ![2, 2, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-54, -5, 1], ![284, 25, -5], ![-1420, -111, 25]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![8, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -2, 7]], ![![-8, -1, 1], ![42, 5, -5], ![-210, -23, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [6, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 6], [0, 1]]
 g := ![![[3, 2], [3, 1]], ![[2, 5], [6, 6]]]
 h' := ![![[3, 6], [3, 3], [0, 1]], ![[0, 1], [5, 4], [3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [4, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [6, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3278, 2, 204]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![410, -58, 204]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-2, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-2, 1, 0]] 
 ![![7, 0, 0], ![5, 1, 0], ![3, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-2, 1, 0], ![0, -2, 1], ![284, 79, -2]]]
  hmulB := by decide  
  f := ![![![13, -6, 0], ![42, 0, 0]], ![![11, -5, 0], ![36, 0, 0]], ![![5, -2, 0], ![16, 1, 0]]]
  g := ![![![1, 0, 0], ![-5, 7, 0], ![-3, 0, 7]], ![![-1, 1, 0], ![1, -2, 1], ![-15, 79, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![-54, -5, 1]] ![![7, 0, 0], ![-2, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![-14, 7, 0]], ![![-378, -35, 7], ![392, 35, -7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![-2, 1, 0]]], ![![![-54, -5, 1]], ![![56, 5, -1]]]]
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


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [3, 6, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 9, 6], [6, 1, 5], [0, 1]]
 g := ![![[5, 10, 9], [9, 2, 1], []], ![[5, 10, 4, 7], [10, 3, 4, 6], [4, 3]], ![[6, 0, 7, 9], [0, 5, 1, 9], [5, 3]]]
 h' := ![![[7, 9, 6], [6, 6, 3], [0, 0, 1], [0, 1]], ![[6, 1, 5], [5, 3, 6], [4, 5, 1], [7, 9, 6]], ![[0, 1], [6, 2, 2], [10, 6, 9], [6, 1, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 4], []]
 b := ![[], [2, 6, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [3, 6, 9, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1592085, -1020503, -153087]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-144735, -92773, -13917]
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


def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9025, -1246, 36]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![9025, -1246, 36]] 
 ![![13, 0, 0], ![6, 1, 0], ![3, 0, 1]] where
  M :=![![![9025, -1246, 36], ![10224, 11869, -1246], ![-353864, -88210, 11869]]]
  hmulB := by decide  
  f := ![![![30963501, 11613214, 1125232]], ![![38872838, 14579701, 1412662]], ![![260849483, 97834572, 9479425]]]
  g := ![![![1261, -1246, 36], ![-4404, 11869, -1246], ![10753, -88210, 11869]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15467, -1257, 267]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-15467, -1257, 267]] 
 ![![13, 0, 0], ![10, 1, 0], ![4, 0, 1]] where
  M :=![![![-15467, -1257, 267], ![75828, 5626, -1257], ![-356988, -23475, 5626]]]
  hmulB := by decide  
  f := ![![![2143801, 804057, 77907]], ![![3351046, 1256848, 121779]], ![![18225184, 6835563, 662314]]]
  g := ![![![-305, -1257, 267], ![1892, 5626, -1257], ![-11134, -23475, 5626]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![9025, -1246, 36]] ![![-15467, -1257, 267]]
  ![![-246922931, -19199521, 4178433]] where
 M := ![![![-246922931, -19199521, 4178433]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-246922931, -19199521, 4178433]] ![![-15467, -1257, 267]]
  ![![13, 0, 0]] where
 M := ![![![871645255585, 104276904446, -18286760622]]]
 hmul := by decide  
 g := ![![![![67049635045, 8021300342, -1406673894]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N1
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [7, 6, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 9, 14], [14, 7, 3], [0, 1]]
 g := ![![[10, 2, 16], [4, 4], [12, 1], []], ![[9, 9, 6, 6], [0, 16], [4, 15], [3, 9]], ![[13, 11, 13, 10], [13, 4], [1, 13], [14, 9]]]
 h' := ![![[15, 9, 14], [7, 11, 13], [1, 6, 2], [0, 0, 1], [0, 1]], ![[14, 7, 3], [2, 6, 7], [6, 7, 13], [0, 2, 7], [15, 9, 14]], ![[0, 1], [7, 0, 14], [9, 4, 2], [13, 15, 9], [14, 7, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 15], []]
 b := ![[], [4, 8, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [7, 6, 5, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-145401, -62322, -6936]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8553, -3666, -408]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55, 5, -1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![55, 5, -1]] 
 ![![19, 0, 0], ![10, 1, 0], ![14, 0, 1]] where
  M :=![![![55, 5, -1], ![-284, -24, 5], ![1420, 111, -24]]]
  hmulB := by decide  
  f := ![![![21, 9, 1]], ![![26, 10, 1]], ![![150, 59, 6]]]
  g := ![![![1, 5, -1], ![-6, -24, 5], ![34, 111, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-7, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-7, 1, 0]] 
 ![![19, 0, 0], ![12, 1, 0], ![8, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-7, 1, 0], ![0, -7, 1], ![284, 79, -7]]]
  hmulB := by decide  
  f := ![![![106, -15, 0], ![285, 0, 0]], ![![64, -9, 0], ![172, 0, 0]], ![![52, -7, 0], ![140, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 19, 0], ![-8, 0, 19]], ![![-1, 1, 0], ![4, -7, 1], ![-32, 79, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-3, 1, 0]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-3, 1, 0]] 
 ![![19, 0, 0], ![16, 1, 0], ![10, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-3, 1, 0], ![0, -3, 1], ![284, 79, -3]]]
  hmulB := by decide  
  f := ![![![46, -15, 0], ![285, 0, 0]], ![![40, -13, 0], ![248, 0, 0]], ![![28, -9, 0], ![174, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 19, 0], ![-10, 0, 19]], ![![-1, 1, 0], ![2, -3, 1], ![-50, 79, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![55, 5, -1]] ![![19, 0, 0], ![-7, 1, 0]]
  ![![19, 0, 0], ![-51, 3, 1]] where
 M := ![![![1045, 95, -19], ![-669, -59, 12]]]
 hmul := by decide  
 g := ![![![![55, 5, -1], ![0, 0, 0]], ![![-3, -5, 0], ![12, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![-51, 3, 1]] ![![19, 0, 0], ![-3, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-57, 19, 0]], ![![-969, 57, 19], ![437, 19, 0]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-3, 1, 0]]], ![![![-51, 3, 1]], ![![23, 1, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [2, 10, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 14, 13], [13, 8, 10], [0, 1]]
 g := ![![[18, 11, 6], [13, 14, 4], [13, 0, 1], []], ![[1, 19, 12, 18], [8, 20, 12, 1], [4, 14, 4, 4], [19, 8]], ![[6, 7, 2, 17], [11, 4, 14, 15], [0, 12, 7, 5], [22, 8]]]
 h' := ![![[10, 14, 13], [20, 12, 11], [20, 8, 21], [0, 0, 1], [0, 1]], ![[13, 8, 10], [17, 16, 14], [22, 10, 19], [16, 5, 8], [10, 14, 13]], ![[0, 1], [10, 18, 21], [12, 5, 6], [10, 18, 14], [13, 8, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 21], []]
 b := ![[], [2, 5, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [2, 10, 0, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3339853, 1260147, 109319]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![145211, 54789, 4753]
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


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [3, 24, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 1, 18], [14, 27, 11], [0, 1]]
 g := ![![[10, 18, 6], [20, 22], [13, 7, 24], [1]], ![[26, 1, 27, 3], [7, 16], [9, 11, 24, 10], [6, 2, 25, 3]], ![[16, 3, 25, 12], [22, 5], [28, 4, 13, 27], [26, 10, 18, 26]]]
 h' := ![![[28, 1, 18], [11, 18, 8], [19, 24, 15], [26, 5, 13], [0, 1]], ![[14, 27, 11], [13, 7, 18], [18, 7, 25], [10, 27, 6], [28, 1, 18]], ![[0, 1], [22, 4, 3], [1, 27, 18], [27, 26, 10], [14, 27, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 18], []]
 b := ![[], [4, 7, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [3, 24, 16, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![106778, 3277, -4669]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3682, 113, -161]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![14, 1, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![14, 1, 0]] 
 ![![31, 0, 0], ![14, 1, 0], ![21, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![14, 1, 0], ![0, 14, 1], ![284, 79, 14]]]
  hmulB := by decide  
  f := ![![![141, 10, 0], ![-310, 0, 0]], ![![42, 3, 0], ![-92, 0, 0]], ![![91, 6, 0], ![-200, 1, 0]]]
  g := ![![![1, 0, 0], ![-14, 31, 0], ![-21, 0, 31]], ![![0, 1, 0], ![-7, 14, 1], ![-36, 79, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4558291, 1709639, 165651]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![4558291, 1709639, 165651]] 
 ![![31, 0, 0], ![19, 1, 0], ![11, 0, 1]] where
  M :=![![![4558291, 1709639, 165651], ![47044884, 17644720, 1709639], ![485537476, 182106365, 17644720]]]
  hmulB := by decide  
  f := ![![![126165, 12535, -2399]], ![![55349, 5639, -1066]], ![![159605, 14414, -2895]]]
  g := ![![![-959581, 1709639, 165651], ![-9903575, 17644720, 1709639], ![-102212109, 182106365, 17644720]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-2, 1, 0]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-2, 1, 0]] 
 ![![31, 0, 0], ![29, 1, 0], ![27, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-2, 1, 0], ![0, -2, 1], ![284, 79, -2]]]
  hmulB := by decide  
  f := ![![![37, -18, 0], ![558, 0, 0]], ![![35, -17, 0], ![528, 0, 0]], ![![33, -16, 0], ![498, 1, 0]]]
  g := ![![![1, 0, 0], ![-29, 31, 0], ![-27, 0, 31]], ![![-1, 1, 0], ![1, -2, 1], ![-63, 79, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![14, 1, 0]] ![![4558291, 1709639, 165651]]
  ![![31, 0, 0], ![-44, 2, 1]] where
 M := ![![![141307021, 52998809, 5135181]], ![![110860958, 41579666, 4028753]]]
 hmul := by decide  
 g := ![![![![1571703, 1845393, 233528], ![-2104187, 0, 0]]], ![![![1233062, 1447784, 183212], ![-1650819, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![-44, 2, 1]] ![![31, 0, 0], ![-2, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![-62, 31, 0]], ![![-1364, 62, 31], ![372, 31, 0]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![-2, 1, 0]]], ![![![-44, 2, 1]], ![![12, 1, 0]]]]
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


lemma PB129I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB129I0 : PrimesBelowBoundCertificateInterval O 1 31 129 where
  m := 11
  g := ![3, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB129I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1]
    · exact ![I3N0]
    · exact ![I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0]
    · exact ![I29N0]
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
    · exact ![49, 7]
    · exact ![1331]
    · exact ![13, 13, 13]
    · exact ![4913]
    · exact ![19, 19, 19]
    · exact ![12167]
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
      exact NI2N1
      exact NI2N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
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
      exact NI31N2
  β := ![I2N0, I2N1, I3N0, I5N0, I7N0, I7N1, I13N0, I13N1, I19N0, I19N1, I19N2, I31N0, I31N1, I31N2]
  Il := ![[I2N0, I2N1, I2N1], [I3N0], [I5N0], [I7N0, I7N1], [], [I13N0, I13N1, I13N1], [], [I19N0, I19N1, I19N2], [], [], [I31N0, I31N1, I31N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
