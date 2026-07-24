
import IdealArithmetic.Examples.NF3_3_80565_1.RI3_3_80565_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-36, 17, 8]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-36, 17, 8]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![-36, 17, 8], ![-263, 124, 59], ![-635, 300, 141]]]
  hmulB := by decide  
  f := ![![![-216, 3, 11]], ![![-191, 2, 10]], ![![-188, 4, 9]]]
  g := ![![![-22, 17, 8], ![-161, 124, 59], ![-388, 300, 141]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-216, 3, 11]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-216, 3, 11]] 
 ![![2, 0, 0], ![0, 2, 0], ![0, 1, 1]] where
  M :=![![![-216, 3, 11], ![-382, 4, 20], ![-160, 5, 7]]]
  hmulB := by decide  
  f := ![![![-36, 17, 8]], ![![-263, 124, 59]], ![![-449, 212, 100]]]
  g := ![![![-108, -4, 11], ![-191, -8, 20], ![-80, -1, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P1 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [0, 1]]
 g := ![![[1]], ![[1]]]
 h' := ![![[1, 1], [0, 1]], ![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], []]
 b := ![[], [1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N1 : CertifiedPrimeIdeal' SI2N1 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![746, -815, 999]
  a := ![2, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![373, -907, 999]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N1 B_one_repr
lemma NI2N1 : Nat.card (O ⧸ I2N1) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-36, 17, 8]] ![![-216, 3, 11]]
  ![![2, 0, 0]] where
 M := ![![![2, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 2, 2]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-5, 2, 2]] 
 ![![3, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-5, 2, 2], ![-68, 35, 8], ![-80, 30, 37]]]
  hmulB := by decide  
  f := ![![![-1055, 14, 54]], ![![-977, 13, 50]], ![![-605, 8, 31]]]
  g := ![![![-3, 2, 2], ![-37, 35, 8], ![-49, 30, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![905, -427, -202]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![905, -427, -202]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![905, -427, -202], ![6643, -3135, -1483], ![15955, -7530, -3562]]]
  hmulB := by decide  
  f := ![![![-120, 86, -29]], ![![287, -176, 57]], ![![-1035, 679, -224]]]
  g := ![![![721, -427, -202], ![5293, -3135, -1483], ![12713, -7530, -3562]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-5, 2, 2]] ![![905, -427, -202]]
  ![![40671, -19195, -9080]] where
 M := ![![![40671, -19195, -9080]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![40671, -19195, -9080]] ![![905, -427, -202]]
  ![![3, 0, 0]] where
 M := ![![![-235576530, 111182208, 52593603]]]
 hmul := by decide  
 g := ![![![![-78525510, 37060736, 17531201]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -6, 2]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![9, -6, 2]] 
 ![![5, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![9, -6, 2], ![-76, 49, -16], ![200, -130, 43]]]
  hmulB := by decide  
  f := ![![![-27, 2, 2]], ![![-19, 3, 2]], ![![-16, 6, 3]]]
  g := ![![![3, -6, 2], ![-25, 49, -16], ![66, -130, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16779, -7919, -3746]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![16779, -7919, -3746]] 
 ![![5, 0, 0], ![4, 1, 0], ![0, 0, 1]] where
  M :=![![![16779, -7919, -3746], ![123191, -58141, -27503], ![295895, -139650, -66060]]]
  hmulB := by decide  
  f := ![![![-510, 240, -71]], ![![137, -194, 73]], ![![-1609, 1031, -338]]]
  g := ![![![9691, -7919, -3746], ![71151, -58141, -27503], ![170899, -139650, -66060]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![9, -6, 2]] ![![16779, -7919, -3746]]
  ![![3655, -1725, -816]] where
 M := ![![![3655, -1725, -816]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![3655, -1725, -816]] ![![16779, -7919, -3746]]
  ![![5, 0, 0]] where
 M := ![![![-392627550, 185303680, 87656005]]]
 hmul := by decide  
 g := ![![![![-78525510, 37060736, 17531201]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [3, 2, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 0, 5], [1, 6, 2], [0, 1]]
 g := ![![[1, 0, 4], [1]], ![[2, 6, 0, 5], [5, 4, 2, 6]], ![[6, 2, 5, 4], [1, 2, 0, 1]]]
 h' := ![![[4, 0, 5], [4, 5, 5], [0, 1]], ![[1, 6, 2], [0, 6, 6], [4, 0, 5]], ![[0, 1], [5, 3, 3], [1, 6, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 5], []]
 b := ![[], [2, 2, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [3, 2, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-190372490, 487544043, -944340145]
  a := ![-65, 1, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-27196070, 69649149, -134905735]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-75, -9, 8]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-75, -9, 8]] 
 ![![11, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-75, -9, 8], ![-289, 85, -19], ![275, -220, 76]]]
  hmulB := by decide  
  f := ![![![-2280, 1076, 509]], ![![-1729, 816, 386]], ![![-3655, 1725, 816]]]
  g := ![![![-6, -9, 8], ![-34, 85, -19], ![45, -220, 76]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, -2, -1]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![4, -2, -1]] 
 ![![11, 0, 0], ![3, 1, 0], ![1, 0, 1]] where
  M :=![![![4, -2, -1], ![33, -16, -7], ![75, -35, -18]]]
  hmulB := by decide  
  f := ![![![-43, 1, 2]], ![![-18, 0, 1]], ![![-8, 1, 0]]]
  g := ![![![1, -2, -1], ![8, -16, -7], ![18, -35, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![81, -38, -18]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![81, -38, -18]] 
 ![![11, 0, 0], ![6, 1, 0], ![3, 0, 1]] where
  M :=![![![81, -38, -18], ![592, -279, -132], ![1420, -670, -317]]]
  hmulB := by decide  
  f := ![![![3, 14, -6]], ![![22, -3, 0]], ![![-41, 32, -11]]]
  g := ![![![33, -38, -18], ![242, -279, -132], ![581, -670, -317]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-75, -9, 8]] ![![4, -2, -1]]
  ![![3, 14, -6]] where
 M := ![![![3, 14, -6]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![3, 14, -6]] ![![81, -38, -18]]
  ![![11, 0, 0]] where
 M := ![![![11, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [5, 9, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 9], [8, 3], [0, 1]]
 g := ![![[4, 6, 10], [9, 1], [1]], ![[10, 3, 4], [2, 9], [1]], ![[3, 4, 12], [4, 3], [1]]]
 h' := ![![[6, 9], [6, 4, 6], [8, 4, 1], [0, 1]], ![[8, 3], [12, 8, 5], [3, 1, 3], [6, 9]], ![[0, 1], [6, 1, 2], [0, 8, 9], [8, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11], []]
 b := ![[], [4, 2, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [5, 9, 12, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-127647, 123864, -128310]
  a := ![-2, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9819, 9528, -9870]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [14, 15, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 5, 13], [12, 11, 4], [0, 1]]
 g := ![![[0, 16, 16], [6, 15], [12, 1], []], ![[4, 10, 14, 4], [14, 4], [16, 2], [16, 16]], ![[2, 4], [13, 8], [10, 8], [8, 16]]]
 h' := ![![[0, 5, 13], [5, 12, 4], [2, 10, 10], [0, 0, 1], [0, 1]], ![[12, 11, 4], [10, 6, 13], [6, 0, 2], [14, 12, 11], [0, 5, 13]], ![[0, 1], [5, 16], [0, 7, 5], [15, 5, 5], [12, 11, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 7], []]
 b := ![[], [15, 9, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [14, 15, 5, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16745, -5049, -10863]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![985, -297, -639]
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


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [6, 4, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 16, 3], [2, 2, 16], [0, 1]]
 g := ![![[4, 12, 16], [9, 4, 6], [16, 1], []], ![[18, 6, 7, 12], [7, 17, 10, 15], [4, 4], [12, 9]], ![[13, 13, 18, 6], [2, 5, 2, 1], [16, 9], [18, 9]]]
 h' := ![![[14, 16, 3], [3, 17, 4], [18, 6, 5], [0, 0, 1], [0, 1]], ![[2, 2, 16], [15, 3, 2], [0, 2, 9], [10, 4, 2], [14, 16, 3]], ![[0, 1], [1, 18, 13], [4, 11, 5], [10, 15, 16], [2, 2, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 5], []]
 b := ![[], [8, 0, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [6, 4, 3, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1854362, 908656, 422864]
  a := ![2, 19, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-97598, 47824, 22256]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, 5, 2]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-9, 5, 2]] 
 ![![23, 0, 0], ![0, 23, 0], ![7, 14, 1]] where
  M :=![![![-9, 5, 2], ![-65, 31, 17], ![-185, 90, 36]]]
  hmulB := by decide  
  f := ![![![18, 0, -1]], ![![35, -2, -1]], ![![27, -1, -1]]]
  g := ![![![-1, -1, 2], ![-8, -9, 17], ![-19, -18, 36]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [5, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 22], [0, 1]]
 g := ![![[2, 6], [17, 18], [20, 8], [1]], ![[11, 17], [21, 5], [9, 15], [1]]]
 h' := ![![[13, 22], [7, 11], [15, 15], [18, 13], [0, 1]], ![[0, 1], [12, 12], [3, 8], [3, 10], [13, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [20, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [5, 10, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![923, -707, 467]
  a := ![-2, 3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-102, -315, 467]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18, 0, 1]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-18, 0, 1]] 
 ![![23, 0, 0], ![3, 1, 0], ![5, 0, 1]] where
  M :=![![![-18, 0, 1], ![-35, 2, 1], ![-5, -5, 2]]]
  hmulB := by decide  
  f := ![![![9, -5, -2]], ![![4, -2, -1]], ![![10, -5, -2]]]
  g := ![![![-1, 0, 1], ![-2, 2, 1], ![0, -5, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-9, 5, 2]] ![![-18, 0, 1]]
  ![![23, 0, 0]] where
 M := ![![![-23, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4514, -60, -231]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![4514, -60, -231]] 
 ![![29, 0, 0], ![0, 29, 0], ![19, 27, 1]] where
  M :=![![![4514, -60, -231], ![8025, -106, -411], ![3255, -45, -166]]]
  hmulB := by decide  
  f := ![![![31, -15, -6]], ![![195, -89, -51]], ![![221, -102, -55]]]
  g := ![![![307, 213, -231], ![546, 379, -411], ![221, 153, -166]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [19, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 28], [0, 1]]
 g := ![![[26, 7], [4], [7, 5], [28, 1]], ![[19, 22], [4], [2, 24], [27, 28]]]
 h' := ![![[28, 28], [10, 6], [12, 27], [19, 11], [0, 1]], ![[0, 1], [4, 23], [14, 2], [8, 18], [28, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [12, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [19, 1, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-574, 65, 765]
  a := ![2, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-521, -710, 765]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, -15, -6]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![31, -15, -6]] 
 ![![29, 0, 0], ![5, 1, 0], ![21, 0, 1]] where
  M :=![![![31, -15, -6], ![195, -89, -51], ![555, -270, -104]]]
  hmulB := by decide  
  f := ![![![4514, -60, -231]], ![![1055, -14, -54]], ![![3381, -45, -173]]]
  g := ![![![8, -15, -6], ![59, -89, -51], ![141, -270, -104]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![4514, -60, -231]] ![![31, -15, -6]]
  ![![29, 0, 0]] where
 M := ![![![29, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31829, 15022, 7106]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-31829, 15022, 7106]] 
 ![![31, 0, 0], ![0, 31, 0], ![10, 7, 1]] where
  M :=![![![-31829, 15022, 7106], ![-233688, 110291, 52172], ![-561300, 264910, 125313]]]
  hmulB := by decide  
  f := ![![![373, -46, -2]], ![![24, 333, -140]], ![![178, 31, -23]]]
  g := ![![![-3319, -1120, 7106], ![-24368, -8223, 52172], ![-58530, -19751, 125313]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [5, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 30], [0, 1]]
 g := ![![[8, 25], [9, 1], [23, 10], [22, 1]], ![[0, 6], [0, 30], [26, 21], [13, 30]]]
 h' := ![![[22, 30], [17, 26], [9, 1], [14, 14], [0, 1]], ![[0, 1], [0, 5], [0, 30], [12, 17], [22, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [9, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [5, 9, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-515, -500, 2010]
  a := ![-5, 0, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-665, -470, 2010]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-373, 46, 2]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-373, 46, 2]] 
 ![![31, 0, 0], ![9, 1, 0], ![25, 0, 1]] where
  M :=![![![-373, 46, 2], ![-24, -333, 140], ![-1620, 910, -287]]]
  hmulB := by decide  
  f := ![![![31829, -15022, -7106]], ![![16779, -7919, -3746]], ![![43775, -20660, -9773]]]
  g := ![![![-27, 46, 2], ![-17, -333, 140], ![-85, 910, -287]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-31829, 15022, 7106]] ![![-373, 46, 2]]
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


lemma PB64I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB64I0 : PrimesBelowBoundCertificateInterval O 1 31 64 where
  m := 11
  g := ![2, 3, 3, 1, 3, 1, 1, 1, 2, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB64I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N1, I3N1]
    · exact ![I5N0, I5N1, I5N1]
    · exact ![I7N0]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0]
    · exact ![I17N0]
    · exact ![I19N0]
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
    · exact ![2, 4]
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![343]
    · exact ![11, 11, 11]
    · exact ![2197]
    · exact ![4913]
    · exact ![6859]
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
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N2
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I11N0, I11N1, I11N2, I23N1, I29N1, I31N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N1, I3N1], [I5N0, I5N1, I5N1], [], [I11N0, I11N1, I11N2], [], [], [], [I23N1], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
