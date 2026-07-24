
import IdealArithmetic.Examples.NF3_1_25160_1.RI3_1_25160_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, -1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-1, 1, -1]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-1, 1, -1], ![-12, 14, 1], ![14, -14, 15]]]
  hmulB := by decide  
  f := ![![![-224, 1, -15]], ![![-209, 1, -14]], ![![14, 0, 1]]]
  g := ![![![-1, 1, -1], ![-13, 14, 1], ![14, -14, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, 0, -1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-15, 0, -1]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-15, 0, -1], ![-13, 0, -1], ![1, 1, 0]]]
  hmulB := by decide  
  f := ![![![-1, 1, 0]], ![![0, 0, 1]], ![![6, -7, 0]]]
  g := ![![![-7, 0, -1], ![-6, 0, -1], ![0, 1, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-1, 1, -1]] ![![-15, 0, -1]]
  ![![1, -1, 0]] where
 M := ![![![1, -1, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![1, -1, 0]] ![![-15, 0, -1]]
  ![![2, 0, 0]] where
 M := ![![![-2, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [2, 0, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 0, 2], [1, 2, 1], [0, 1]]
 g := ![![[1]], ![[0, 2, 1, 2]], ![[2, 1, 2, 1]]]
 h' := ![![[1, 0, 2], [0, 1]], ![[1, 2, 1], [1, 0, 2]], ![[0, 1], [1, 2, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 2], []]
 b := ![[], [2, 1, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [2, 0, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2226, -2760, -1302]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![742, -920, -434]
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


def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6615015126, -29763421, 442718442]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![6615015126, -29763421, 442718442]] 
 ![![5, 0, 0], ![0, 1, 0], ![3, 0, 1]] where
  M :=![![![6615015126, -29763421, 442718442], ![5725576325, -25761504, 383191600], ![-829642915, 3732873, -55524925]]]
  hmulB := by decide  
  f := ![![![20400, -24559, -6832]], ![![-22675, 24576, -11190]], ![![-50247, 60308, 15565]]]
  g := ![![![1057371960, -29763421, 442718442], ![915200305, -25761504, 383191600], ![-132613628, 3732873, -55524925]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![196694, -885, 13164]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![196694, -885, 13164]] 
 ![![5, 0, 0], ![2, 1, 0], ![1, 0, 1]] where
  M :=![![![196694, -885, 13164], ![170247, -766, 11394], ![-24669, 111, -1651]]]
  hmulB := by decide  
  f := ![![![-68, 69, -66]], ![![-185, 212, -12]], ![![179, -180, 185]]]
  g := ![![![37060, -885, 13164], ![32077, -766, 11394], ![-4648, 111, -1651]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![6615015126, -29763421, 442718442]] ![![196694, -885, 13164]]
  ![![1285145230812759, -5782347858962, 86010006552048]] where
 M := ![![![1285145230812759, -5782347858962, 86010006552048]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![1285145230812759, -5782347858962, 86010006552048]] ![![196694, -885, 13164]]
  ![![5, 0, 0]] where
 M := ![![![249674147801907643020, -1123377140082049495, 16709765226096715200]]]
 hmul := by decide  
 g := ![![![![49934829560381528604, -224675428016409899, 3341953045219343040]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12, -13, 6]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![12, -13, 6]] 
 ![![7, 0, 0], ![0, 7, 0], ![2, 6, 1]] where
  M :=![![![12, -13, 6], ![65, -78, -20], ![-175, 189, -91]]]
  hmulB := by decide  
  f := ![![![-1554, 7, -104]], ![![-1345, 6, -90]], ![![-1569, 7, -105]]]
  g := ![![![0, -7, 6], ![15, 6, -20], ![1, 105, -91]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [1, 3, 1] where
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

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [1, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-270, 261, -352]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![62, 339, -352]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1554, -7, 104]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![1554, -7, 104]] 
 ![![7, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![1554, -7, 104], ![1345, -6, 90], ![-195, 1, -13]]]
  hmulB := by decide  
  f := ![![![-12, 13, -6]], ![![-11, 13, 2]], ![![25, -27, 13]]]
  g := ![![![223, -7, 104], ![193, -6, 90], ![-28, 1, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![12, -13, 6]] ![![1554, -7, 104]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2366411232, -10647367, 158375132]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![2366411232, -10647367, 158375132]] 
 ![![11, 0, 0], ![0, 11, 0], ![3, 2, 1]] where
  M :=![![![2366411232, -10647367, 158375132], ![2048229349, -9215748, 137080398], ![-296790903, 1335373, -19863115]]]
  hmulB := by decide  
  f := ![![![1506, -2179, -3030]], ![![-41569, 46956, -7388]], ![![-9447, 11190, 1901]]]
  g := ![![![171935076, -29763421, 158375132], ![148817105, -25761504, 137080398], ![-21563778, 3732873, -19863115]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 10], [0, 1]]
 g := ![![[1, 5], [0, 4], [1]], ![[2, 6], [3, 7], [1]]]
 h' := ![![[9, 10], [0, 7], [9, 9], [0, 1]], ![[0, 1], [8, 4], [2, 2], [9, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [6, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [2, 2, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1974, -2504, -57022]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15372, 10140, -57022]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1506, 2179, 3030]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-1506, 2179, 3030]] 
 ![![11, 0, 0], ![6, 1, 0], ![10, 0, 1]] where
  M :=![![![-1506, 2179, 3030], ![41569, -46956, 7388], ![25297, -35715, -44777]]]
  hmulB := by decide  
  f := ![![![-2366411232, 10647367, -158375132]], ![![-1476972431, 6645450, -98848290]], ![![-2124301947, 9558027, -142171655]]]
  g := ![![![-4080, 2179, 3030], ![22675, -46956, 7388], ![62487, -35715, -44777]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![2366411232, -10647367, 158375132]] ![![-1506, 2179, 3030]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2226, 2495, -530]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-2226, 2495, -530]] 
 ![![13, 0, 0], ![0, 13, 0], ![12, 4, 1]] where
  M :=![![![-2226, 2495, -530], ![-4395, 5724, 4460], ![32965, -36895, 8219]]]
  hmulB := by decide  
  f := ![![![16276712, -73235, 1089340]], ![![14088185, -63388, 942870]], ![![19202453, -86399, 1285149]]]
  g := ![![![318, 355, -530], ![-4455, -932, 4460], ![-5051, -5367, 8219]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [6, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 12], [0, 1]]
 g := ![![[], [10], [0, 1]], ![[], [10], [0, 12]]]
 h' := ![![[0, 12], [5], [0, 7], [0, 1]], ![[0, 1], [5], [0, 6], [0, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [0, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [6, 0, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-144, 121, -363]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![324, 121, -363]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16276712, 73235, -1089340]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-16276712, 73235, -1089340]] 
 ![![13, 0, 0], ![4, 1, 0], ![12, 0, 1]] where
  M :=![![![-16276712, 73235, -1089340], ![-14088185, 63388, -942870], ![2041395, -9185, 136623]]]
  hmulB := by decide  
  f := ![![![2226, -2495, 530]], ![![1023, -1208, -180]], ![![-481, 535, -143]]]
  g := ![![![-269044, 73235, -1089340], ![-232869, 63388, -942870], ![33743, -9185, 136623]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-2226, 2495, -530]] ![![-16276712, 73235, -1089340]]
  ![![13, 0, 0]] where
 M := ![![![-13, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1023, -1208, -180]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![1023, -1208, -180]] 
 ![![17, 0, 0], ![4, 1, 0], ![1, 0, 1]] where
  M :=![![![1023, -1208, -180], ![-3548, 3723, -2596], ![-15524, 18300, 2515]]]
  hmulB := by decide  
  f := ![![![-56870145, 255880, -3806108]], ![![-16276712, 73235, -1089340]], ![![-2925741, 13164, -195809]]]
  g := ![![![355, -1208, -180], ![-932, 3723, -2596], ![-5367, 18300, 2515]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![302, -355, -42]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![302, -355, -42]] 
 ![![17, 0, 0], ![8, 1, 0], ![11, 0, 1]] where
  M :=![![![302, -355, -42], ![-901, 932, -752], ![-4573, 5367, 577]]]
  hmulB := by decide  
  f := ![![![-4573748, 20579, -306104]], ![![-2385221, 10732, -159634]], ![![-2925741, 13164, -195809]]]
  g := ![![![212, -355, -42], ![-5, 932, -752], ![-3168, 5367, 577]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![1023, -1208, -180]] ![![1023, -1208, -180]]
  ![![8126833, -9027168, 2499128]] where
 M := ![![![8126833, -9027168, 2499128]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI17N1 : IdealMulLeCertificate' Table 
  ![![8126833, -9027168, 2499128]] ![![302, -355, -42]]
  ![![17, 0, 0]] where
 M := ![![![-840730410, 2114473685, 7889100206]]]
 hmul := by decide  
 g := ![![![![-49454730, 124380805, 464064718]]]]
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
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1304181, 5868, -87284]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-1304181, 5868, -87284]] 
 ![![19, 0, 0], ![0, 19, 0], ![18, 8, 1]] where
  M :=![![![-1304181, 5868, -87284], ![-1128824, 5079, -75548], ![163568, -736, 10947]]]
  hmulB := by decide  
  f := ![![![185, -212, 12]], ![![-56, 5, -412]], ![![6, -32, -173]]]
  g := ![![![14049, 37060, -87284], ![12160, 32077, -75548], ![-1762, -4648, 10947]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [16, 18, 1] where
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
 g := ![![[13, 6], [8, 11], [1], [1]], ![[0, 13], [0, 8], [1], [1]]]
 h' := ![![[1, 18], [5, 14], [12, 7], [3, 1], [0, 1]], ![[0, 1], [0, 5], [0, 12], [4, 18], [1, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [3, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [16, 18, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![48, -80, -86]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![84, 32, -86]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-185, 212, -12]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-185, 212, -12]] 
 ![![19, 0, 0], ![2, 1, 0], ![8, 0, 1]] where
  M :=![![![-185, 212, -12], ![56, -5, 412], ![2768, -3168, 207]]]
  hmulB := by decide  
  f := ![![![1304181, -5868, 87284]], ![![196694, -885, 13164]], ![![540520, -2432, 36175]]]
  g := ![![![-27, 212, -12], ![-170, -5, 412], ![392, -3168, 207]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-1304181, 5868, -87284]] ![![-185, 212, -12]]
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


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [15, 16, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 6, 5], [7, 16, 18], [0, 1]]
 g := ![![[14, 7, 12], [5, 13, 8], [0, 4, 1], []], ![[16, 6, 20, 5], [8, 20], [13, 11, 13, 15], [22, 2]], ![[6, 17, 13, 6], [20, 14, 10, 6], [12, 15, 7, 4], [9, 2]]]
 h' := ![![[20, 6, 5], [17, 1, 14], [0, 9, 13], [0, 0, 1], [0, 1]], ![[7, 16, 18], [5, 19, 22], [9, 2], [1, 19, 16], [20, 6, 5]], ![[0, 1], [16, 3, 10], [3, 12, 10], [6, 4, 6], [7, 16, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 5], []]
 b := ![[], [21, 2, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [15, 16, 19, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![117323, -130686, -65366]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5101, -5682, -2842]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21116, -24003, 2714]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![21116, -24003, 2714]] 
 ![![29, 0, 0], ![0, 29, 0], ![19, 21, 1]] where
  M :=![![![21116, -24003, 2714], ![11279, -19594, -45292], ![-314753, 357331, -43597]]]
  hmulB := by decide  
  f := ![![![587533630, -2643533, 39321448]], ![![508535291, -2288090, 34034382]], ![![750644576, -3377430, 50237859]]]
  g := ![![![-1050, -2793, 2714], ![30063, 32122, -45292], ![17710, 43892, -43597]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [21, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 28], [0, 1]]
 g := ![![[8, 1], [20], [6, 22], [6, 1]], ![[14, 28], [20], [22, 7], [12, 28]]]
 h' := ![![[6, 28], [28, 28], [19, 22], [19, 15], [0, 1]], ![[0, 1], [22, 1], [6, 7], [22, 14], [6, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [18, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [21, 23, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-255, 318, -192]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![117, 150, -192]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-587533630, 2643533, -39321448]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-587533630, 2643533, -39321448]] 
 ![![29, 0, 0], ![15, 1, 0], ![4, 0, 1]] where
  M :=![![![-587533630, 2643533, -39321448], ![-508535291, 2288090, -34034382], ![73687377, -331547, 4931623]]]
  hmulB := by decide  
  f := ![![![-21116, 24003, -2714]], ![![-11311, 13091, 158]], ![![7941, -9011, 1129]]]
  g := ![![![-16203477, 2643533, -39321448], ![-14024797, 2288090, -34034382], ![2032210, -331547, 4931623]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![21116, -24003, 2714]] ![![-587533630, 2643533, -39321448]]
  ![![29, 0, 0]] where
 M := ![![![-29, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![104234, -469, 6976]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![104234, -469, 6976]] 
 ![![31, 0, 0], ![0, 31, 0], ![12, 27, 1]] where
  M :=![![![104234, -469, 6976], ![90219, -406, 6038], ![-13073, 59, -875]]]
  hmulB := by decide  
  f := ![![![-32, 39, 14]], ![![221, -242, 92]], ![![196, -215, 79]]]
  g := ![![![662, -6091, 6976], ![573, -5272, 6038], ![-83, 764, -875]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [27, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 30], [0, 1]]
 g := ![![[11, 19], [5, 20], [8, 14], [13, 1]], ![[10, 12], [17, 11], [4, 17], [26, 30]]]
 h' := ![![[13, 30], [20, 22], [1, 12], [21, 18], [0, 1]], ![[0, 1], [27, 9], [2, 19], [7, 13], [13, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [18, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [27, 18, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![156, -114, -142]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![60, 120, -142]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32, -39, -14]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![32, -39, -14]] 
 ![![31, 0, 0], ![7, 1, 0], ![7, 0, 1]] where
  M :=![![![32, -39, -14], ![-221, 242, -92], ![-493, 599, 203]]]
  hmulB := by decide  
  f := ![![![-104234, 469, -6976]], ![![-26447, 119, -1770]], ![![-23115, 104, -1547]]]
  g := ![![![13, -39, -14], ![-41, 242, -92], ![-197, 599, 203]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![104234, -469, 6976]] ![![32, -39, -14]]
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


lemma PB45I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB45I0 : PrimesBelowBoundCertificateInterval O 1 31 45 where
  m := 11
  g := ![3, 1, 3, 2, 2, 2, 3, 2, 1, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB45I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1]
    · exact ![I3N0]
    · exact ![I5N0, I5N1, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N0, I17N1]
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
    · exact ![27]
    · exact ![5, 5, 5]
    · exact ![49, 7]
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
      exact NI2N1
      exact NI2N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
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
  β := ![I2N0, I2N1, I3N0, I5N0, I5N1, I7N1, I11N1, I13N1, I17N0, I17N1, I19N1, I29N1, I31N1]
  Il := ![[I2N0, I2N1, I2N1], [I3N0], [I5N0, I5N1, I5N1], [I7N1], [I11N1], [I13N1], [I17N0, I17N0, I17N1], [I19N1], [], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
