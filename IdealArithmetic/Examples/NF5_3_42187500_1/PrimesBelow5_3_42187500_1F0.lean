
import IdealArithmetic.Examples.NF5_3_42187500_1.RI5_3_42187500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -2, 0, 1, 2]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-11, -2, 0, 1, 2]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-11, -2, 0, 1, 2], ![-31, -6, 0, 3, 6], ![-31, -5, 0, 3, 6], ![-62, -10, 1, 6, 12], ![-57, -9, 1, 6, 11]]]
  hmulB := by decide  
  f := ![![![-3, 1, 0, 0, 0]], ![![0, -1, 1, 0, 0]], ![![0, 0, -2, 1, 0]], ![![-2, 1, 0, -2, 2]], ![![-9, 2, 1, 1, -1]]]
  g := ![![![-7, -2, 0, 1, 2], ![-20, -6, 0, 3, 6], ![-20, -5, 0, 3, 6], ![-40, -10, 1, 6, 12], ![-37, -9, 1, 6, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20, 39, -2, 10, -29]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![20, 39, -2, 10, -29]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![20, 39, -2, 10, -29], ![425, -18, 22, -72, 11], ![-259, 193, -29, 105, -144], ![898, -100, 49, -173, 66], ![-81, 195, -23, 78, -150]]]
  hmulB := by decide  
  f := ![![![71, 47, -101, -47, 66]], ![![-436, 158, 113, -35, -28]], ![![699, -333, -90, 114, -23]], ![![465, 39, -356, -113, 205]], ![![-462, 257, 18, -102, 46]]]
  g := ![![![5, 39, -2, 10, -29], ![216, -18, 22, -72, 11], ![-154, 193, -29, 105, -144], ![466, -100, 49, -173, 66], ![-63, 195, -23, 78, -150]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 1, -2, -1, 1]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![3, 1, -2, -1, 1]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3, 1, -2, -1, 1], ![-14, 6, 6, -1, -3], ![30, -12, -3, 4, -2], ![28, 2, -14, -5, 6], ![-10, 10, 2, -4, -1]]]
  hmulB := by decide  
  f := ![![![30, -7, 2, -7, 5]], ![![-19, 12, -2, 7, -9]], ![![98, -29, 7, -25, 21]], ![![-96, 39, -8, 28, -29]], ![![90, -24, 6, -22, 17]]]
  g := ![![![1, 1, -2, -1, 1], ![-10, 6, 6, -1, -3], ![21, -12, -3, 4, -2], ![13, 2, -14, -5, 6], ![-10, 10, 2, -4, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-11, -2, 0, 1, 2]] ![![20, 39, -2, 10, -29]]
  ![![-334, -103, -19, 17, 63]] where
 M := ![![![-334, -103, -19, 17, 63]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-334, -103, -19, 17, 63]] ![![20, 39, -2, 10, -29]]
  ![![-35371, -4254, -1663, 4054, 2961]] where
 M := ![![![-35371, -4254, -1663, 4054, 2961]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-35371, -4254, -1663, 4054, 2961]] ![![20, 39, -2, 10, -29]]
  ![![1315998, -1451861, 155924, -692421, 1041851]] where
 M := ![![![1315998, -1451861, 155924, -692421, 1041851]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![1315998, -1451861, 155924, -692421, 1041851]] ![![3, 1, -2, -1, 1]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-854530, -232588, -33338, 54260, 163356]]]
 hmul := by decide  
 g := ![![![![-427265, -116294, -16669, 27130, 81678]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N1, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -2, 1, 2, 4]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-17, -2, 1, 2, 4]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-17, -2, 1, 2, 4], ![-62, -5, 3, 8, 12], ![-63, -9, 4, 7, 16], ![-155, -13, 7, 20, 30], ![-145, -17, 8, 17, 33]]]
  hmulB := by decide  
  f := ![![![4, -1, 2, 1, -2]], ![![11, -1, -2, 0, 0]], ![![-7, 5, 4, -1, -2]], ![![1, -1, 5, 2, -4]], ![![14, -3, -1, 1, -1]]]
  g := ![![![-7, -2, 1, 2, 4], ![-25, -5, 3, 8, 12], ![-26, -9, 4, 7, 16], ![-62, -13, 7, 20, 30], ![-59, -17, 8, 17, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, -3, -1, 1, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![6, -3, -1, 1, 0]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![6, -3, -1, 1, 0], ![-1, 4, -5, -3, 4], ![-28, 4, 13, 2, -6], ![30, -18, -2, 7, -2], ![15, -3, -9, -1, 5]]]
  hmulB := by decide  
  f := ![![![-30, -5, -1, 3, 4]], ![![-41, -10, -1, 3, 8]], ![![-30, -2, -1, 4, 2]], ![![-32, -12, 0, 1, 10]], ![![-43, -5, -1, 5, 5]]]
  g := ![![![4, -3, -1, 1, 0], ![-3, 4, -5, -3, 4], ![-12, 4, 13, 2, -6], ![22, -18, -2, 7, -2], ![7, -3, -9, -1, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-17, -2, 1, 2, 4]] ![![-17, -2, 1, 2, 4]]
  ![![-540, -59, 27, 65, 116]] where
 M := ![![![-540, -59, 27, 65, 116]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-540, -59, 27, 65, 116]] ![![-17, -2, 1, 2, 4]]
  ![![-15758, -1685, 774, 1909, 3342]] where
 M := ![![![-15758, -1685, 774, 1909, 3342]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-15758, -1685, 774, 1909, 3342]] ![![-17, -2, 1, 2, 4]]
  ![![-456891, -48656, 22382, 55416, 96688]] where
 M := ![![![-456891, -48656, 22382, 55416, 96688]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N3 : IdealMulLeCertificate' Table 
  ![![-456891, -48656, 22382, 55416, 96688]] ![![6, -3, -1, 1, 0]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-206586, -21975, 10113, 25065, 43692]]]
 hmul := by decide  
 g := ![![![![-68862, -7325, 3371, 8355, 14564]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0, I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14, 3, 0, -1, -2]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![14, 3, 0, -1, -2]] 
 ![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![14, 3, 0, -1, -2], ![31, 10, 2, -3, -6], ![31, 5, 2, -1, -6], ![61, 11, -1, -4, -8], ![42, 12, 1, -4, -7]]]
  hmulB := by decide  
  f := ![![![-3, 4, -1, 2, -4]], ![![11, -1, 0, -2, 0]], ![![-13, 9, -2, 5, -8]], ![![29, -5, 1, -6, 2]], ![![-3, 7, -2, 3, -7]]]
  g := ![![![3, 3, 0, -1, -2], ![5, 10, 2, -3, -6], ![6, 5, 2, -1, -6], ![14, 11, -1, -4, -8], ![8, 12, 1, -4, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![14, 3, 0, -1, -2]] ![![14, 3, 0, -1, -2]]
  ![![144, 37, 5, -11, -24]] where
 M := ![![![144, 37, 5, -11, -24]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![144, 37, 5, -11, -24]] ![![14, 3, 0, -1, -2]]
  ![![1639, 418, 71, -120, -284]] where
 M := ![![![1639, 418, 71, -120, -284]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![1639, 418, 71, -120, -284]] ![![14, 3, 0, -1, -2]]
  ![![18857, 4724, 814, -1348, -3264]] where
 M := ![![![18857, 4724, 814, -1348, -3264]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![18857, 4724, 814, -1348, -3264]] ![![14, 3, 0, -1, -2]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![216360, 53885, 9160, -15395, -37310]]]
 hmul := by decide  
 g := ![![![![43272, 10777, 1832, -3079, -7462]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2 ⊙ MulI5N3)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [4, 4, 0, 4, 3, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 6, 1, 4, 4], [2, 5, 2, 2, 5], [1, 0, 3, 6, 6], [0, 2, 1, 2, 6], [0, 1]]
 g := ![![[5, 4, 1], []], ![[5, 6, 4, 5, 2, 5, 0, 4], [0, 0, 0, 5, 6, 5, 0, 1]], ![[6, 5, 1, 3, 6, 3], [3, 4, 5, 4, 3, 0, 6, 6]], ![[0, 3, 4, 6, 5, 3, 6, 6], [2, 3, 1, 2, 1, 3, 0, 6]], ![[0, 0, 5, 2, 4, 3], [4, 0, 1, 1, 6, 3, 2, 6]]]
 h' := ![![[1, 6, 1, 4, 4], [0, 0, 0, 1], [0, 1]], ![[2, 5, 2, 2, 5], [1, 4, 6, 6, 6], [1, 6, 1, 4, 4]], ![[1, 0, 3, 6, 6], [3, 4, 5, 4], [2, 5, 2, 2, 5]], ![[0, 2, 1, 2, 6], [0, 1, 0, 5, 1], [1, 0, 3, 6, 6]], ![[0, 1], [5, 5, 3, 5], [0, 2, 1, 2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 2, 1, 1], [], [], []]
 b := ![[], [3, 0, 6, 1, 5], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [4, 4, 0, 4, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11645929196174, 2517029778956, -1039639154120, -884010667988, -3945391526748]
  a := ![15, -20, -8, 12, -60]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1663704170882, 359575682708, -148519879160, -126287238284, -563627360964]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 16807 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12, 1, -10, -3, 6]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![12, 1, -10, -3, 6]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![8, 6, 1, 1, 0], ![6, 5, 8, 0, 1]] where
  M :=![![![12, 1, -10, -3, 6], ![-87, 28, 24, -5, -6], ![91, -55, -2, 23, -10], ![109, -13, -65, -12, 36], ![-80, 38, 3, -14, 9]]]
  hmulB := by decide  
  f := ![![![65, 18, 3, -4, -12]], ![![184, 43, 9, -14, -28]], ![![125, 43, 6, -5, -28]], ![![184, 46, 9, -13, -30]], ![![227, 66, 11, -13, -43]]]
  g := ![![![0, -1, -5, -3, 6], ![-1, 8, 7, -5, -6], ![-3, -13, 5, 23, -10], ![-1, -11, -31, -12, 36], ![-2, 7, -5, -14, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [5, 8, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 6, 8], [7, 4, 3], [0, 1]]
 g := ![![[5, 5, 3], [8, 4, 1], []], ![[5, 7, 5, 8], [6, 1, 0, 7], [0, 9]], ![[0, 2, 6, 4], [10, 6, 5, 9], [5, 9]]]
 h' := ![![[8, 6, 8], [4, 4, 6], [0, 0, 1], [0, 1]], ![[7, 4, 3], [2, 0, 1], [9, 7, 4], [8, 6, 8]], ![[0, 1], [0, 7, 4], [2, 4, 6], [7, 4, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 4], []]
 b := ![[], [2, 2, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [5, 8, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![33740582100, 5553595523, -3353036480, -4117531617, -9407744452]
  a := ![120, -180, -58, 54, -477]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![11193391068, 7027046135, 6911495523, -4117531617, -9407744452]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![65, 18, 3, -4, -12]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![65, 18, 3, -4, -12]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![3, 5, 1, 0, 0], ![3, 9, 0, 1, 0], ![9, 5, 0, 0, 1]] where
  M :=![![![65, 18, 3, -4, -12], ![184, 43, 9, -14, -28], ![125, 43, 6, -5, -28], ![275, 61, 15, -22, -38], ![187, 59, 10, -9, -37]]]
  hmulB := by decide  
  f := ![![![12, 1, -10, -3, 6]], ![![-87, 28, 24, -5, -6]], ![![-28, 8, 8, -1, -2]], ![![-58, 22, 11, -6, 0]], ![![-37, 17, 3, -6, 3]]]
  g := ![![![16, 9, 3, -4, -12], ![41, 24, 9, -14, -28], ![34, 18, 6, -5, -28], ![58, 34, 15, -22, -38], ![47, 25, 10, -9, -37]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [7, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 10], [0, 1]]
 g := ![![[8, 5], [2, 1], [1]], ![[3, 6], [1, 10], [1]]]
 h' := ![![[10, 10], [8, 7], [4, 10], [0, 1]], ![[0, 1], [1, 4], [5, 1], [10, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [9, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [7, 1, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-53594, -3429, 9521, 3963, 15354]
  a := ![11, -15, -5, 6, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-21112, -14861, 9521, 3963, 15354]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![12, 1, -10, -3, 6]] ![![65, 18, 3, -4, -12]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![68, -25, 5, -19, 18]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![68, -25, 5, -19, 18]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![8, 2, 0, 1, 0], ![5, 0, 1, 0, 1]] where
  M :=![![![68, -25, 5, -19, 18], ![-251, 78, -19, 65, -58], ![528, -180, 39, -142, 130], ![-640, 208, -50, 169, -154], ![455, -155, 33, -123, 111]]]
  hmulB := by decide  
  f := ![![![-4, -1, 3, 1, -2]], ![![29, -10, -9, 1, 2]], ![![-30, 18, 1, -8, 2]], ![![0, -2, 2, 1, -2]], ![![-1, 0, 1, 0, -1]]]
  g := ![![![10, 1, -1, -19, 18], ![-37, -4, 3, 65, -58], ![78, 8, -7, -142, 130], ![-94, -10, 8, 169, -154], ![68, 7, -6, -123, 111]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [10, 1, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 3, 3], [5, 9, 10], [0, 1]]
 g := ![![[9, 1, 9], [9, 10], [1]], ![[6, 5, 7, 4], [12, 1], [1, 5, 9, 1]], ![[8, 1, 11, 12], [6, 12], [12, 10, 3, 12]]]
 h' := ![![[1, 3, 3], [10, 2, 3], [3, 12, 6], [0, 1]], ![[5, 9, 10], [0, 6, 7], [4, 10, 12], [1, 3, 3]], ![[0, 1], [4, 5, 3], [5, 4, 8], [5, 9, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 4], []]
 b := ![[], [8, 11, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [10, 1, 7, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2184444837, -487368024, 245353500, 251437576, 722146037]
  a := ![-52, 75, 27, -35, 209]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-600513510, -76172552, -36676349, 251437576, 722146037]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 22, -1, 6, -16]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![9, 22, -1, 6, -16]] 
 ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![9, 22, -1, 6, -16], ![234, -11, 13, -40, 8], ![-157, 109, -16, 61, -80], ![491, -59, 29, -96, 42], ![-67, 109, -12, 47, -81]]]
  hmulB := by decide  
  f := ![![![20, -61, 58, 41, -46]], ![![53, -20, -12, 5, 2]], ![![-77, -9, 64, 21, -38]], ![![-9, -55, 71, 42, -52]], ![![78, -59, 17, 29, -23]]]
  g := ![![![3, 22, -1, 6, -16], ![30, -11, 13, -40, 8], ![-11, 109, -16, 61, -80], ![61, -59, 29, -96, 42], ![2, 109, -12, 47, -81]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, 6, 10, 0, -4]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![-25, 6, 10, 0, -4]] 
 ![![13, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-25, 6, 10, 0, -4], ![60, -31, -6, 12, -4], ![-6, 30, -29, -22, 24], ![-172, 52, 54, -5, -20], ![12, -24, 20, 14, -15]]]
  hmulB := by decide  
  f := ![![![-1401, -166, 58, 164, 292]], ![![-1535, -181, 64, 180, 320]], ![![-1686, -198, 71, 198, 352]], ![![-1377, -158, 60, 163, 288]], ![![-1264, -144, 56, 150, 265]]]
  g := ![![![-15, 6, 10, 0, -4], ![33, -31, -6, 12, -4], ![2, 30, -29, -22, 24], ![-99, 52, 54, -5, -20], ![2, -24, 20, 14, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![68, -25, 5, -19, 18]] ![![9, 22, -1, 6, -16]]
  ![![-16558, 5399, -1240, 4383, -3944]] where
 M := ![![![-16558, 5399, -1240, 4383, -3944]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-16558, 5399, -1240, 4383, -3944]] ![![-25, 6, 10, 0, -4]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![-55874, 18655, -4212, 14937, -13624]]]
 hmul := by decide  
 g := ![![![![-4298, 1435, -324, 1149, -1048]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3286, -349, 161, 399, 694]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-3286, -349, 161, 399, 694]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![13, 3, 3, 3, 1]] where
  M :=![![![-3286, -349, 161, 399, 694], ![-10809, -1154, 529, 1311, 2290], ![-12426, -1314, 607, 1508, 2622], ![-26632, -2840, 1308, 3229, 5638], ![-26727, -2841, 1307, 3245, 5649]]]
  hmulB := by decide  
  f := ![![![-102, -25, -5, 7, 18]], ![![-277, -66, -9, 19, 46]], ![![-216, -60, -11, 18, 38]], ![![-402, -102, -22, 27, 74]], ![![-256, -64, -12, 18, 45]]]
  g := ![![![-724, -143, -113, -99, 694], ![-2387, -472, -373, -327, 2290], ![-2736, -540, -427, -374, 2622], ![-5878, -1162, -918, -805, 5638], ![-5892, -1164, -920, -806, 5649]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [8, 9, 16, 10, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 16, 7, 6], [1, 7, 14, 4], [15, 10, 13, 7], [0, 1]]
 g := ![![[16, 5, 14, 4], [9, 0, 15], [1], []], ![[1, 5, 4, 14, 3, 5], [5, 13, 15], [9, 6, 1], [11, 13, 2]], ![[5, 14, 3, 16, 3, 9], [14, 12, 15], [8, 3, 8], [0, 3, 16]], ![[1, 0, 14, 11, 0, 5], [2, 16, 15], [3, 1, 16], [4, 15, 15]]]
 h' := ![![[8, 16, 7, 6], [9, 12, 5, 2], [9, 8, 1, 7], [0, 0, 1], [0, 1]], ![[1, 7, 14, 4], [13, 1, 16, 10], [11, 13, 9, 10], [10, 2, 8, 1], [8, 16, 7, 6]], ![[15, 10, 13, 7], [15, 12, 3, 10], [5, 3, 14, 7], [1, 7, 7, 12], [1, 7, 14, 4]], ![[0, 1], [9, 9, 10, 12], [12, 10, 10, 10], [6, 8, 1, 4], [15, 10, 13, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [4, 3, 15], []]
 b := ![[], [], [3, 7, 11, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [8, 9, 16, 10, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3550847679, -4349170615, 1059734481, -1080747861, 5446192496]
  a := ![14, -17, -7, 18, -57]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4373608831, -1216926359, -898755471, -1024666197, 5446192496]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![102, 25, 5, -7, -18]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![102, 25, 5, -7, -18]] 
 ![![17, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![102, 25, 5, -7, -18], ![277, 66, 9, -19, -46], ![216, 60, 11, -18, -38], ![402, 102, 22, -27, -74], ![341, 79, 13, -23, -57]]]
  hmulB := by decide  
  f := ![![![3286, 349, -161, -399, -694]], ![![1409, 150, -69, -171, -298]], ![![2084, 221, -102, -253, -440]], ![![4466, 475, -219, -542, -944]], ![![4085, 434, -200, -496, -863]]]
  g := ![![![18, 25, 5, -7, -18], ![49, 66, 9, -19, -46], ![39, 60, 11, -18, -38], ![71, 102, 22, -27, -74], ![60, 79, 13, -23, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-3286, -349, 161, 399, 694]] ![![102, 25, 5, -7, -18]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![-17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [18, 13, 3, 6, 15, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 15, 5, 15, 17], [4, 3, 8, 16, 4], [11, 8, 15, 1, 3], [8, 11, 10, 6, 14], [0, 1]]
 g := ![![[0, 9, 15, 14, 17], [5, 13, 10, 4, 1], [], []], ![[4, 9, 18, 4, 17, 15, 14, 1], [13, 1, 16, 7, 0, 9, 10, 7], [5, 14, 5, 9], [1, 5, 13, 4]], ![[0, 8, 13, 17, 18, 17, 11, 5], [5, 11, 16, 3, 7, 18, 9, 11], [4, 3, 1, 6], [8, 4, 2, 16]], ![[2, 6, 7, 13, 9, 18, 17, 15], [14, 1, 9, 17, 9, 15, 6, 14], [11, 1, 16, 1], [11, 15, 4, 9]], ![[6, 1, 0, 9, 2, 16, 9, 10], [18, 4, 9, 15, 5, 10, 4, 8], [5, 16, 18, 1], [11, 3, 2, 6]]]
 h' := ![![[0, 15, 5, 15, 17], [5, 5, 16, 14, 13], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[4, 3, 8, 16, 4], [13, 11, 16, 7, 16], [6, 9, 3, 6, 14], [1, 11, 18, 2, 16], [0, 15, 5, 15, 17]], ![[11, 8, 15, 1, 3], [6, 12, 14, 14, 5], [10, 8, 16, 13, 6], [5, 0, 18, 11, 5], [4, 3, 8, 16, 4]], ![[8, 11, 10, 6, 14], [2, 3, 10, 3, 10], [12, 9, 15, 1, 12], [18, 10, 18, 13, 18], [11, 8, 15, 1, 3]], ![[0, 1], [2, 7, 1, 0, 13], [6, 12, 4, 18, 5], [18, 17, 2, 12, 18], [8, 11, 10, 6, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 6, 10, 13], [], [], []]
 b := ![[], [0, 13, 16, 4, 16], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [18, 13, 3, 6, 15, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3148174762336, 315476711360, -167252603210, -387207644870, -668316157400]
  a := ![6, -12, -2, -14, -24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![165693408544, 16604037440, -8802768590, -20379349730, -35174534600]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 2476099 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![116, -33, 7, -29, 22]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![116, -33, 7, -29, 22]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![6, 20, 7, 1, 0], ![9, 5, 20, 0, 1]] where
  M :=![![![116, -33, 7, -29, 22], ![-301, 120, -29, 87, -94], ![812, -248, 55, -210, 174], ![-794, 314, -74, 229, -246], ![771, -207, 43, -189, 135]]]
  hmulB := by decide  
  f := ![![![-16, -7, -5, 1, 6]], ![![-91, -4, 3, 1, 10]], ![![-30, -30, 3, 12, 2]], ![![-94, -16, 1, 5, 12]], ![![-56, -30, 1, 11, 7]]]
  g := ![![![4, 19, -10, -29, 22], ![1, -50, 54, 87, -94], ![22, 134, -85, -210, 174], ![2, -132, 141, 229, -246], ![30, 126, -58, -189, 135]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [5, 21, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 9, 5], [3, 13, 18], [0, 1]]
 g := ![![[17, 4, 13], [3], [10, 10, 1], []], ![[13, 6, 20, 14], [10, 7, 2, 7], [18, 17, 15, 17], [18, 2]], ![[21, 15, 3, 1], [19, 6, 3, 16], [16, 16, 11, 9], [5, 2]]]
 h' := ![![[7, 9, 5], [8, 22, 17], [19, 16], [0, 0, 1], [0, 1]], ![[3, 13, 18], [17, 22, 9], [16, 6, 11], [5, 14, 13], [7, 9, 5]], ![[0, 1], [9, 2, 20], [21, 1, 12], [7, 9, 9], [3, 13, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 5], []]
 b := ![[], [13, 6, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [5, 21, 13, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2631779, -217464, 229450, 344713, 649095]
  a := ![0, 10, 7, 1, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-458344, -450313, -659367, 344713, 649095]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16, 7, 5, -1, -6]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![16, 7, 5, -1, -6]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![3, 5, 1, 0, 0], ![21, 16, 0, 1, 0], ![4, 8, 0, 0, 1]] where
  M :=![![![16, 7, 5, -1, -6], ![91, 4, -3, -1, -10], ![30, 30, -3, -12, -2], ![36, 36, 28, -5, -26], ![89, 7, 7, 1, -17]]]
  hmulB := by decide  
  f := ![![![-116, 33, -7, 29, -22]], ![![301, -120, 29, -87, 94]], ![![15, -11, 3, -6, 10]], ![![138, -67, 17, -44, 56]], ![![51, -27, 7, -17, 23]]]
  g := ![![![2, 2, 5, -1, -6], ![7, 5, -3, -1, -10], ![13, 11, -3, -12, -2], ![7, 8, 28, -5, -26], ![5, 4, 7, 1, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [7, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 22], [0, 1]]
 g := ![![[3, 6], [2, 16], [3, 4], [1]], ![[15, 17], [11, 7], [11, 19], [1]]]
 h' := ![![[2, 22], [9, 11], [2, 4], [16, 2], [0, 1]], ![[0, 1], [8, 12], [10, 19], [20, 21], [2, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [21, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [7, 21, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5480, -57, 478, 653, 1174]
  a := ![2, -5, -1, -3, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1101, -969, 478, 653, 1174]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![116, -33, 7, -29, 22]] ![![16, 7, 5, -1, -6]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![-23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB318I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB318I0 : PrimesBelowBoundCertificateInterval O 1 23 318 where
  m := 9
  g := ![5, 5, 5, 1, 2, 3, 2, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB318I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N1, I2N2]
    · exact ![I3N0, I3N0, I3N0, I3N0, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
    · exact ![I23N0, I23N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![16807]
    · exact ![1331, 121]
    · exact ![2197, 13, 13]
    · exact ![83521, 17]
    · exact ![2476099]
    · exact ![12167, 529]
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
      exact NI2N1
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N0
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
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
      exact NI13N2
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I11N1, I13N1, I13N2, I17N1]
  Il := ![[I2N0, I2N1, I2N1, I2N1, I2N2], [I3N0, I3N0, I3N0, I3N0, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [I11N1], [I13N1, I13N2], [I17N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
