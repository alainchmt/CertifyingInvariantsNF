
import IdealArithmetic.Examples.NF3_1_656731_1.RI3_1_656731_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![16, 1, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![16, 1, 1]] 
 ![![2, 0, 0], ![0, 2, 0], ![0, 1, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![16, 1, 1], ![88, -8, 10], ![94, -17, -7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![-16, 0, -1], ![2, 0, 0]], ![![-8, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -1, 2]], ![![8, 0, 1], ![44, -9, 10], ![47, -5, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
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

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4074, 4341, -8609]
  a := ![2, -2, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2037, 6475, -8609]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![1, 0, 9], ![87, -24, 1]]]
  hmulB := by decide  
  f := ![![![0, 0, -9], ![0, 2, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -4], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![-1, 0, 2]], ![![0, 1, 0], ![-4, 0, 9], ![43, -24, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![16, 1, 1]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![32, 2, 2], ![88, -8, 10]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![0, 1, 0]]], ![![![16, 1, 1]], ![![44, -4, 5]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![1, 1, 0]] 
 ![![3, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![1, 1, 0], ![1, 1, 9], ![87, -24, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-55, 19, -1], ![-9, 0, 2]]]
  g := ![![![1, 0, 0], ![-1, 3, 0], ![0, 0, 3]], ![![0, 1, 0], ![0, 1, 9], ![37, -24, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-1, 1, 0]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 3]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-1, 1, 0], ![1, -1, 9], ![87, -24, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![0, 0, 1]], ![![-1, 1, 0], ![1, -1, 3], ![45, -24, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P1 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 2, 1] where
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

def PI3N1 : CertifiedPrimeIdeal' SI3N1 3 where
  n := 2
  hpos := by decide
  P := [2, 2, 1]
  hirr := P3P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1813531, 1924967, -6448929]
  a := ![-65, 1, -521]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-678801, 1924967, -2149643]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N1 B_one_repr
lemma NI3N1 : Nat.card (O ⧸ I3N1) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![3, 3, 0], ![0, 0, 9]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![-1, 1, 0]]], ![![![1, 1, 0]], ![![0, 0, 3]]]]
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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [2, 0, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 1, 1], [0, 3, 4], [0, 1]]
 g := ![![[4, 2, 1], []], ![[1, 3, 4, 4], [4, 1]], ![[0, 3, 0, 4], [1, 1]]]
 h' := ![![[2, 1, 1], [0, 0, 1], [0, 1]], ![[0, 3, 4], [1, 2, 3], [2, 1, 1]], ![[0, 1], [3, 3, 1], [0, 3, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 3], []]
 b := ![[], [4, 2, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [2, 0, 3, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5279010, 2921890, -3966230]
  a := ![-2, 1, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1055802, 584378, -793246]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![884784249721187627, 9824977839293905, 35435083171523608]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![884784249721187627, 9824977839293905, 35435083171523608]] 
 ![![7, 0, 0], ![3, 1, 0], ![3, 0, 1]] where
  M :=![![![884784249721187627, 9824977839293905, 35435083171523608], ![3092677213761847801, 34342253604621035, 123859883725168753], ![1102818654219234991, 12246114057611536, 44167231443914940]]]
  hmulB := by decide  
  f := ![![![-244771708, 36701188, 93456185]], ![![1061867737, -339659512, 100590776]], ![![444697361, -16647379, -310092915]]]
  g := ![![![107000580955533584, 9824977839293905, 35435083171523608], ![374010114538925491, 34342253604621035, 123859883725168753], ![133368373959236509, 12246114057611536, 44167231443914940]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8640843, 2010725, 1293738]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-8640843, 2010725, 1293738]] 
 ![![7, 0, 0], ![4, 1, 0], ![3, 0, 1]] where
  M :=![![![-8640843, 2010725, 1293738], ![114565931, -39690555, 19390263], ![183989241, -39201234, -37679830]]]
  hmulB := by decide  
  f := ![![![2255655602190192, 25047650104058, 90337665815265]], ![![2415292426398983, 26820317577152, 96731025716121]], ![![1368353718047211, 15194715503091, 54801752881955]]]
  g := ![![![-2937851, 2010725, 1293738], ![30736766, -39690555, 19390263], ![64833381, -39201234, -37679830]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, -2]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![-1, 1, -2]] 
 ![![7, 0, 0], ![6, 1, 0], ![0, 0, 1]] where
  M :=![![![-1, 1, -2], ![-173, 47, 7], ![73, -38, 48]]]
  hmulB := by decide  
  f := ![![![2522, 28, 101]], ![![3421, 38, 137]], ![![449, 5, 18]]]
  g := ![![![-1, 1, -2], ![-65, 47, 7], ![43, -38, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![884784249721187627, 9824977839293905, 35435083171523608]] ![![-8640843, 2010725, 1293738]]
  ![![2522, 28, 101]] where
 M := ![![![2522, 28, 101]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![2522, 28, 101]] ![![-1, 1, -2]]
  ![![7, 0, 0]] where
 M := ![![![7, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![18, 2, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![18, 2, 1]] 
 ![![11, 0, 0], ![0, 11, 0], ![7, 2, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![18, 2, 1], ![89, -6, 19], ![181, -41, -4]]]
  hmulB := by decide  
  f := ![![![-17, -2, -1], ![11, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -2, 11]], ![![1, 0, 1], ![-4, -4, 19], ![19, -3, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [7, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 10], [0, 1]]
 g := ![![[4, 3], [0, 3], [1]], ![[8, 8], [4, 8], [1]]]
 h' := ![![[5, 10], [0, 6], [4, 5], [0, 1]], ![[0, 1], [8, 5], [7, 6], [5, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [2, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [7, 6, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2136, 131, -1953]
  a := ![-1, -1, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1437, 367, -1953]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![3, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![3, 1, 0]] 
 ![![11, 0, 0], ![3, 1, 0], ![4, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![3, 1, 0], ![1, 3, 9], ![87, -24, 4]]]
  hmulB := by decide  
  f := ![![![-3, -12, -36], ![0, 44, 0]], ![![-1, -3, -9], ![1, 11, 0]], ![![-3, -5, -13], ![7, 16, 0]]]
  g := ![![![1, 0, 0], ![-3, 11, 0], ![-4, 0, 11]], ![![0, 1, 0], ![-4, 3, 9], ![13, -24, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![18, 2, 1]] ![![11, 0, 0], ![3, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![33, 11, 0]], ![![198, 22, 11], ![143, 0, 22]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![3, 1, 0]]], ![![![18, 2, 1]], ![![13, 0, 2]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [10, 3, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 3, 9], [6, 9, 4], [0, 1]]
 g := ![![[3, 1, 1], [9, 4], [1]], ![[2, 5, 8, 10], [12, 3], [1, 2, 3, 1]], ![[7, 1, 7, 4], [6, 10], [12, 4, 1, 12]]]
 h' := ![![[9, 3, 9], [10, 6, 1], [3, 10, 2], [0, 1]], ![[6, 9, 4], [0, 5, 11], [4, 4, 4], [9, 3, 9]], ![[0, 1], [4, 2, 1], [5, 12, 7], [6, 9, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 12], []]
 b := ![[], [11, 8, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [10, 3, 11, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-24587160, 7410143, -406211]
  a := ![2, 19, 17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1891320, 570011, -31247]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5054084765, -1199078046, -692238242]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![5054084765, -1199078046, -692238242]] 
 ![![17, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![5054084765, -1199078046, -692238242], ![-61423805100, 21667802573, -11483940656], ![-109165457696, 23932205410, 20468724527]]]
  hmulB := by decide  
  f := ![![![-718348308667800956931, -7976810409746145022, -28769422683313034842]], ![![-147700975521057657428, -1640127309899301219, -5915336257119314120]], ![![-137180298927453398510, -1523301751104473730, -5493989414391784437]]]
  g := ![![![378738897, -1199078046, -692238242], ![-2262113164, 21667802573, -11483940656], ![-8829582750, 23932205410, 20468724527]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4133145, 45896, 165530]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![4133145, 45896, 165530]] 
 ![![17, 0, 0], ![2, 1, 0], ![11, 0, 1]] where
  M :=![![![4133145, 45896, 165530], ![14447006, 160425, 578594], ![5151662, 57206, 206321]]]
  hmulB := by decide  
  f := ![![![-1939, 564, -26]], ![![-328, -11, 294]], ![![1621, -442, -61]]]
  g := ![![![130619, 45896, 165530], ![456566, 160425, 578594], ![162807, 57206, 206321]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-159636824208791, -1772667473094, -6393359900856]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![-159636824208791, -1772667473094, -6393359900856]] 
 ![![17, 0, 0], ![14, 1, 0], ![1, 0, 1]] where
  M :=![![![-159636824208791, -1772667473094, -6393359900856], ![-557994978847566, -6196186588247, -22347367158702], ![-198975589465170, -2209499951736, -7968854061341]]]
  hmulB := by decide  
  f := ![![![4747445, -2026962, 1875444]], ![![13388288, -4037687, 581706]], ![![-9321773, 3514602, -2377337]]]
  g := ![![![-7554477628507, -1772667473094, -6393359900856], ![-26405941144318, -6196186588247, -22347367158702], ![-9416102122325, -2209499951736, -7968854061341]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![5054084765, -1199078046, -692238242]] ![![4133145, 45896, 165530]]
  ![![4747445, -2026962, 1875444]] where
 M := ![![![4747445, -2026962, 1875444]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![4747445, -2026962, 1875444]] ![![-159636824208791, -1772667473094, -6393359900856]]
  ![![17, 0, 0]] where
 M := ![![![17, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![3, 1, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![3, 1, 0]] 
 ![![19, 0, 0], ![3, 1, 0], ![16, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![3, 1, 0], ![1, 3, 9], ![87, -24, 4]]]
  hmulB := by decide  
  f := ![![![-25, -78, -234], ![0, 494, 0]], ![![-4, -12, -36], ![1, 76, 0]], ![![-22, -66, -197], ![6, 416, 0]]]
  g := ![![![1, 0, 0], ![-3, 19, 0], ![-16, 0, 19]], ![![0, 1, 0], ![-8, 3, 9], ![5, -24, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![42349591403695177083744158, 470265827150034265900392, 1696075957661844437323223]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![42349591403695177083744158, 470265827150034265900392, 1696075957661844437323223]] 
 ![![19, 0, 0], ![7, 1, 0], ![1, 0, 1]] where
  M :=![![![42349591403695177083744158, 470265827150034265900392, 1696075957661844437323223], ![148028874143730500313020793, 1643768419810910587986806, 5928468402012152830426751], ![52785658665685892194596665, 586151852032088679653153, 2114034246960944853887198]]]
  hmulB := by decide  
  f := ![![![5946583613685, -1857279909497, 437536790654]], ![![4096552956484, -923960985710, -695538150539]], ![![-8030211104104, 2409483971211, -314423288466]]]
  g := ![![![1966402876630689093953589, 470265827150034265900392, 1696075957661844437323223], ![6873369831739051229825600, 1643768419810910587986806, 5928468402012152830426751], ![2450976918657911925428284, 586151852032088679653153, 2114034246960944853887198]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![8, 1, 0]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![19, 0, 0], ![8, 1, 0]] 
 ![![19, 0, 0], ![8, 1, 0], ![12, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![8, 1, 0], ![1, 8, 9], ![87, -24, 9]]]
  hmulB := by decide  
  f := ![![![-43, -478, -540], ![-38, 1140, 0]], ![![-25, -200, -225], ![1, 475, 0]], ![![-28, -302, -341], ![-22, 720, 0]]]
  g := ![![![1, 0, 0], ![-8, 19, 0], ![-12, 0, 19]], ![![0, 1, 0], ![-9, 8, 9], ![9, -24, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![3, 1, 0]] ![![42349591403695177083744158, 470265827150034265900392, 1696075957661844437323223]]
  ![![19, 0, 0], ![13, -1, 1]] where
 M := ![![![804642236670208364591139002, 8935050715850651052107448, 32225443195575044309141237]], ![![275077648354816031564253267, 3054565901261013385687982, 11016696274997686142396420]]]
 hmul := by decide  
 g := ![![![![28866477721512585994681634, 1507428418087156657366740, 658913366724722045856875], ![19706089227805325437860612, 0, 0]]], ![![![9868389261766881946179919, 515334449788009913363476, 225258296330869009167282], ![6736788644711174968218062, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![13, -1, 1]] ![![19, 0, 0], ![8, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![152, 19, 0]], ![![247, -19, 19], ![190, -19, 0]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![8, 1, 0]]], ![![![13, -1, 1]], ![![10, -1, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![0, 1, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![0, 1, 0]] 
 ![![23, 0, 0], ![0, 1, 0], ![18, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![0, 1, 0], ![1, 0, 9], ![87, -24, 1]]]
  hmulB := by decide  
  f := ![![![0, 0, -9], ![0, 23, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -7], ![0, 18, 0]]]
  g := ![![![1, 0, 0], ![0, 23, 0], ![-18, 0, 23]], ![![0, 1, 0], ![-7, 0, 9], ![3, -24, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![24, 5, 1]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![24, 5, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![1, 5, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![24, 5, 1], ![92, 0, 46], ![442, -113, 5]]]
  hmulB := by decide  
  f := ![![![-23, -5, -1], ![23, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -5, 23]], ![![1, 0, 1], ![2, -10, 46], ![19, -6, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [17, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 22], [0, 1]]
 g := ![![[12, 1], [18, 9], [17, 9], [1]], ![[15, 22], [22, 14], [21, 14], [1]]]
 h' := ![![[3, 22], [16, 1], [10, 3], [6, 3], [0, 1]], ![[0, 1], [19, 22], [19, 20], [15, 20], [3, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [21, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [17, 20, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6861, 4519, -7229]
  a := ![-2, 3, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16, 1768, -7229]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![0, 1, 0]] ![![23, 0, 0], ![24, 5, 1]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![552, 115, 23]], ![![0, 23, 0], ![92, 0, 46]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![24, 5, 1]]], ![![![0, 1, 0]], ![![4, 0, 2]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![21, 13, 1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![21, 13, 1]] 
 ![![29, 0, 0], ![0, 29, 0], ![21, 13, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![21, 13, 1], ![100, -3, 118], ![1138, -305, 10]]]
  hmulB := by decide  
  f := ![![![-20, -13, -1], ![29, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -13, 29]], ![![0, 0, 1], ![-82, -53, 118], ![32, -15, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [16, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 28], [0, 1]]
 g := ![![[27, 20], [16], [7, 20], [3, 1]], ![[0, 9], [16], [9, 9], [6, 28]]]
 h' := ![![[3, 28], [21, 22], [4, 4], [10, 22], [0, 1]], ![[0, 1], [0, 7], [16, 25], [18, 7], [3, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [1, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [16, 26, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5473, 1434, -7191]
  a := ![2, 1, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5396, 3273, -7191]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-2, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-2, 1, 0]] 
 ![![29, 0, 0], ![27, 1, 0], ![19, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-2, 1, 0], ![1, -2, 9], ![87, -24, -1]]]
  hmulB := by decide  
  f := ![![![-275, 558, -2520], ![58, 8120, 0]], ![![-255, 518, -2340], ![59, 7540, 0]], ![![-181, 366, -1651], ![26, 5320, 0]]]
  g := ![![![1, 0, 0], ![-27, 29, 0], ![-19, 0, 29]], ![![-1, 1, 0], ![-4, -2, 9], ![26, -24, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![21, 13, 1]] ![![29, 0, 0], ![-2, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![-58, 29, 0]], ![![609, 377, 29], ![58, -29, 116]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![-2, 1, 0]]], ![![![21, 13, 1]], ![![2, -1, 4]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0]] 
 ![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [29, 16, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 26, 30], [14, 4, 1], [0, 1]]
 g := ![![[0, 9, 25], [8, 23, 25], [25, 2, 10], [1]], ![[7, 10, 11, 3], [12, 6], [29, 2, 13, 24], [27, 0, 2, 30]], ![[27, 21, 8, 5], [9, 20, 18, 25], [27, 14, 24, 18], [11, 4, 26, 1]]]
 h' := ![![[0, 26, 30], [16, 0, 26], [19, 11, 26], [2, 15, 14], [0, 1]], ![[14, 4, 1], [24, 19, 11], [27, 26], [23, 2, 10], [0, 26, 30]], ![[0, 1], [25, 12, 25], [27, 25, 5], [7, 14, 7], [14, 4, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 15], []]
 b := ![[], [4, 25, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [29, 16, 17, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-28201351, 21526400, -37833640]
  a := ![-5, 0, -40]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-909721, 694400, -1220440]
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



lemma PB230I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB230I0 : PrimesBelowBoundCertificateInterval O 1 31 230 where
  m := 11
  g := ![2, 2, 1, 3, 2, 1, 3, 3, 2, 2, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB230I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N1]
    · exact ![I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N1]
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
    · exact ![4, 2]
    · exact ![3, 9]
    · exact ![125]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![2197]
    · exact ![17, 17, 17]
    · exact ![19, 19, 19]
    · exact ![23, 529]
    · exact ![841, 29]
    · exact ![29791]
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
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
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
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I7N0, I7N1, I7N2, I11N0, I11N1, I17N0, I17N1, I17N2, I19N0, I19N1, I19N2, I23N0, I29N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N1], [I5N0], [I7N0, I7N1, I7N2], [I11N0, I11N1], [], [I17N0, I17N1, I17N2], [I19N0, I19N1, I19N2], [I23N0], [I29N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
