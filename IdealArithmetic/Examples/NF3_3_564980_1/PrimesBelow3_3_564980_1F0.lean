
import IdealArithmetic.Examples.NF3_3_564980_1.RI3_3_564980_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7422, -9270, -2045]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-7422, -9270, -2045]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-7422, -9270, -2045], ![-74710, -93312, -20585], ![-372305, -465005, -102582]]]
  hmulB := by decide  
  f := ![![![3659, 85, -90]], ![![432, -18, -5]], ![![-305, 120, -18]]]
  g := ![![![924, -9270, -2045], ![9301, -93312, -20585], ![46350, -465005, -102582]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-7422, -9270, -2045]] ![![-7422, -9270, -2045]]
  ![![1509011509, 1884739405, 415781130]] where
 M := ![![![1509011509, 1884739405, 415781130]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![1509011509, 1884739405, 415781130]] ![![-7422, -9270, -2045]]
  ![![2, 0, 0]] where
 M := ![![![-306806157971998, -383197644403440, -84534949065490]]]
 hmul := by decide  
 g := ![![![![-153403078985999, -191598822201720, -42267474532745]]]]
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
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![314, 5, -8]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![314, 5, -8]] 
 ![![3, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![314, 5, -8], ![-251, -22, 2], ![-136, -86, -17]]]
  hmulB := by decide  
  f := ![![![-546, -773, 166]], ![![1513, 2142, -460]], ![![-6562, -9290, 1995]]]
  g := ![![![110, 5, -8], ![-85, -22, 2], ![-34, -86, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-546, -773, 166]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-546, -773, 166]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 1, 1]] where
  M :=![![![-546, -773, 166], ![4539, 6426, -1380], ![-18594, -26324, 5653]]]
  hmulB := by decide  
  f := ![![![314, 5, -8]], ![![-251, -22, 2]], ![![-129, -36, -5]]]
  g := ![![![-182, -313, 166], ![1513, 2602, -1380], ![-6198, -10659, 5653]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P1 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2], [0, 1]]
 g := ![![[2, 1]], ![[1, 2]]]
 h' := ![![[2, 2], [0, 1]], ![[0, 1], [2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N1 : CertifiedPrimeIdeal' SI3N1 3 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P3P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![279, 317, 176]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![93, 47, 176]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N1 B_one_repr
lemma NI3N1 : Nat.card (O ⧸ I3N1) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![314, 5, -8]] ![![-546, -773, 166]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![373, 8, -9]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![373, 8, -9]] 
 ![![5, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![373, 8, -9], ![-280, -5, 7], ![-77, 3, 3]]]
  hmulB := by decide  
  f := ![![![-36, -51, 11]], ![![53, 75, -16]], ![![-245, -347, 75]]]
  g := ![![![73, 8, -9], ![-55, -5, 7], ![-16, 3, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-606, -757, -167]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-606, -757, -167]] 
 ![![5, 0, 0], ![2, 1, 0], ![1, 0, 1]] where
  M :=![![![-606, -757, -167], ![-6101, -7620, -1681], ![-30403, -37973, -8377]]]
  hmulB := by decide  
  f := ![![![127, 102, -23]], ![![-76, -127, 27]], ![![508, 707, -152]]]
  g := ![![![215, -757, -167], ![2164, -7620, -1681], ![10784, -37973, -8377]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![373, 8, -9]] ![![373, 8, -9]]
  ![![137582, 2917, -3328]] where
 M := ![![![137582, 2917, -3328]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![137582, 2917, -3328]] ![![-606, -757, -167]]
  ![![5, 0, 0]] where
 M := ![![![9875, -2970, -1015]]]
 hmul := by decide  
 g := ![![![![1975, -594, -203]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-371, -8, 9]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-371, -8, 9]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 3, 1]] where
  M :=![![![-371, -8, 9], ![280, 7, -7], ![77, -3, -1]]]
  hmulB := by decide  
  f := ![![![-4, -5, -1]], ![![-37, -46, -11]], ![![-44, -55, -12]]]
  g := ![![![-53, -5, 9], ![40, 4, -7], ![11, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [3, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 6], [0, 1]]
 g := ![![[2, 4], [1, 1]], ![[6, 3], [2, 6]]]
 h' := ![![[1, 6], [4, 5], [0, 1]], ![[0, 1], [2, 2], [1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [5, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [3, 6, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![308, 65, 1088]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![44, -457, 1088]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 5, 1]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![4, 5, 1]] 
 ![![7, 0, 0], ![0, 1, 0], ![4, 0, 1]] where
  M :=![![![4, 5, 1], ![37, 46, 11], ![197, 247, 51]]]
  hmulB := by decide  
  f := ![![![371, 8, -9]], ![![-40, -1, 1]], ![![201, 5, -5]]]
  g := ![![![0, 5, 1], ![-1, 46, 11], ![-1, 247, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-371, -8, 9]] ![![4, 5, 1]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0]] 
 ![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [9, 8, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 6, 6], [7, 4, 5], [0, 1]]
 g := ![![[4, 1, 4], [8, 4, 1], []], ![[5, 3, 6, 2], [1, 6, 4, 8], [7, 3]], ![[10, 10, 0, 3], [0, 2, 7, 4], [8, 3]]]
 h' := ![![[8, 6, 6], [5, 10, 2], [0, 0, 1], [0, 1]], ![[7, 4, 5], [10, 9, 2], [1, 2, 4], [8, 6, 6]], ![[0, 1], [7, 3, 7], [10, 9, 6], [7, 4, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6], []]
 b := ![[], [3, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [9, 8, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-798883701, -899262958, -562066142]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-72625791, -81751178, -51096922]
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


def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, -1, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![10, -1, 0]] 
 ![![13, 0, 0], ![3, 1, 0], ![9, 0, 1]] where
  M :=![![![10, -1, 0], ![-1, 10, -2], ![-32, -42, 9]]]
  hmulB := by decide  
  f := ![![![-6, -9, -2]], ![![-7, -9, -2]], ![![-32, -41, -9]]]
  g := ![![![1, -1, 0], ![-1, 10, -2], ![1, -42, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 136, 30]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![109, 136, 30]] 
 ![![13, 0, 0], ![6, 1, 0], ![2, 0, 1]] where
  M :=![![![109, 136, 30], ![1096, 1369, 302], ![5462, 6822, 1505]]]
  hmulB := by decide  
  f := ![![![101, -20, 2]], ![![50, 5, -2]], ![![-28, -62, 13]]]
  g := ![![![-59, 136, 30], ![-594, 1369, 302], ![-2960, 6822, 1505]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![10, -1, 0]] ![![10, -1, 0]]
  ![![101, -20, 2]] where
 M := ![![![101, -20, 2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI13N1 : IdealMulLeCertificate' Table 
  ![![101, -20, 2]] ![![109, 136, 30]]
  ![![13, 0, 0]] where
 M := ![![![13, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N0
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [16, 3, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 12, 8], [1, 4, 9], [0, 1]]
 g := ![![[16, 7, 13], [11, 9], [0, 1], []], ![[5, 0, 6, 1], [11, 16], [13, 16], [5, 13]], ![[2, 2, 11, 9], [1, 15], [12, 8], [4, 13]]]
 h' := ![![[16, 12, 8], [11, 10, 8], [0, 1, 14], [0, 0, 1], [0, 1]], ![[1, 4, 9], [15, 14, 10], [15, 5, 13], [6, 8, 4], [16, 12, 8]], ![[0, 1], [10, 10, 16], [3, 11, 7], [5, 9, 12], [1, 4, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 16], []]
 b := ![[], [16, 7, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [16, 3, 0, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-243355, -257465, -228650]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14315, -15145, -13450]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-953, -1192, -263]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-953, -1192, -263]] 
 ![![19, 0, 0], ![0, 19, 0], ![18, 8, 1]] where
  M :=![![![-953, -1192, -263], ![-9608, -11999, -2647], ![-47875, -59795, -13191]]]
  hmulB := by decide  
  f := ![![![-76, -127, 27]], ![![737, 1058, -227]], ![![77, 97, -21]]]
  g := ![![![199, 48, -263], ![2002, 483, -2647], ![9977, 2407, -13191]]]
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
  c := ![276, 300, 142]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-120, -44, 142]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-76, -127, 27]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-76, -127, 27]] 
 ![![19, 0, 0], ![2, 1, 0], ![8, 0, 1]] where
  M :=![![![-76, -127, 27], ![737, 1058, -227], ![-3065, -4335, 931]]]
  hmulB := by decide  
  f := ![![![-953, -1192, -263]], ![![-606, -757, -167]], ![![-2921, -3649, -805]]]
  g := ![![![-2, -127, 27], ![23, 1058, -227], ![-97, -4335, 931]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-953, -1192, -263]] ![![-76, -127, 27]]
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


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [13, 19, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 14, 12], [3, 8, 11], [0, 1]]
 g := ![![[9, 10, 2], [18, 6, 16], [5, 1, 1], []], ![[17, 3, 18, 12], [13, 2, 14, 18], [2, 0, 13, 9], [20, 6]], ![[3, 18, 2, 15], [4, 15, 9, 21], [12, 18, 1, 17], [21, 6]]]
 h' := ![![[21, 14, 12], [19, 10, 5], [4, 7, 19], [0, 0, 1], [0, 1]], ![[3, 8, 11], [7, 8, 22], [2, 15, 6], [20, 15, 8], [21, 14, 12]], ![[0, 1], [17, 5, 19], [0, 1, 21], [12, 8, 14], [3, 8, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 11], []]
 b := ![[], [22, 5, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [13, 19, 22, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1583504, 1976919, 433366]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![68848, 85953, 18842]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -6, 1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-5, -6, 1]] 
 ![![29, 0, 0], ![0, 29, 0], ![24, 23, 1]] where
  M :=![![![-5, -6, 1], ![26, 37, -11], ![-155, -215, 31]]]
  hmulB := by decide  
  f := ![![![-42, -1, 1]], ![![31, 0, -1]], ![![-10, -1, 0]]]
  g := ![![![-1, -1, 1], ![10, 10, -11], ![-31, -32, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [4, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 28], [0, 1]]
 g := ![![[10, 22], [28], [19, 1], [18, 1]], ![[0, 7], [28], [8, 28], [7, 28]]]
 h' := ![![[18, 28], [9, 14], [11, 12], [15, 1], [0, 1]], ![[0, 1], [0, 15], [24, 17], [4, 28], [18, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [1, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [4, 11, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-248, -402, 357]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-304, -297, 357]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![42, 1, -1]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![42, 1, -1]] 
 ![![29, 0, 0], ![11, 1, 0], ![27, 0, 1]] where
  M :=![![![42, 1, -1], ![-31, 0, 1], ![-5, 5, 1]]]
  hmulB := by decide  
  f := ![![![5, 6, -1]], ![![1, 1, 0]], ![![10, 13, -2]]]
  g := ![![![2, 1, -1], ![-2, 0, 1], ![-3, 5, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-5, -6, 1]] ![![42, 1, -1]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0]] 
 ![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [19, 18, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 6, 8], [13, 24, 23], [0, 1]]
 g := ![![[12, 28, 16], [4, 1, 16], [17, 29, 4], [1]], ![[1, 25, 11, 8], [8, 10, 3, 10], [21, 1, 8, 10], [5, 26, 6, 16]], ![[22, 30, 1, 21], [19, 13, 10, 11], [18, 29, 21, 23], [25, 3, 19, 15]]]
 h' := ![![[20, 6, 8], [17, 16, 27], [18, 0, 27], [12, 13, 2], [0, 1]], ![[13, 24, 23], [13, 9, 1], [4, 6, 28], [0, 13, 28], [20, 6, 8]], ![[0, 1], [26, 6, 3], [5, 25, 7], [17, 5, 1], [13, 24, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 29], []]
 b := ![[], [11, 30, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [19, 18, 29, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![272366, 318959, 148676]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8786, 10289, 4796]
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



lemma PB168I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB168I0 : PrimesBelowBoundCertificateInterval O 1 31 168 where
  m := 11
  g := ![3, 2, 3, 2, 1, 3, 1, 2, 1, 2, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB168I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0, I3N1]
    · exact ![I5N0, I5N0, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
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
    · exact ![2, 2, 2]
    · exact ![3, 9]
    · exact ![5, 5, 5]
    · exact ![49, 7]
    · exact ![1331]
    · exact ![13, 13, 13]
    · exact ![4913]
    · exact ![361, 19]
    · exact ![12167]
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
      exact NI2N0
      exact NI2N0
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N1
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
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
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
  β := ![I2N0, I3N0, I3N1, I5N0, I5N1, I7N0, I7N1, I13N0, I13N1, I19N1, I29N1]
  Il := ![[I2N0, I2N0, I2N0], [I3N0, I3N1], [I5N0, I5N0, I5N1], [I7N0, I7N1], [], [I13N0, I13N0, I13N1], [], [I19N1], [], [I29N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
