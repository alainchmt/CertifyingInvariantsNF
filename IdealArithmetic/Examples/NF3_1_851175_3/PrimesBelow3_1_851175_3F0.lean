
import IdealArithmetic.Examples.NF3_1_851175_3.RI3_1_851175_3
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
  c := ![4682, 24658, -35148]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2341, 12329, -17574]
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


def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![24, 1, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![24, 1, 1]] 
 ![![3, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![24, 1, 1], ![111, -10, 2], ![49, 14, -11]]]
  hmulB := by decide  
  f := ![![![-21, 23, -27], ![15, 0, -6]], ![![-7, 8, -9], ![5, 0, -2]], ![![-22, 15, -18], ![11, 0, -4]]]
  g := ![![![1, 0, 0], ![-1, 3, 0], ![-2, 0, 3]], ![![7, 1, 1], ![39, -10, 2], ![19, 14, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![24, 1, 1]] ![![3, 0, 0], ![24, 1, 1]]
  ![![3, 0, 0], ![1, 1, 0]] where
 M := ![![![9, 0, 0], ![72, 3, 3]], ![![72, 3, 3], ![736, 28, 15]]]
 hmul := by decide  
 g := ![![![![2, -1, 0], ![3, 0, 0]], ![![21, -2, 1], ![9, 0, 0]]], ![![![21, -2, 1], ![9, 0, 0]], ![![222, -14, 5], ![70, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![24, 1, 1]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![72, 3, 3]], ![![3, 3, 0], ![135, -9, 3]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![24, 1, 1]]], ![![![1, 1, 0]], ![![45, -3, 1]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-40228, -1409, -1071]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-40228, -1409, -1071]] 
 ![![5, 0, 0], ![0, 1, 0], ![3, 0, 1]] where
  M :=![![![-40228, -1409, -1071], ![-118543, -4152, -3156], ![-90335, -3164, -2405]]]
  hmulB := by decide  
  f := ![![![24, 1, -12]], ![![-269, 89, 3]], ![![188, -124, 79]]]
  g := ![![![-7403, -1409, -1071], ![-21815, -4152, -3156], ![-16624, -3164, -2405]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-40228, -1409, -1071]] ![![-40228, -1409, -1071]]
  ![![1882067856, 65920064, 50106747]] where
 M := ![![![1882067856, 65920064, 50106747]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![1882067856, 65920064, 50106747]] ![![-40228, -1409, -1071]]
  ![![5, 0, 0]] where
 M := ![![![-88052580848165, -3084071462340, -2344245122295]]]
 hmul := by decide  
 g := ![![![![-17610516169633, -616814292468, -468849024459]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![1, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![1, 1, 0]] 
 ![![7, 0, 0], ![1, 1, 0], ![6, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![1, 1, 0], ![-1, 2, 3], ![112, -35, 0]]]
  hmulB := by decide  
  f := ![![![-5, 9, 15], ![7, -35, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-4, 8, 13], ![4, -30, 0]]]
  g := ![![![1, 0, 0], ![-1, 7, 0], ![-6, 0, 7]], ![![0, 1, 0], ![-3, 2, 3], ![21, -35, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![2, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![2, 1, 0]] 
 ![![7, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![2, 1, 0], ![-1, 3, 3], ![112, -35, 1]]]
  hmulB := by decide  
  f := ![![![-1, -1, 0], ![7, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-1, -3, -2], ![6, 5, 0]]]
  g := ![![![1, 0, 0], ![-2, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![-1, 3, 3], ![26, -35, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -1, 0]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![3, -1, 0]] 
 ![![7, 0, 0], ![4, 1, 0], ![0, 0, 1]] where
  M :=![![![3, -1, 0], ![1, 2, -3], ![-112, 35, 4]]]
  hmulB := by decide  
  f := ![![![113, 4, 3]], ![![112, 4, 3]], ![![37, 1, 1]]]
  g := ![![![1, -1, 0], ![-1, 2, -3], ![-36, 35, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![1, 1, 0]] ![![7, 0, 0], ![2, 1, 0]]
  ![![-113, -4, -3]] where
 M := ![![![49, 0, 0], ![14, 7, 0]], ![![7, 7, 0], ![1, 4, 3]]]
 hmul := by decide  
 g := ![![![![-21, 7, 0]], ![![-7, 0, 3]]], ![![![-4, -1, 3]], ![![47, -16, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![-113, -4, -3]] ![![3, -1, 0]]
  ![![7, 0, 0]] where
 M := ![![![-7, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [2, 9, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 7, 5], [3, 3, 6], [0, 1]]
 g := ![![[7, 6, 4], [2, 0, 1], []], ![[2, 9, 3, 1], [2, 0, 7, 1], [4, 3]], ![[6, 5, 5, 6], [7, 2, 9, 8], [3, 3]]]
 h' := ![![[8, 7, 5], [7, 4, 9], [0, 0, 1], [0, 1]], ![[3, 3, 6], [4, 9, 3], [1, 4, 3], [8, 7, 5]], ![[0, 1], [2, 9, 10], [3, 7, 7], [3, 3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 5], []]
 b := ![[], [7, 10, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [2, 9, 0, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3942796, -1759296, 554400]
  a := ![-3, 0, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![358436, -159936, 50400]
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


def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![4, 1, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![4, 1, 0]] 
 ![![13, 0, 0], ![4, 1, 0], ![6, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![4, 1, 0], ![-1, 5, 3], ![112, -35, 3]]]
  hmulB := by decide  
  f := ![![![61, -300, -180], ![0, 780, 0]], ![![18, -90, -54], ![1, 234, 0]], ![![26, -139, -83], ![7, 360, 0]]]
  g := ![![![1, 0, 0], ![-4, 13, 0], ![-6, 0, 13]], ![![0, 1, 0], ![-3, 5, 3], ![18, -35, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-2, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-2, 1, 0]] 
 ![![13, 0, 0], ![11, 1, 0], ![12, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-2, 1, 0], ![-1, -1, 3], ![112, -35, -3]]]
  hmulB := by decide  
  f := ![![![-45, -49, 144], ![13, -624, 0]], ![![-37, -41, 120], ![14, -520, 0]], ![![-42, -45, 133], ![9, -576, 0]]]
  g := ![![![1, 0, 0], ![-11, 13, 0], ![-12, 0, 13]], ![![-1, 1, 0], ![-2, -1, 3], ![41, -35, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![4, 1, 0]] ![![13, 0, 0], ![-2, 1, 0]]
  ![![13, 0, 0], ![23, 1, 1]] where
 M := ![![![169, 0, 0], ![-26, 13, 0]], ![![52, 13, 0], ![-9, 3, 3]]]
 hmul := by decide  
 g := ![![![![-10, -1, -1], ![13, 0, 0]], ![![-2, 1, 0], ![0, 0, 0]]], ![![![-19, 0, -1], ![13, 0, 0]], ![![-6, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![23, 1, 1]] ![![13, 0, 0], ![-2, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![-26, 13, 0]], ![![299, 13, 13], ![65, -13, 0]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![-2, 1, 0]]], ![![![23, 1, 1]], ![![5, -1, 0]]]]
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [14, 3, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 2, 8], [3, 14, 9], [0, 1]]
 g := ![![[11, 1, 15], [13, 1], [2, 1], []], ![[6, 8, 9, 16], [6, 15], [2, 9], [7, 13]], ![[2, 16, 6, 9], [4, 13], [3, 4], [6, 13]]]
 h' := ![![[16, 2, 8], [7, 13, 10], [6, 14, 1], [0, 0, 1], [0, 1]], ![[3, 14, 9], [10, 13, 6], [14, 8, 7], [5, 14, 14], [16, 2, 8]], ![[0, 1], [10, 8, 1], [7, 12, 9], [10, 3, 2], [3, 14, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 10], []]
 b := ![[], [3, 3, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [14, 3, 15, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1017180873, -62756775, -387058380]
  a := ![1, -64, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![59834169, -3691575, -22768140]
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


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [17, 8, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 11], [18, 7], [0, 1]]
 g := ![![[15, 5, 17], [15, 7, 9], [10, 1], []], ![[18, 8, 5], [3, 13, 6], [2, 11], []], ![[8, 6, 16], [17, 18, 4], [9, 7], []]]
 h' := ![![[11, 11], [11, 9, 13], [1, 17, 16], [0, 0, 1], [0, 1]], ![[18, 7], [11, 15, 15], [15, 12, 17], [7, 14, 7], [11, 11]], ![[0, 1], [15, 14, 10], [0, 9, 5], [1, 5, 11], [18, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17], []]
 b := ![[], [17, 5, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [17, 8, 9, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3204692, 1548994, -606898]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-168668, 81526, -31942]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [6, 5, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 13, 7], [5, 9, 16], [0, 1]]
 g := ![![[8, 3, 13], [20, 7, 12], [4, 3, 1], []], ![[0, 22, 15, 10], [8, 12, 20, 5], [5, 6, 12, 15], [7, 3]], ![[17, 16, 3, 2], [14, 18, 4, 4], [13, 19, 22, 13], [21, 3]]]
 h' := ![![[21, 13, 7], [18, 20, 6], [22, 8, 14], [0, 0, 1], [0, 1]], ![[5, 9, 16], [3, 21, 10], [3, 14, 21], [8, 10, 9], [21, 13, 7]], ![[0, 1], [18, 5, 7], [5, 1, 11], [14, 13, 13], [5, 9, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 17], []]
 b := ![[], [16, 17, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [6, 5, 20, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20171, 25070, -41400]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![877, 1090, -1800]
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


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [18, 3, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 3, 4], [17, 25, 25], [0, 1]]
 g := ![![[10, 0, 13], [5, 5], [28, 18, 5], [1]], ![[3, 2, 4, 4], [13, 9], [17, 26, 23, 16], [20, 24, 7, 6]], ![[13, 27, 27, 9], [5, 6], [20, 13, 15, 20], [15, 8, 3, 23]]]
 h' := ![![[23, 3, 4], [2, 3, 10], [18, 3, 11], [11, 26, 11], [0, 1]], ![[17, 25, 25], [14, 20, 1], [4, 24, 26], [4, 6, 2], [23, 3, 4]], ![[0, 1], [13, 6, 18], [25, 2, 21], [3, 26, 16], [17, 25, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 18], []]
 b := ![[], [23, 18, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [18, 3, 18, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-444048, 518868, -292059]
  a := ![-1, 21, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15312, 17892, -10071]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![13, 7, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![13, 7, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![13, 7, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![13, 7, 1], ![105, -15, 20], ![721, -196, -28]]]
  hmulB := by decide  
  f := ![![![-12, -7, -1], ![31, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -7, 31]], ![![0, 0, 1], ![-5, -5, 20], ![35, 0, -28]]]
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
  c := ![-1890, 1076, -577]
  a := ![1, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![181, 165, -577]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![11, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![11, 1, 0]] 
 ![![31, 0, 0], ![11, 1, 0], ![28, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![11, 1, 0], ![-1, 12, 3], ![112, -35, 10]]]
  hmulB := by decide  
  f := ![![![-265, 3059, 765], ![31, -7905, 0]], ![![-101, 1079, 270], ![32, -2790, 0]], ![![-239, 2763, 691], ![27, -7140, 0]]]
  g := ![![![1, 0, 0], ![-11, 31, 0], ![-28, 0, 31]], ![![0, 1, 0], ![-7, 12, 3], ![7, -35, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![13, 7, 1]] ![![31, 0, 0], ![11, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![341, 31, 0]], ![![403, 217, 31], ![248, 62, 31]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![11, 1, 0]]], ![![![13, 7, 1]], ![![8, 2, 1]]]]
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


lemma PB262I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB262I0 : PrimesBelowBoundCertificateInterval O 1 31 262 where
  m := 11
  g := ![1, 3, 3, 3, 1, 3, 1, 1, 1, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB262I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0]
    · exact ![I13N0, I13N1, I13N1]
    · exact ![I17N0]
    · exact ![I19N0]
    · exact ![I23N0]
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
    · exact ![8]
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![7, 7, 7]
    · exact ![1331]
    · exact ![13, 13, 13]
    · exact ![4913]
    · exact ![6859]
    · exact ![12167]
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
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
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
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
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
  β := ![I2N0, I3N0, I5N0, I7N0, I7N1, I7N2, I13N0, I13N1, I31N1]
  Il := ![[I2N0], [I3N0, I3N0, I3N0], [I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [], [I13N0, I13N1, I13N1], [], [], [], [], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
