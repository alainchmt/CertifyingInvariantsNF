
import IdealArithmetic.Examples.NF3_3_902356_1.RI3_3_902356_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, -1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![0, -1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![0, -1, 0], ![-2, -1, -5], ![0, -35, 1]]]
  hmulB := by decide  
  f := ![![![176, -1, -5]], ![![-1, 0, 0]], ![![-35, 0, 1]]]
  g := ![![![0, -1, 0], ![-1, -1, -5], ![0, -35, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![0, -1, 0]] ![![0, -1, 0]]
  ![![2, 1, 5]] where
 M := ![![![2, 1, 5]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 1, 5]] ![![0, -1, 0]]
  ![![2, 0, 0]] where
 M := ![![![-2, -178, 0]]]
 hmul := by decide  
 g := ![![![![-1, -89, 0]]]]
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
  c := ![-64797, -127098, -159330]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21599, -42366, -53110]
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


def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 20, 7]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![3, 20, 7]] 
 ![![5, 0, 0], ![1, 1, 0], ![4, 0, 1]] where
  M :=![![![3, 20, 7], ![40, 268, 93], ![98, 651, 228]]]
  hmulB := by decide  
  f := ![![![-561, 3, 16]], ![![-111, 1, 3]], ![![-404, 1, 12]]]
  g := ![![![-9, 20, 7], ![-120, 268, 93], ![-293, 651, 228]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, 65, -26]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-21, 65, -26]] 
 ![![5, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-21, 65, -26], ![130, -866, 351], ![-364, 2457, -996]]]
  hmulB := by decide  
  f := ![![![-129, -858, -299]], ![![-369, -2462, -858]], ![![-863, -5759, -2007]]]
  g := ![![![-12, 65, -26], ![129, -866, 351], ![-365, 2457, -996]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1

def I5N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49, -2, -2]] i)))

def SI5N2: IdealEqSpanCertificate' Table ![![49, -2, -2]] 
 ![![5, 0, 0], ![3, 1, 0], ![0, 0, 1]] where
  M :=![![![49, -2, -2], ![-4, -23, -8], ![-28, -56, -19]]]
  hmulB := by decide  
  f := ![![![-11, 74, -30]], ![![23, -153, 62]], ![![-84, 560, -227]]]
  g := ![![![11, -2, -2], ![13, -23, -8], ![28, -56, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N2 : Nat.card (O ⧸ I5N2) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N2)

lemma isPrimeI5N2 : Ideal.IsPrime I5N2 := prime_ideal_of_norm_prime hp5.out _ NI5N2
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![3, 20, 7]] ![![-21, 65, -26]]
  ![![-11, 74, -30]] where
 M := ![![![-11, 74, -30]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-11, 74, -30]] ![![49, -2, -2]]
  ![![5, 0, 0]] where
 M := ![![![5, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1, I5N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
    exact isPrimeI5N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, 5, 2]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-9, 5, 2]] 
 ![![7, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-9, 5, 2], ![10, 66, 23], ![28, 161, 56]]]
  hmulB := by decide  
  f := ![![![-7, 42, -17]], ![![11, -74, 30]], ![![-34, 227, -92]]]
  g := ![![![-2, 5, 2], ![-8, 66, 23], ![-19, 161, 56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-100549, 571, 2854]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-100549, 571, 2854]] 
 ![![7, 0, 0], ![5, 1, 0], ![0, 0, 1]] where
  M :=![![![-100549, 571, 2854], ![1142, -88, 1], ![39956, 7, -1230]]]
  hmulB := by decide  
  f := ![![![108233, 722308, 251723]], ![![283683, 1893198, 659776]], ![![503446, 3359817, 1170890]]]
  g := ![![![-14772, 571, 2854], ![226, -88, 1], ![5703, 7, -1230]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-9, 5, 2]] ![![-9, 5, 2]]
  ![![187, 607, 209]] where
 M := ![![![187, 607, 209]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![187, 607, 209]] ![![-100549, 571, 2854]]
  ![![7, 0, 0]] where
 M := ![![![-9758665, 54824, 277235]]]
 hmul := by decide  
 g := ![![![![-1394095, 7832, 39605]]]]
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


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [8, 10, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 3, 9], [7, 7, 2], [0, 1]]
 g := ![![[9, 8, 3], [2, 1, 1], []], ![[5, 9, 8, 9], [7, 4, 10, 1], [3, 4]], ![[9, 2, 8, 6], [1, 2, 3, 7], [10, 4]]]
 h' := ![![[5, 3, 9], [6, 5, 6], [0, 0, 1], [0, 1]], ![[7, 7, 2], [4, 10, 10], [1, 1, 7], [5, 3, 9]], ![[0, 1], [9, 7, 6], [2, 10, 3], [7, 7, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 5], []]
 b := ![[], [1, 8, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [8, 10, 10, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1136113, -1106105, 2887742]
  a := ![5, 0, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![103283, -100555, 262522]
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


def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![155, -1024, 415]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![155, -1024, 415]] 
 ![![13, 0, 0], ![8, 1, 0], ![12, 0, 1]] where
  M :=![![![155, -1024, 415], ![-2048, 13656, -5535], ![5810, -38745, 15704]]]
  hmulB := by decide  
  f := ![![![-249, -1721, -600]], ![![-418, -2826, -985]], ![![-876, -5899, -2056]]]
  g := ![![![259, -1024, 415], ![-3452, 13656, -5535], ![9794, -38745, 15704]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 287, 100]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![43, 287, 100]] 
 ![![13, 0, 0], ![9, 1, 0], ![11, 0, 1]] where
  M :=![![![43, 287, 100], ![574, 3830, 1335], ![1400, 9345, 3256]]]
  hmulB := by decide  
  f := ![![![5095, -28, -145]], ![![3523, -20, -100]], ![![4155, -21, -119]]]
  g := ![![![-280, 287, 100], ![-3737, 3830, 1335], ![-9117, 9345, 3256]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![155, -1024, 415]] ![![43, 287, 100]]
  ![![-111, 740, -300]] where
 M := ![![![-111, 740, -300]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-111, 740, -300]] ![![43, 287, 100]]
  ![![13, 0, 0]] where
 M := ![![![-13, -1157, 0]]]
 hmul := by decide  
 g := ![![![![-1, -89, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, -158, 64]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![25, -158, 64]] 
 ![![17, 0, 0], ![4, 1, 0], ![10, 0, 1]] where
  M :=![![![25, -158, 64], ![-316, 2107, -854], ![896, -5978, 2423]]]
  hmulB := by decide  
  f := ![![![49, 242, 84]], ![![40, 247, 86]], ![![98, 606, 211]]]
  g := ![![![1, -158, 64], ![-12, 2107, -854], ![34, -5978, 2423]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-89, -594, -207]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-89, -594, -207]] 
 ![![17, 0, 0], ![6, 1, 0], ![9, 0, 1]] where
  M :=![![![-89, -594, -207], ![-1188, -7928, -2763], ![-2898, -19341, -6740]]]
  hmulB := by decide  
  f := ![![![4463, -27, -126]], ![![1572, -8, -45]], ![![2259, -18, -62]]]
  g := ![![![314, -594, -207], ![4191, -7928, -2763], ![10224, -19341, -6740]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -19, -7]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![-3, -19, -7]] 
 ![![17, 0, 0], ![7, 1, 0], ![13, 0, 1]] where
  M :=![![![-3, -19, -7], ![-38, -267, -88], ![-98, -616, -229]]]
  hmulB := by decide  
  f := ![![![-6935, 39, 197]], ![![-2851, 16, 81]], ![![-5141, 29, 146]]]
  g := ![![![13, -19, -7], ![175, -267, -88], ![423, -616, -229]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![25, -158, 64]] ![![-89, -594, -207]]
  ![![7, -50, 19]] where
 M := ![![![7, -50, 19]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![7, -50, 19]] ![![-3, -19, -7]]
  ![![17, 0, 0]] where
 M := ![![![17, 1513, 0]]]
 hmul := by decide  
 g := ![![![![1, 89, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-98543, 550, 2801]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-98543, 550, 2801]] 
 ![![19, 0, 0], ![0, 19, 0], ![6, 7, 1]] where
  M :=![![![-98543, 550, 2801], ![1100, 42, -51], ![39214, -357, -1058]]]
  hmulB := by decide  
  f := ![![![-3297, -22003, -7668]], ![![-44006, -293680, -102347]], ![![-22904, -152853, -53269]]]
  g := ![![![-6071, -1003, 2801], ![74, 21, -51], ![2398, 371, -1058]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [14, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 18], [0, 1]]
 g := ![![[6, 6], [5, 9], [7], [1]], ![[15, 13], [9, 10], [7], [1]]]
 h' := ![![[11, 18], [6, 14], [3, 16], [5, 11], [0, 1]], ![[0, 1], [8, 5], [8, 3], [12, 8], [11, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [18, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [14, 8, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![259680, 484049, 639063]
  a := ![-66, -64, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-188142, -209968, 639063]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3297, 22003, 7668]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![3297, 22003, 7668]] 
 ![![19, 0, 0], ![4, 1, 0], ![4, 0, 1]] where
  M :=![![![3297, 22003, 7668], ![44006, 293680, 102347], ![107352, 716429, 249674]]]
  hmulB := by decide  
  f := ![![![98543, -550, -2801]], ![![20688, -118, -587]], ![![18682, -97, -534]]]
  g := ![![![-6073, 22003, 7668], ![-81058, 293680, 102347], ![-197740, 716429, 249674]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-98543, 550, 2801]] ![![3297, 22003, 7668]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-87, 2, 3]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-87, 2, 3]] 
 ![![23, 0, 0], ![0, 23, 0], ![17, 16, 1]] where
  M :=![![![-87, 2, 3], ![4, 20, 7], ![42, 49, 16]]]
  hmulB := by decide  
  f := ![![![-1, 5, -2]], ![![10, -66, 27]], ![![5, -34, 14]]]
  g := ![![![-6, -2, 3], ![-5, -4, 7], ![-10, -9, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [1, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 22], [0, 1]]
 g := ![![[16, 1], [16, 1], [7, 3], [1]], ![[0, 22], [0, 22], [5, 20], [1]]]
 h' := ![![[7, 22], [7, 22], [16, 1], [22, 7], [0, 1]], ![[0, 1], [0, 1], [0, 22], [2, 16], [7, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [16, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [1, 16, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![331, 505, 815]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-588, -545, 815]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 5, -2]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-1, 5, -2]] 
 ![![23, 0, 0], ![13, 1, 0], ![10, 0, 1]] where
  M :=![![![-1, 5, -2], ![10, -66, 27], ![-28, 189, -76]]]
  hmulB := by decide  
  f := ![![![-87, 2, 3]], ![![-49, 2, 2]], ![![-36, 3, 2]]]
  g := ![![![-2, 5, -2], ![26, -66, 27], ![-75, 189, -76]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-87, 2, 3]] ![![-1, 5, -2]]
  ![![23, 0, 0]] where
 M := ![![![23, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14617, 97550, 33996]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![14617, 97550, 33996]] 
 ![![29, 0, 0], ![0, 29, 0], ![11, 21, 1]] where
  M :=![![![14617, 97550, 33996], ![195100, 1302027, 453754], ![475944, 3176278, 1106927]]]
  hmulB := by decide  
  f := ![![![-227, 622, -248]], ![![1244, -8285, 3358]], ![![695, -4953, 2009]]]
  g := ![![![-12391, -21254, 33996], ![-165386, -283683, 453754], ![-403457, -692041, 1106927]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [23, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 28], [0, 1]]
 g := ![![[23, 24], [4], [15, 9], [22, 1]], ![[0, 5], [4], [10, 20], [15, 28]]]
 h' := ![![[22, 28], [4, 13], [3, 2], [16, 26], [0, 1]], ![[0, 1], [0, 16], [18, 27], [8, 3], [22, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [15, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [23, 7, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1621, 10661, 3717]
  a := ![3, 21, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1354, -2324, 3717]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, -622, 248]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![227, -622, 248]] 
 ![![29, 0, 0], ![12, 1, 0], ![4, 0, 1]] where
  M :=![![![227, -622, 248], ![-1244, 8285, -3358], ![3472, -23506, 9529]]]
  hmulB := by decide  
  f := ![![![-14617, -97550, -33996]], ![![-12776, -85263, -29714]], ![![-18428, -122982, -42859]]]
  g := ![![![231, -622, 248], ![-3008, 8285, -3358], ![8532, -23506, 9529]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![14617, 97550, 33996]] ![![227, -622, 248]]
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


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [9, 8, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 14, 16], [19, 16, 15], [0, 1]]
 g := ![![[30, 29, 25], [30, 8, 2], [14, 21, 9], [1]], ![[10, 25, 18, 5], [4, 22, 0, 7], [14, 9, 18, 19], [23, 2, 14, 4]], ![[7, 3, 29, 6], [21, 17, 26, 3], [5, 21, 12, 22], [18, 1, 24, 27]]]
 h' := ![![[9, 14, 16], [9, 2, 26], [29, 28, 8], [22, 23, 28], [0, 1]], ![[19, 16, 15], [9, 30, 14], [6, 23, 18], [26, 7, 10], [9, 14, 16]], ![[0, 1], [7, 30, 22], [5, 11, 5], [1, 1, 24], [19, 16, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 4], []]
 b := ![[], [9, 2, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [9, 8, 3, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-175739, 354361, -451887]
  a := ![-3, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5669, 11431, -14577]
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



lemma PB212I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB212I0 : PrimesBelowBoundCertificateInterval O 1 31 212 where
  m := 11
  g := ![3, 1, 3, 3, 1, 3, 3, 2, 2, 2, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB212I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0]
    · exact ![I5N0, I5N1, I5N2]
    · exact ![I7N0, I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1, I13N1]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0, I19N1]
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
    · exact ![2, 2, 2]
    · exact ![27]
    · exact ![5, 5, 5]
    · exact ![7, 7, 7]
    · exact ![1331]
    · exact ![13, 13, 13]
    · exact ![17, 17, 17]
    · exact ![361, 19]
    · exact ![529, 23]
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
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
      exact NI5N2
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
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
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
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
  β := ![I2N0, I3N0, I5N0, I5N1, I5N2, I7N0, I7N1, I13N0, I13N1, I17N0, I17N1, I17N2, I19N1, I23N1, I29N1]
  Il := ![[I2N0, I2N0, I2N0], [I3N0], [I5N0, I5N1, I5N2], [I7N0, I7N0, I7N1], [], [I13N0, I13N1, I13N1], [I17N0, I17N1, I17N2], [I19N1], [I23N1], [I29N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
