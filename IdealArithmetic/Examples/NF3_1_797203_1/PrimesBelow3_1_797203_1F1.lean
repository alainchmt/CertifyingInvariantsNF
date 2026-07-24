
import IdealArithmetic.Examples.NF3_1_797203_1.RI3_1_797203_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [29, 23, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 20, 3], [22, 16, 34], [0, 1]]
 g := ![![[16, 11, 21], [5, 10], [10, 20, 28], [2, 1], []], ![[22, 24, 11, 10], [4, 36], [19, 35, 20, 30], [5, 34], [27, 9]], ![[36, 36, 24, 3], [18, 25], [17, 16, 16, 1], [0, 30], [33, 9]]]
 h' := ![![[17, 20, 3], [2, 14, 24], [6, 1, 11], [16, 36, 18], [0, 0, 1], [0, 1]], ![[22, 16, 34], [2, 20, 19], [28, 18, 31], [24, 7, 26], [24, 20, 16], [17, 20, 3]], ![[0, 1], [21, 3, 31], [5, 18, 32], [27, 31, 30], [8, 17, 20], [22, 16, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 35], []]
 b := ![[], [26, 29, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [29, 23, 35, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-636918, 382765, -183372]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17214, 10345, -4956]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [24, 17, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 25, 24], [22, 15, 17], [0, 1]]
 g := ![![[7, 11, 33], [8, 8], [15, 39], [20, 18, 1], []], ![[12, 18, 33, 12], [38, 39], [40, 9], [13, 26, 24, 29], [6, 2]], ![[31, 4, 40, 13], [38, 16], [26, 23], [11, 36, 16, 6], [13, 2]]]
 h' := ![![[37, 25, 24], [11, 38, 22], [30, 2, 7], [12, 7, 30], [0, 0, 1], [0, 1]], ![[22, 15, 17], [36, 15, 12], [28, 19, 30], [39, 7, 3], [36, 19, 15], [37, 25, 24]], ![[0, 1], [39, 29, 7], [7, 20, 4], [37, 27, 8], [8, 22, 25], [22, 15, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 24], []]
 b := ![[], [7, 25, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [24, 17, 23, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2077306, -657640, 185648]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![50666, -16040, 4528]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [4, 16, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 35, 26], [36, 7, 17], [0, 1]]
 g := ![![[33, 3, 35], [1, 1, 10], [29, 16], [41, 33, 1], []], ![[8, 0, 28, 22], [6, 0, 22, 7], [26, 21], [26, 3, 2, 27], [5, 31]], ![[17, 14, 12, 24], [38, 14, 15, 14], [40, 15], [13, 37, 26, 13], [14, 31]]]
 h' := ![![[40, 35, 26], [39, 18, 11], [34, 22, 15], [8, 29, 4], [0, 0, 1], [0, 1]], ![[36, 7, 17], [36, 32, 29], [18, 21, 32], [6, 4, 8], [32, 16, 7], [40, 35, 26]], ![[0, 1], [8, 36, 3], [33, 0, 39], [35, 10, 31], [36, 27, 35], [36, 7, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 23], []]
 b := ![[], [8, 40, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [4, 16, 10, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-493525491, 355249875, -202980898]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11477337, 8261625, -4720486]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![5, -13, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![5, -13, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![5, 34, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![5, -13, 1], ![126, -8, -50], ![-1875, 363, -46]]]
  hmulB := by decide  
  f := ![![![-4, 13, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -34, 47]], ![![0, -1, 1], ![8, 36, -50], ![-35, 41, -46]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [8, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 46], [0, 1]]
 g := ![![[35, 6], [21, 25], [8, 21], [23, 4], [1]], ![[0, 41], [24, 22], [3, 26], [31, 43], [1]]]
 h' := ![![[2, 46], [20, 37], [30, 5], [4, 31], [39, 2], [0, 1]], ![[0, 1], [0, 10], [40, 42], [19, 16], [43, 45], [2, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [10, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [8, 45, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-165, 3531, -2430]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![255, 1833, -2430]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![3, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![3, 1, 0]] 
 ![![47, 0, 0], ![3, 1, 0], ![46, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![3, 1, 0], ![2, 2, 4], ![152, -26, 5]]]
  hmulB := by decide  
  f := ![![![-351, -352, -704], ![0, 8272, 0]], ![![-22, -22, -44], ![1, 517, 0]], ![![-342, -344, -689], ![-24, 8096, 0]]]
  g := ![![![1, 0, 0], ![-3, 47, 0], ![-46, 0, 47]], ![![0, 1, 0], ![-4, 2, 4], ![0, -26, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![5, -13, 1]] ![![47, 0, 0], ![3, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![141, 47, 0]], ![![235, -611, 47], ![141, -47, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![3, 1, 0]]], ![![![5, -13, 1]], ![![3, -1, -1]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![13, 11, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![13, 11, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![13, 11, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![13, 11, 1], ![174, -24, 46], ![1773, -261, 10]]]
  hmulB := by decide  
  f := ![![![-12, -11, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -11, 53]], ![![0, 0, 1], ![-8, -10, 46], ![31, -7, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [28, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 52], [0, 1]]
 g := ![![[2, 36], [11], [32, 6], [43], [50, 1]], ![[0, 17], [11], [14, 47], [43], [47, 52]]]
 h' := ![![[50, 52], [35, 47], [5, 8], [22, 18], [31, 34], [0, 1]], ![[0, 1], [0, 6], [34, 45], [21, 35], [35, 19], [50, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [52, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [28, 3, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1842, 1208, -902]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![256, 210, -902]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![7, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![7, 1, 0]] 
 ![![53, 0, 0], ![7, 1, 0], ![43, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![7, 1, 0], ![2, 6, 4], ![152, -26, 9]]]
  hmulB := by decide  
  f := ![![![2073, 6376, 4256], ![424, -56392, 0]], ![![273, 839, 560], ![54, -7420, 0]], ![![1682, 5173, 3453], ![343, -45752, 0]]]
  g := ![![![1, 0, 0], ![-7, 53, 0], ![-43, 0, 53]], ![![0, 1, 0], ![-4, 6, 4], ![-1, -26, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![13, 11, 1]] ![![53, 0, 0], ![7, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![371, 53, 0]], ![![689, 583, 53], ![265, 53, 53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![7, 1, 0]]], ![![![13, 11, 1]], ![![5, 1, 1]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-28, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-28, 1, 0]] 
 ![![59, 0, 0], ![31, 1, 0], ![4, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-28, 1, 0], ![2, -29, 4], ![152, -26, -26]]]
  hmulB := by decide  
  f := ![![![2673, -53324, 7360], ![-2124, -108560, 0]], ![![1401, -27995, 3864], ![-1120, -56994, 0]], ![![204, -3616, 499], ![-96, -7360, 0]]]
  g := ![![![1, 0, 0], ![-31, 59, 0], ![-4, 0, 59]], ![![-1, 1, 0], ![15, -29, 4], ![18, -26, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-23, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-23, 1, 0]] 
 ![![59, 0, 0], ![36, 1, 0], ![10, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-23, 1, 0], ![2, -24, 4], ![152, -26, -21]]]
  hmulB := by decide  
  f := ![![![342, -4917, 820], ![-177, -12095, 0]], ![![205, -2998, 500], ![-117, -7375, 0]], ![![72, -834, 139], ![6, -2050, 0]]]
  g := ![![![1, 0, 0], ![-36, 59, 0], ![-10, 0, 59]], ![![-1, 1, 0], ![14, -24, 4], ![22, -26, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5011, -124, -164]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-5011, -124, -164]] 
 ![![59, 0, 0], ![50, 1, 0], ![37, 0, 1]] where
  M :=![![![-5011, -124, -164], ![-25176, -623, -824], ![-35412, -876, -1159]]]
  hmulB := by decide  
  f := ![![![-233, 52, -4]], ![![-206, 41, 0]], ![![-19, 8, -3]]]
  g := ![![![123, -124, -164], ![618, -623, -824], ![869, -876, -1159]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-28, 1, 0]] ![![59, 0, 0], ![-23, 1, 0]]
  ![![233, -52, 4]] where
 M := ![![![3481, 0, 0], ![-1357, 59, 0]], ![![-1652, 59, 0], ![646, -52, 4]]]
 hmul := by decide  
 g := ![![![![295649, 7316, 9676]], ![![-90077, -2229, -2948]]], ![![![-115132, -2849, -3768]], ![![35078, 868, 1148]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![233, -52, 4]] ![![-5011, -124, -164]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![10, -19, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![10, -19, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![10, 42, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![10, -19, 1], ![114, 3, -74], ![-2787, 519, -53]]]
  hmulB := by decide  
  f := ![![![-9, 19, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -42, 61]], ![![0, -1, 1], ![14, 51, -74], ![-37, 45, -53]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [46, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 60], [0, 1]]
 g := ![![[24, 4], [52], [4, 14], [41, 39], [55, 1]], ![[0, 57], [52], [42, 47], [51, 22], [49, 60]]]
 h' := ![![[55, 60], [49, 59], [60, 28], [5, 21], [32, 51], [0, 1]], ![[0, 1], [0, 2], [14, 33], [1, 40], [31, 10], [55, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [19, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [46, 6, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![174341, 48410, -44243]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10111, 31256, -44243]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![13, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![13, 1, 0]] 
 ![![61, 0, 0], ![13, 1, 0], ![53, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![13, 1, 0], ![2, 12, 4], ![152, -26, 15]]]
  hmulB := by decide  
  f := ![![![2545, 16342, 5452], ![854, -83143, 0]], ![![541, 3477, 1160], ![184, -17690, 0]], ![![2214, 14199, 4737], ![729, -72239, 0]]]
  g := ![![![1, 0, 0], ![-13, 61, 0], ![-53, 0, 61]], ![![0, 1, 0], ![-6, 12, 4], ![-5, -26, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![10, -19, 1]] ![![61, 0, 0], ![13, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![793, 61, 0]], ![![610, -1159, 61], ![244, -244, -61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![13, 1, 0]]], ![![![10, -19, 1]], ![![4, -4, -1]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![18, -6, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![18, -6, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![18, 61, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![18, -6, 1], ![140, -2, -22], ![-811, 181, -19]]]
  hmulB := by decide  
  f := ![![![-17, 6, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -61, 67]], ![![0, -1, 1], ![8, 20, -22], ![-7, 20, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [52, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 66], [0, 1]]
 g := ![![[53, 49], [27, 24], [25], [36], [14], [1]], ![[14, 18], [12, 43], [25], [36], [14], [1]]]
 h' := ![![[58, 66], [3, 60], [12, 52], [21, 5], [33, 6], [15, 58], [0, 1]], ![[0, 1], [66, 7], [13, 15], [43, 62], [46, 61], [29, 9], [58, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [37, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [52, 9, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![459, -19, -8]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9, 7, -8]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![22, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![22, 1, 0]] 
 ![![67, 0, 0], ![22, 1, 0], ![19, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![22, 1, 0], ![2, 21, 4], ![152, -26, 24]]]
  hmulB := by decide  
  f := ![![![531, 6715, 1280], ![335, -21440, 0]], ![![166, 2203, 420], ![135, -7035, 0]], ![![145, 1904, 363], ![112, -6080, 0]]]
  g := ![![![1, 0, 0], ![-22, 67, 0], ![-19, 0, 67]], ![![0, 1, 0], ![-8, 21, 4], ![4, -26, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![18, -6, 1]] ![![67, 0, 0], ![22, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![1474, 67, 0]], ![![1206, -402, 67], ![536, -134, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![22, 1, 0]]], ![![![18, -6, 1]], ![![8, -2, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![51, -11, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![51, -11, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![51, 60, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![51, -11, 1], ![130, 36, -42], ![-1571, 311, 4]]]
  hmulB := by decide  
  f := ![![![-50, 11, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -60, 71]], ![![0, -1, 1], ![32, 36, -42], ![-25, 1, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [38, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 70], [0, 1]]
 g := ![![[9, 43], [69, 60], [47, 45], [4], [27], [1]], ![[0, 28], [68, 11], [64, 26], [4], [27], [1]]]
 h' := ![![[13, 70], [5, 16], [60, 42], [54, 20], [63, 2], [33, 13], [0, 1]], ![[0, 1], [0, 55], [38, 29], [30, 51], [18, 69], [60, 58], [13, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [30, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [38, 58, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4381, 3400, -1884]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1415, 1640, -1884]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-29, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-29, 1, 0]] 
 ![![71, 0, 0], ![42, 1, 0], ![67, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-29, 1, 0], ![2, -30, 4], ![152, -26, -27]]]
  hmulB := by decide  
  f := ![![![1634, -31005, 4136], ![-1065, -73414, 0]], ![![962, -18321, 2444], ![-638, -43381, 0]], ![![1535, -29258, 3903], ![-1022, -69278, 0]]]
  g := ![![![1, 0, 0], ![-42, 71, 0], ![-67, 0, 71]], ![![-1, 1, 0], ![14, -30, 4], ![43, -26, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![51, -11, 1]] ![![71, 0, 0], ![-29, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-2059, 71, 0]], ![![3621, -781, 71], ![-1349, 355, -71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-29, 1, 0]]], ![![![51, -11, 1]], ![![-19, 5, -1]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![806470171300900607435325181789818707757169972, 19955446934497290175824972101272522415784577, 26394412076745244485293300417889584072726643]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![806470171300900607435325181789818707757169972, 19955446934497290175824972101272522415784577, 26394412076745244485293300417889584072726643]] 
 ![![73, 0, 0], ![0, 73, 0], ![18, 10, 1]] where
  M :=![![![806470171300900607435325181789818707757169972, 19955446934497290175824972101272522415784577, 26394412076745244485293300417889584072726643], ![4051861529534271742116231607721761823886018890, 100260010371026960641874398823416999450492677, 132610611891479649673886489240869257808591594], ![5699063553794857799740019101600271398544646647, 141018681621701567560883235814154019007767073, 186520763251264075654642615545124150770573051]]]
  hmulB := by decide  
  f := ![![![2681849987802447003605, 804806734646028597144, -951699768688687907501]], ![![-143048751371388504745864, 26621237239062304001487, 1315827401206738573574]], ![![-18575414615134275798431, 3232622250633391966441, 330296381506612401180]]]
  g := ![![![4539325396157345297260901017367208143124526, -3342310600451440475028877151748264634403861, 26394412076745244485293300417889584072726643], ![22806445417638877369674997279261851826457126, -16792412445805062138314938268291446282677031, 132610611891479649673886489240869257808591594], ![32077942674960334766526740024493653214716873, -23619026724533413547747163282699828612300869, 186520763251264075654642615545124150770573051]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [18, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 72], [0, 1]]
 g := ![![[72, 69], [67], [71], [25, 1], [32], [1]], ![[0, 4], [67], [71], [43, 72], [32], [1]]]
 h' := ![![[18, 72], [23, 19], [34, 33], [61, 61], [40, 1], [55, 18], [0, 1]], ![[0, 1], [0, 54], [44, 40], [64, 12], [58, 72], [14, 55], [18, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [47, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [18, 55, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2293, 625, -850]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![241, 125, -850]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29880217, -5786072, -114605]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![29880217, -5786072, -114605]] 
 ![![73, 0, 0], ![31, 1, 0], ![60, 0, 1]] where
  M :=![![![29880217, -5786072, -114605], ![-28992104, 38646019, -23373498], ![-891058049, 147572747, 21173198]]]
  hmulB := by decide  
  f := ![![![4267551119057768, 105597073428321, 139669769327351]], ![![2105960051717874, 52110264649264, 68924529883779]], ![![3920691356255251, 97014311366393, 128317632772215]]]
  g := ![![![2960613, -5786072, -114605], ![2402619, 38646019, -23373498], ![-92276782, 147572747, 21173198]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![806470171300900607435325181789818707757169972, 19955446934497290175824972101272522415784577, 26394412076745244485293300417889584072726643]] ![![29880217, -5786072, -114605]]
  ![![73, 0, 0]] where
 M := ![![![10176557351462394957787749364409, 251810615481779728111176017300, 333061603287632566681168532908]]]
 hmul := by decide  
 g := ![![![![139404895225512259695722594033, 3449460486051777097413370100, 4562487716268939269605048396]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [26, 73, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 45, 65], [5, 33, 14], [0, 1]]
 g := ![![[51, 16, 55], [62, 63, 21], [11, 34, 65], [78, 18, 19], [22, 1], []], ![[22, 50, 41, 31], [17, 22, 44, 65], [29, 22, 9, 65], [39, 20, 7, 52], [56, 62], [50, 38]], ![[62, 73, 61, 77], [67, 1, 13, 35], [13, 46, 57, 35], [10, 56, 76, 27], [54, 50], [22, 38]]]
 h' := ![![[17, 45, 65], [47, 29, 23], [30, 16, 69], [26, 45, 67], [60, 27, 16], [0, 0, 1], [0, 1]], ![[5, 33, 14], [39, 52, 37], [63, 42, 78], [46, 58, 1], [64, 72, 71], [16, 52, 33], [17, 45, 65]], ![[0, 1], [14, 77, 19], [50, 21, 11], [21, 55, 11], [54, 59, 71], [6, 27, 45], [5, 33, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 30], []]
 b := ![[], [54, 65, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [26, 73, 57, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1668954, 891278, -898862]
  a := ![-4, -2, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![21126, 11282, -11378]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB253I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB253I1 : PrimesBelowBoundCertificateInterval O 31 79 253 where
  m := 11
  g := ![1, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB253I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![68921]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I47N1, I53N1, I59N0, I59N1, I59N2, I61N1, I67N1, I71N1, I73N1]
  Il := ![[], [], [], [I47N1], [I53N1], [I59N0, I59N1, I59N2], [I61N1], [I67N1], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
