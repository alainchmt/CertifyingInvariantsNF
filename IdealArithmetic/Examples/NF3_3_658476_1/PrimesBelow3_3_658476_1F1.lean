
import IdealArithmetic.Examples.NF3_3_658476_1.RI3_3_658476_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103649, 5003808, 967962]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![103649, 5003808, 967962]] 
 ![![37, 0, 0], ![0, 37, 0], ![32, 30, 1]] where
  M :=![![![103649, 5003808, 967962], ![967962, 46729823, 9039654], ![4035846, 194836542, 37690169]]]
  hmulB := by decide  
  f := ![![![713, 8004, -1938]], ![![-1938, -74617, 17946]], ![![-686, -43176, 10373]]]
  g := ![![![-834355, -649596, 967962], ![-7791918, -6066481, 9039654], ![-32487826, -25293744, 37690169]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [36, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 36], [0, 1]]
 g := ![![[32, 36], [33], [16, 21], [25], [1]], ![[0, 1], [33], [22, 16], [25], [1]]]
 h' := ![![[32, 36], [30, 6], [16, 25], [26, 13], [1, 32], [0, 1]], ![[0, 1], [0, 31], [2, 12], [35, 24], [26, 5], [32, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [33, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [36, 5, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![39, 321, 377]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-325, -297, 377]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![713, 8004, -1938]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![713, 8004, -1938]] 
 ![![37, 0, 0], ![15, 1, 0], ![28, 0, 1]] where
  M :=![![![713, 8004, -1938], ![-1938, -74617, 17946], ![9942, 384870, -92563]]]
  hmulB := by decide  
  f := ![![![103649, 5003808, 967962]], ![![68181, 3291539, 636732]], ![![187514, 9052518, 1751165]]]
  g := ![![![-1759, 8004, -1938], ![16617, -74617, 17946], ![-85712, 384870, -92563]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![103649, 5003808, 967962]] ![![713, 8004, -1938]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3741, -42, -86]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![3741, -42, -86]] 
 ![![41, 0, 0], ![2, 1, 0], ![38, 0, 1]] where
  M :=![![![3741, -42, -86], ![-86, 1, 2], ![44, 0, -1]]]
  hmulB := by decide  
  f := ![![![1, 42, -2]], ![![0, 1, 2]], ![![2, 84, -5]]]
  g := ![![![173, -42, -86], ![-4, 1, 2], ![2, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1974, 95319, 18439]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![1974, 95319, 18439]] 
 ![![41, 0, 0], ![16, 1, 0], ![28, 0, 1]] where
  M :=![![![1974, 95319, 18439], ![18439, 890170, 172199], ![76880, 3711498, 717971]]]
  hmulB := by decide  
  f := ![![![-968, -33873, 8149]], ![![-179, -5522, 1329]], ![![-1686, -62832, 15113]]]
  g := ![![![-49742, 95319, 18439], ![-464533, 890170, 172199], ![-1936836, 3711498, 717971]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1215, -14, -28]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![1215, -14, -28]] 
 ![![41, 0, 0], ![23, 1, 0], ![11, 0, 1]] where
  M :=![![![1215, -14, -28], ![-28, -3, 0], ![14, -14, -3]]]
  hmulB := by decide  
  f := ![![![-9, -350, 84]], ![![-3, -117, 28]], ![![-13, -504, 121]]]
  g := ![![![45, -14, -28], ![1, -3, 0], ![9, -14, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![3741, -42, -86]] ![![1974, 95319, 18439]]
  ![![-1384, 12411, 2435]] where
 M := ![![![-1384, 12411, 2435]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![-1384, 12411, 2435]] ![![1215, -14, -28]]
  ![![41, 0, 0]] where
 M := ![![![-1994978, -51947, 31447]]]
 hmul := by decide  
 g := ![![![![-48658, -1267, 767]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [17, 10, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 27, 28], [33, 15, 15], [0, 1]]
 g := ![![[12, 1, 1], [12, 36, 35], [39, 6], [34, 1, 1], []], ![[7, 18, 28, 22], [32, 15, 8, 19], [28, 1], [41, 13, 28, 22], [17, 10]], ![[8, 37, 41, 13], [27, 40, 41, 35], [19, 36], [13, 3, 41, 13], [30, 10]]]
 h' := ![![[11, 27, 28], [11, 0, 42], [42, 2, 11], [24, 30, 7], [0, 0, 1], [0, 1]], ![[33, 15, 15], [7, 4, 28], [22, 10, 6], [38, 8, 42], [4, 39, 15], [11, 27, 28]], ![[0, 1], [34, 39, 16], [27, 31, 26], [36, 5, 37], [20, 4, 27], [33, 15, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 18], []]
 b := ![[], [35, 36, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [17, 10, 42, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2322, -26789, 149038]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-54, -623, 3466]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4378, 51, 101]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-4378, 51, 101]] 
 ![![47, 0, 0], ![4, 1, 0], ![37, 0, 1]] where
  M :=![![![-4378, 51, 101], ![101, 16, 1], ![-50, 72, 15]]]
  hmulB := by decide  
  f := ![![![-168, -6507, 1565]], ![![19, 736, -177]], ![![-304, -11775, 2832]]]
  g := ![![![-177, 51, 101], ![0, 16, 1], ![-19, 72, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![104, -57, 11]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![104, -57, 11]] 
 ![![47, 0, 0], ![11, 1, 0], ![28, 0, 1]] where
  M :=![![![104, -57, 11], ![11, 520, -125], ![-68, -2682, 645]]]
  hmulB := by decide  
  f := ![![![-150, -7263, -1405]], ![![-65, -3143, -608]], ![![-214, -10344, -2001]]]
  g := ![![![9, -57, 11], ![-47, 520, -125], ![242, -2682, 645]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -240, -44]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![-5, -240, -44]] 
 ![![47, 0, 0], ![32, 1, 0], ![36, 0, 1]] where
  M :=![![![-5, -240, -44], ![-44, -2137, -436], ![-196, -9396, -1701]]]
  hmulB := by decide  
  f := ![![![-461619, 5184, 10612]], ![![-314068, 3527, 7220]], ![![-353696, 3972, 8131]]]
  g := ![![![197, -240, -44], ![1788, -2137, -436], ![7696, -9396, -1701]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-4378, 51, 101]] ![![104, -57, 11]]
  ![![-461619, 5184, 10612]] where
 M := ![![![-461619, 5184, 10612]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-461619, 5184, 10612]] ![![-5, -240, -44]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [36, 15, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 21, 33], [5, 31, 20], [0, 1]]
 g := ![![[2, 20, 28], [41, 36], [19, 16, 24], [8, 37], [1]], ![[39, 6, 48, 45], [11, 4], [41, 43, 15, 20], [52, 42], [0, 11, 36, 3]], ![[8, 25, 43, 20], [28, 11], [34, 27, 7, 31], [49, 15], [15, 25, 36, 50]]]
 h' := ![![[34, 21, 33], [33, 36, 44], [5, 41, 6], [1, 52, 36], [17, 38, 39], [0, 1]], ![[5, 31, 20], [19, 15, 8], [16, 30, 2], [43, 28, 23], [31, 34, 25], [34, 21, 33]], ![[0, 1], [10, 2, 1], [45, 35, 45], [13, 26, 47], [9, 34, 42], [5, 31, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 14], []]
 b := ![[], [44, 11, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [36, 15, 14, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-205481, 5565, -20299]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3877, 105, -383]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![610, 22829, -5491]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![610, 22829, -5491]] 
 ![![59, 0, 0], ![25, 1, 0], ![29, 0, 1]] where
  M :=![![![610, 22829, -5491], ![-5491, -212674, 51149], ![28320, 1096958, -263823]]]
  hmulB := by decide  
  f := ![![![12040, 581111, 112413]], ![![7007, 338215, 65426]], ![![13862, 669141, 129442]]]
  g := ![![![-6964, 22829, -5491], ![64882, -212674, 51149], ![-334657, 1096958, -263823]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, -155, 37]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-4, -155, 37]] 
 ![![59, 0, 0], ![37, 1, 0], ![5, 0, 1]] where
  M :=![![![-4, -155, 37], ![37, 1432, -347], ![-192, -7442, 1779]]]
  hmulB := by decide  
  f := ![![![-34846, 391, 801]], ![![-21839, 245, 502]], ![![-2960, 33, 68]]]
  g := ![![![94, -155, 37], ![-868, 1432, -347], ![4513, -7442, 1779]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 1, -1]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![0, 1, -1]] 
 ![![59, 0, 0], ![56, 1, 0], ![56, 0, 1]] where
  M :=![![![0, 1, -1], ![-1, -42, 3], ![2, 64, -45]]]
  hmulB := by decide  
  f := ![![![-1698, 19, 39]], ![![-1611, 18, 37]], ![![-1612, 18, 37]]]
  g := ![![![0, 1, -1], ![37, -42, 3], ![-18, 64, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![610, 22829, -5491]] ![![-4, -155, 37]]
  ![![1896505, 73460600, -17667582]] where
 M := ![![![1896505, 73460600, -17667582]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![1896505, 73460600, -17667582]] ![![0, 1, -1]]
  ![![59, 0, 0]] where
 M := ![![![-108795764, -4214173943, 1013526485]]]
 hmul := by decide  
 g := ![![![![-1843996, -71426677, 17178415]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [47, 4, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 52, 10], [48, 8, 51], [0, 1]]
 g := ![![[18, 21, 9], [14, 52], [48], [18, 37, 25], [1]], ![[16, 22, 3, 37], [55, 56], [58, 33, 60, 54], [53, 17, 12, 11], [54, 46, 47, 24]], ![[52, 37, 26, 7], [25, 20], [37, 28, 58, 7], [9, 26, 42, 35], [55, 37, 19, 37]]]
 h' := ![![[8, 52, 10], [14, 50, 58], [1, 55, 28], [8, 32], [14, 57, 56], [0, 1]], ![[48, 8, 51], [51, 5, 49], [47, 57, 42], [20, 17, 15], [48, 42, 42], [8, 52, 10]], ![[0, 1], [42, 6, 15], [34, 10, 52], [19, 12, 46], [37, 23, 24], [48, 8, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 46], []]
 b := ![[], [46, 53, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [47, 4, 5, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1586, -50203, -228201]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![26, -823, -3741]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀


def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45, -1738, 418]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-45, -1738, 418]] 
 ![![67, 0, 0], ![37, 1, 0], ![34, 0, 1]] where
  M :=![![![-45, -1738, 418], ![418, 16191, -3894], ![-2156, -83512, 20085]]]
  hmulB := by decide  
  f := ![![![-507, 286, 66]], ![![-279, 197, 44]], ![![-254, 308, 65]]]
  g := ![![![747, -1738, 418], ![-6959, 16191, -3894], ![35894, -83512, 20085]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 3, -1]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![0, 3, -1]] 
 ![![67, 0, 0], ![60, 1, 0], ![46, 0, 1]] where
  M :=![![![0, 3, -1], ![-1, -40, 7], ![4, 150, -47]]]
  hmulB := by decide  
  f := ![![![-830, 9, 19]], ![![-743, 8, 17]], ![![-570, 6, 13]]]
  g := ![![![-2, 3, -1], ![31, -40, 7], ![-102, 150, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-45, -1738, 418]] ![![-45, -1738, 418]]
  ![![-1625667, -62969764, 15144492]] where
 M := ![![![-1625667, -62969764, 15144492]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI67N1 : IdealMulLeCertificate' Table 
  ![![-1625667, -62969764, 15144492]] ![![0, 3, -1]]
  ![![67, 0, 0]] where
 M := ![![![123547732, 4785587359, -1150953805]]]
 hmul := by decide  
 g := ![![![![1843996, 71426677, -17178415]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-102745, 1154, 2362]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-102745, 1154, 2362]] 
 ![![71, 0, 0], ![0, 71, 0], ![22, 57, 1]] where
  M :=![![![-102745, 1154, 2362], ![2362, -25, -54], ![-1208, 20, 29]]]
  hmulB := by decide  
  f := ![![![5, 194, -46]], ![![-46, -1779, 434]], ![![-32, -1237, 303]]]
  g := ![![![-2179, -1880, 2362], ![50, 43, -54], ![-26, -23, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [70, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 70], [0, 1]]
 g := ![![[63, 45], [48, 3], [52, 9], [38], [64], [1]], ![[58, 26], [24, 68], [51, 62], [38], [64], [1]]]
 h' := ![![[63, 70], [48, 51], [52, 28], [3, 68], [65, 40], [1, 63], [0, 1]], ![[0, 1], [66, 20], [41, 43], [27, 3], [29, 31], [65, 8], [63, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [50, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [70, 8, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![73, 315, 368]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-113, -291, 368]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -194, 46]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-5, -194, 46]] 
 ![![71, 0, 0], ![29, 1, 0], ![62, 0, 1]] where
  M :=![![![-5, -194, 46], ![46, 1779, -434], ![-240, -9308, 2213]]]
  hmulB := by decide  
  f := ![![![102745, -1154, -2362]], ![![41933, -471, -964]], ![![89738, -1008, -2063]]]
  g := ![![![39, -194, 46], ![-347, 1779, -434], ![1866, -9308, 2213]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-102745, 1154, 2362]] ![![-5, -194, 46]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [1, 44, 68, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 38, 48], [32, 34, 25], [0, 1]]
 g := ![![[27, 72, 65], [12, 3], [35, 49], [66, 56, 69], [5, 1], []], ![[50, 26, 26, 71], [21, 8], [44, 38], [2, 27, 4, 50], [23, 61], [57, 41]], ![[50, 42, 70, 6], [31, 71], [71, 55], [21, 56, 33, 8], [72, 57], [7, 41]]]
 h' := ![![[46, 38, 48], [38, 51, 24], [14, 26, 21], [7, 58, 7], [68, 71, 54], [0, 0, 1], [0, 1]], ![[32, 34, 25], [43, 65, 52], [65, 70, 64], [6, 0, 29], [56, 35, 61], [15, 71, 34], [46, 38, 48]], ![[0, 1], [17, 30, 70], [11, 50, 61], [3, 15, 37], [26, 40, 31], [68, 2, 38], [32, 34, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 18], []]
 b := ![[], [10, 18, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [1, 44, 68, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![581518, 35220602, 19410043]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7966, 482474, 265891]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [5, 20, 74, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 54, 29], [1, 24, 50], [0, 1]]
 g := ![![[15, 68, 9], [25, 49, 26], [10, 29, 73], [41, 23, 25], [5, 1], []], ![[73, 69, 54, 68], [28, 9, 65, 29], [76, 73, 29, 35], [68, 42, 63, 37], [41, 23], [69, 51]], ![[8, 75, 18, 32], [4, 16, 12, 20], [15, 0, 18, 31], [46, 0, 5, 55], [13, 72], [48, 51]]]
 h' := ![![[4, 54, 29], [33, 17, 3], [29, 47, 42], [32, 6, 51], [54, 53, 5], [0, 0, 1], [0, 1]], ![[1, 24, 50], [62, 74, 12], [66, 44, 1], [25, 38, 55], [43, 7, 77], [66, 61, 24], [4, 54, 29]], ![[0, 1], [44, 67, 64], [71, 67, 36], [15, 35, 52], [18, 19, 76], [77, 18, 54], [1, 24, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 14], []]
 b := ![[], [62, 40, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [5, 20, 74, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![474, 20856, 5767]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6, 264, 73]
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



lemma PB181I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB181I1 : PrimesBelowBoundCertificateInterval O 31 79 181 where
  m := 11
  g := ![2, 3, 1, 3, 1, 3, 1, 3, 2, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB181I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0]
    · exact ![I67N0, I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
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
    · exact ![1369, 37]
    · exact ![41, 41, 41]
    · exact ![79507]
    · exact ![47, 47, 47]
    · exact ![148877]
    · exact ![59, 59, 59]
    · exact ![226981]
    · exact ![67, 67, 67]
    · exact ![5041, 71]
    · exact ![389017]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I41N0, I41N1, I41N2, I47N0, I47N1, I47N2, I59N0, I59N1, I59N2, I67N0, I67N1, I71N1]
  Il := ![[I37N1], [I41N0, I41N1, I41N2], [], [I47N0, I47N1, I47N2], [], [I59N0, I59N1, I59N2], [], [I67N0, I67N0, I67N1], [I71N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
