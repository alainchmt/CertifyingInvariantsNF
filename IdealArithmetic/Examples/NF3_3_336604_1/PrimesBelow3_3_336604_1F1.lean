
import IdealArithmetic.Examples.NF3_3_336604_1.RI3_3_336604_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33049, 14190, 3513]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-33049, 14190, 3513]] 
 ![![37, 0, 0], ![0, 37, 0], ![4, 9, 1]] where
  M :=![![![-33049, 14190, 3513], ![-266988, 114635, 28380], ![-944946, 405726, 100445]]]
  hmulB := by decide  
  f := ![![![-235, -24, 15]], ![![-1140, 311, -48]], ![![-238, 33, -1]]]
  g := ![![![-1273, -471, 3513], ![-10284, -3805, 28380], ![-36398, -13467, 100445]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [7, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 36], [0, 1]]
 g := ![![[15, 16], [12], [3, 34], [36], [1]], ![[0, 21], [12], [22, 3], [36], [1]]]
 h' := ![![[6, 36], [24, 33], [16, 30], [19, 21], [30, 6], [0, 1]], ![[0, 1], [0, 4], [11, 7], [34, 16], [29, 31], [6, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [10, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [7, 31, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-563, 56, 257]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-43, -61, 257]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-235, -24, 15]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-235, -24, 15]] 
 ![![37, 0, 0], ![19, 1, 0], ![32, 0, 1]] where
  M :=![![![-235, -24, 15], ![-1140, 311, -48], ![2394, -1482, 335]]]
  hmulB := by decide  
  f := ![![![-33049, 14190, 3513]], ![![-24187, 10385, 2571]], ![![-54122, 23238, 5753]]]
  g := ![![![-7, -24, 15], ![-149, 311, -48], ![536, -1482, 335]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-33049, 14190, 3513]] ![![-235, -24, 15]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2491, -142, -47]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![2491, -142, -47]] 
 ![![41, 0, 0], ![0, 41, 0], ![29, 10, 1]] where
  M :=![![![2491, -142, -47], ![3572, 563, -284], ![9006, -3610, 705]]]
  hmulB := by decide  
  f := ![![![15325, -6580, -1629]], ![![123804, -53157, -13160]], ![![51723, -22208, -5498]]]
  g := ![![![94, 8, -47], ![288, 83, -284], ![-279, -260, 705]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [40, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 40], [0, 1]]
 g := ![![[15, 40], [37], [18], [2, 20], [1]], ![[0, 1], [37], [18], [15, 21], [1]]]
 h' := ![![[15, 40], [29, 9], [22, 23], [2, 10], [1, 15], [0, 1]], ![[0, 1], [0, 32], [39, 18], [29, 31], [21, 26], [15, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [16, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [40, 26, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15, -279, 706]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-499, -179, 706]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15325, -6580, -1629]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![15325, -6580, -1629]] 
 ![![41, 0, 0], ![21, 1, 0], ![15, 0, 1]] where
  M :=![![![15325, -6580, -1629], ![123804, -53157, -13160], ![438178, -188138, -46577]]]
  hmulB := by decide  
  f := ![![![2491, -142, -47]], ![![1363, -59, -31]], ![![1131, -140, 0]]]
  g := ![![![4340, -6580, -1629], ![35061, -53157, -13160], ![124091, -188138, -46577]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![2491, -142, -47]] ![![15325, -6580, -1629]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 10, -3]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![5, 10, -3]] 
 ![![43, 0, 0], ![3, 1, 0], ![37, 0, 1]] where
  M :=![![![5, 10, -3], ![228, -99, 20], ![-874, 494, -109]]]
  hmulB := by decide  
  f := ![![![-911, 392, 97]], ![![-235, 101, 25]], ![![-1391, 598, 148]]]
  g := ![![![2, 10, -3], ![-5, -99, 20], ![39, 494, -109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -4, 1]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![7, -4, 1]] 
 ![![43, 0, 0], ![36, 1, 0], ![22, 0, 1]] where
  M :=![![![7, -4, 1], ![-76, 41, -8], ![342, -190, 45]]]
  hmulB := by decide  
  f := ![![![-325, 10, 9]], ![![-288, 9, 8]], ![![-176, 6, 5]]]
  g := ![![![3, -4, 1], ![-32, 41, -8], ![144, -190, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![5, 10, -3]] ![![5, 10, -3]]
  ![![4927, -2422, 512]] where
 M := ![![![4927, -2422, 512]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI43N1 : IdealMulLeCertificate' Table 
  ![![4927, -2422, 512]] ![![7, -4, 1]]
  ![![43, 0, 0]] where
 M := ![![![393665, -216290, 47343]]]
 hmul := by decide  
 g := ![![![![9155, -5030, 1101]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, -12, -3]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![29, -12, -3]] 
 ![![47, 0, 0], ![4, 1, 0], ![37, 0, 1]] where
  M :=![![![29, -12, -3], ![228, -97, -24], ![798, -342, -85]]]
  hmulB := by decide  
  f := ![![![37, 6, -3]], ![![8, -1, 0]], ![![17, 12, -4]]]
  g := ![![![4, -12, -3], ![32, -97, -24], ![113, -342, -85]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, -6, -6]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![223, -6, -6]] 
 ![![47, 0, 0], ![10, 1, 0], ![39, 0, 1]] where
  M :=![![![223, -6, -6], ![456, -11, -12], ![228, 0, -5]]]
  hmulB := by decide  
  f := ![![![-55, 30, -6]], ![![-2, 1, 0]], ![![-99, 54, -11]]]
  g := ![![![11, -6, -6], ![22, -11, -12], ![9, 0, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3349, -1438, -356]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![3349, -1438, -356]] 
 ![![47, 0, 0], ![32, 1, 0], ![36, 0, 1]] where
  M :=![![![3349, -1438, -356], ![27056, -11617, -2876], ![95760, -41116, -10179]]]
  hmulB := by decide  
  f := ![![![-173, -106, 36]], ![![-176, -49, 20]], ![![68, -196, 53]]]
  g := ![![![1323, -1438, -356], ![10688, -11617, -2876], ![37828, -41116, -10179]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![29, -12, -3]] ![![223, -6, -6]]
  ![![311, -42, -15]] where
 M := ![![![311, -42, -15]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![311, -42, -15]] ![![3349, -1438, -356]]
  ![![47, 0, 0]] where
 M := ![![![-1531213, 657436, 162761]]]
 hmul := by decide  
 g := ![![![![-32579, 13988, 3463]]]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [36, 49, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 52, 12], [14, 0, 41], [0, 1]]
 g := ![![[52, 21, 13], [6, 25], [44, 46, 9], [2, 9], [1]], ![[47, 13, 30, 22], [37, 52], [21, 26, 6, 14], [42, 25], [13, 22, 2, 32]], ![[14, 0, 11, 33], [45, 42], [10, 23, 42, 19], [16, 11], [10, 14, 43, 21]]]
 h' := ![![[36, 52, 12], [32, 2, 15], [6, 29, 48], [5, 32, 50], [17, 4, 50], [0, 1]], ![[14, 0, 41], [42, 10, 24], [46, 20, 30], [14, 8, 13], [25, 36, 48], [36, 52, 12]], ![[0, 1], [6, 41, 14], [6, 4, 28], [8, 13, 43], [52, 13, 8], [14, 0, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 46], []]
 b := ![[], [18, 15, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [36, 49, 3, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-264470, 10070, -20617]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4990, 190, -389]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [15, 47, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 23, 25], [8, 35, 34], [0, 1]]
 g := ![![[14, 36, 26], [19, 47, 16], [9, 51], [16, 0, 35], [1]], ![[54, 40, 12, 16], [22, 56, 46, 49], [9, 45], [58, 43, 22, 20], [41, 27, 10, 49]], ![[42, 29, 46, 34], [22, 50, 31, 38], [48, 12], [58, 36, 45, 37], [58, 47, 3, 10]]]
 h' := ![![[26, 23, 25], [10, 55, 47], [58, 19, 4], [55, 4, 13], [44, 12, 34], [0, 1]], ![[8, 35, 34], [53, 46, 11], [31, 37, 25], [44, 31, 24], [28, 3, 15], [26, 23, 25]], ![[0, 1], [8, 17, 1], [23, 3, 30], [25, 24, 22], [55, 44, 10], [8, 35, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 2], []]
 b := ![[], [21, 46, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [15, 47, 25, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-122956, 140656, -152102]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2084, 2384, -2578]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-851, 358, 89]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-851, 358, 89]] 
 ![![61, 0, 0], ![0, 61, 0], ![11, 52, 1]] where
  M :=![![![-851, 358, 89], ![-6764, 2889, 716], ![-23826, 10222, 2531]]]
  hmulB := by decide  
  f := ![![![-113, 60, -13]], ![![988, -547, 120]], ![![739, -410, 90]]]
  g := ![![![-30, -70, 89], ![-240, -563, 716], ![-847, -1990, 2531]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [5, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 60], [0, 1]]
 g := ![![[36, 49], [9], [54, 39], [50, 16], [3, 1]], ![[0, 12], [9], [49, 22], [37, 45], [6, 60]]]
 h' := ![![[3, 60], [21, 54], [35, 3], [55, 51], [46, 4], [0, 1]], ![[0, 1], [0, 7], [44, 58], [25, 10], [58, 57], [3, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [33, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [5, 58, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-565, 2, 176]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-41, -150, 176]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-113, 60, -13]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-113, 60, -13]] 
 ![![61, 0, 0], ![18, 1, 0], ![12, 0, 1]] where
  M :=![![![-113, 60, -13], ![988, -547, 120], ![-5054, 2774, -607]]]
  hmulB := by decide  
  f := ![![![-851, 358, 89]], ![![-362, 153, 38]], ![![-558, 238, 59]]]
  g := ![![![-17, 60, -13], ![154, -547, 120], ![-782, 2774, -607]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-851, 358, 89]] ![![-113, 60, -13]]
  ![![61, 0, 0]] where
 M := ![![![61, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1831, -48, -49]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![1831, -48, -49]] 
 ![![67, 0, 0], ![0, 67, 0], ![31, 42, 1]] where
  M :=![![![1831, -48, -49], ![3724, -79, -96], ![1786, 38, -31]]]
  hmulB := by decide  
  f := ![![![91, -50, 11]], ![![-836, 459, -100]], ![![-419, 230, -50]]]
  g := ![![![50, 30, -49], ![100, 59, -96], ![41, 20, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [63, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 66], [0, 1]]
 g := ![![[41, 62], [30, 33], [65], [37], [29], [1]], ![[25, 5], [15, 34], [65], [37], [29], [1]]]
 h' := ![![[30, 66], [53, 53], [48, 57], [18, 20], [65, 38], [4, 30], [0, 1]], ![[0, 1], [35, 14], [16, 10], [15, 47], [66, 29], [33, 37], [30, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [23, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [63, 37, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-46981, 16342, 18377]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9204, -11276, 18377]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-91, 50, -11]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-91, 50, -11]] 
 ![![67, 0, 0], ![50, 1, 0], ![65, 0, 1]] where
  M :=![![![-91, 50, -11], ![836, -459, 100], ![-4218, 2318, -509]]]
  hmulB := by decide  
  f := ![![![-1831, 48, 49]], ![![-1422, 37, 38]], ![![-1803, 46, 48]]]
  g := ![![![-28, 50, -11], ![258, -459, 100], ![-1299, 2318, -509]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![1831, -48, -49]] ![![-91, 50, -11]]
  ![![67, 0, 0]] where
 M := ![![![-67, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [62, 61, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 50, 66], [33, 20, 5], [0, 1]]
 g := ![![[52, 64, 64], [68, 50, 6], [67, 34, 45], [69, 37], [4, 1], []], ![[55, 29, 10, 39], [6, 20, 17, 47], [41, 49, 33, 68], [2, 10], [69, 45], [26, 25]], ![[49, 54, 64, 60], [20, 57, 59, 36], [14, 29, 70, 27], [38, 5], [18, 15], [16, 25]]]
 h' := ![![[42, 50, 66], [44, 12, 63], [35, 53, 19], [0, 7, 20], [36, 49, 26], [0, 0, 1], [0, 1]], ![[33, 20, 5], [42, 40, 64], [37, 4, 44], [68, 46, 10], [11, 10, 62], [10, 70, 20], [42, 50, 66]], ![[0, 1], [19, 19, 15], [6, 14, 8], [41, 18, 41], [57, 12, 54], [26, 1, 50], [33, 20, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 32], []]
 b := ![[], [25, 3, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [62, 61, 67, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31169, 13348, 4828]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-439, 188, 68]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![75, -2, -2]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![75, -2, -2]] 
 ![![73, 0, 0], ![2, 1, 0], ![70, 0, 1]] where
  M :=![![![75, -2, -2], ![152, -3, -4], ![76, 0, -1]]]
  hmulB := by decide  
  f := ![![![3, -2, 2]], ![![-2, 1, 0]], ![![6, -4, 3]]]
  g := ![![![3, -2, -2], ![6, -3, -4], ![2, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1483, -42, -40]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![1483, -42, -40]] 
 ![![73, 0, 0], ![7, 1, 0], ![45, 0, 1]] where
  M :=![![![1483, -42, -40], ![3040, -79, -84], ![1672, -76, -37]]]
  hmulB := by decide  
  f := ![![![-3461, 1486, 368]], ![![-715, 307, 76]], ![![-3489, 1498, 371]]]
  g := ![![![49, -42, -40], ![101, -79, -84], ![53, -76, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-147, 4, 4]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![-147, 4, 4]] 
 ![![73, 0, 0], ![63, 1, 0], ![28, 0, 1]] where
  M :=![![![-147, 4, 4], ![-304, 9, 8], ![-152, 0, 5]]]
  hmulB := by decide  
  f := ![![![45, -20, -4]], ![![43, -19, -4]], ![![36, -16, -3]]]
  g := ![![![-7, 4, 4], ![-15, 9, 8], ![-4, 0, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![75, -2, -2]] ![![1483, -42, -40]]
  ![![101801, -2840, -2758]] where
 M := ![![![101801, -2840, -2758]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![101801, -2840, -2758]] ![![-147, 4, 4]]
  ![![73, 0, 0]] where
 M := ![![![-13682171, 381644, 370694]]]
 hmul := by decide  
 g := ![![![![-187427, 5228, 5078]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [68, 62, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 46, 8], [72, 32, 71], [0, 1]]
 g := ![![[57, 29, 42], [25, 6, 44], [24, 55, 21], [57, 77, 9], [67, 1], []], ![[49, 25], [19, 7, 19, 22], [12, 40, 24, 55], [37, 55, 29, 36], [33, 76], [47, 64]], ![[29, 68, 11, 59], [12, 16, 78, 39], [76, 78, 65, 29], [23, 20, 73, 34], [75, 62], [63, 64]]]
 h' := ![![[74, 46, 8], [38, 35, 11], [27, 11, 53], [74, 43, 10], [26, 44, 3], [0, 0, 1], [0, 1]], ![[72, 32, 71], [58, 48], [21, 11, 46], [65, 5, 32], [10, 18, 53], [68, 16, 32], [74, 46, 8]], ![[0, 1], [55, 75, 68], [13, 57, 59], [4, 31, 37], [48, 17, 23], [31, 63, 46], [72, 32, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 71], []]
 b := ![[], [69, 13, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [68, 62, 12, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-128296, -36577, 190390]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1624, -463, 2410]
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



lemma PB129I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB129I1 : PrimesBelowBoundCertificateInterval O 31 79 129 where
  m := 11
  g := ![2, 2, 3, 3, 1, 1, 2, 2, 1, 3, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB129I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0, I73N1, I73N2]
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
    · exact ![1681, 41]
    · exact ![43, 43, 43]
    · exact ![47, 47, 47]
    · exact ![148877]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![357911]
    · exact ![73, 73, 73]
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
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N0
      exact NI43N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I41N1, I43N0, I43N1, I47N0, I47N1, I47N2, I61N1, I67N1, I73N0, I73N1, I73N2]
  Il := ![[I37N1], [I41N1], [I43N0, I43N0, I43N1], [I47N0, I47N1, I47N2], [], [], [I61N1], [I67N1], [], [I73N0, I73N1, I73N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
