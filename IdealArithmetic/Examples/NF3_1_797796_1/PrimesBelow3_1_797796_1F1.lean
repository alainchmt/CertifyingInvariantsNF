
import IdealArithmetic.Examples.NF3_1_797796_1.RI3_1_797796_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1681, 372, 42]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![1681, 372, 42]] 
 ![![37, 0, 0], ![0, 37, 0], ![18, 30, 1]] where
  M :=![![![1681, 372, 42], ![29820, 6595, 744], ![264120, 58434, 6595]]]
  hmulB := by decide  
  f := ![![![517, 24, -6]], ![![-4260, -185, 48]], ![![-2742, -120, 31]]]
  g := ![![![25, -24, 42], ![444, -425, 744], ![3930, -3768, 6595]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [20, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 36], [0, 1]]
 g := ![![[26, 11], [1], [7, 4], [4], [1]], ![[4, 26], [1], [36, 33], [4], [1]]]
 h' := ![![[35, 36], [7, 14], [8, 1], [24, 35], [17, 35], [0, 1]], ![[0, 1], [16, 23], [6, 36], [28, 2], [21, 2], [35, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [1, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [20, 2, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1440, 587, 117]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, -79, 117]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-517, -24, 6]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-517, -24, 6]] 
 ![![37, 0, 0], ![14, 1, 0], ![13, 0, 1]] where
  M :=![![![-517, -24, 6], ![4260, 185, -48], ![-17040, -678, 185]]]
  hmulB := by decide  
  f := ![![![-1681, -372, -42]], ![![-1442, -319, -36]], ![![-7729, -1710, -193]]]
  g := ![![![-7, -24, 6], ![62, 185, -48], ![-269, -678, 185]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![1681, 372, 42]] ![![-517, -24, 6]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [35, 25, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 5, 12], [12, 35, 29], [0, 1]]
 g := ![![[12, 25, 25], [23, 40], [0, 16], [20, 2, 1], []], ![[24, 30, 1, 27], [25, 18], [17, 18], [1, 5, 22, 22], [39, 21]], ![[4, 37, 33, 26], [25, 1], [32, 32], [12, 17, 6, 28], [22, 21]]]
 h' := ![![[31, 5, 12], [14, 18, 5], [9, 31, 9], [38, 4, 37], [0, 0, 1], [0, 1]], ![[12, 35, 29], [28, 19, 22], [40, 19, 31], [15, 3, 31], [6, 35, 35], [31, 5, 12]], ![[0, 1], [11, 4, 14], [36, 32, 1], [7, 34, 14], [30, 6, 5], [12, 35, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 1], []]
 b := ![[], [35, 25, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [35, 25, 39, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2001538, 1591948, 377733]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![48818, 38828, 9213]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![153, 9, -2]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![153, 9, -2]] 
 ![![43, 0, 0], ![0, 43, 0], ![31, 17, 1]] where
  M :=![![![153, 9, -2], ![-1420, -81, 18], ![6390, 343, -81]]]
  hmulB := by decide  
  f := ![![![-9, -1, 0]], ![![0, -9, -2]], ![![-23, -7, -1]]]
  g := ![![![5, 1, -2], ![-46, -9, 18], ![207, 40, -81]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [7, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 42], [0, 1]]
 g := ![![[17, 6], [0, 41], [36], [0, 14], [1]], ![[34, 37], [23, 2], [36], [11, 29], [1]]]
 h' := ![![[10, 42], [0, 7], [6, 16], [0, 37], [36, 10], [0, 1]], ![[0, 1], [27, 36], [37, 27], [26, 6], [7, 33], [10, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [30, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [7, 33, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![571, 26, 214]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-141, -84, 214]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![9, 1, 0]] 
 ![![43, 0, 0], ![9, 1, 0], ![24, 0, 1]] where
  M :=![![![9, 1, 0], ![0, 9, 2], ![710, 117, 9]]]
  hmulB := by decide  
  f := ![![![-153, -9, 2]], ![![1, 0, 0]], ![![-234, -13, 3]]]
  g := ![![![0, 1, 0], ![-3, 9, 2], ![-13, 117, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![153, 9, -2]] ![![9, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-68, 1, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-68, 1, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![26, 1, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-68, 1, 1], ![710, 49, 2], ![710, 472, 49]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -1, 47]], ![![-2, 0, 1], ![14, 1, 2], ![-12, 9, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [2, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 46], [0, 1]]
 g := ![![[19, 24], [4, 42], [17, 21], [35, 34], [1]], ![[0, 23], [6, 5], [18, 26], [12, 13], [1]]]
 h' := ![![[9, 46], [39, 27], [13, 29], [24, 16], [45, 9], [0, 1]], ![[0, 1], [0, 20], [39, 18], [27, 31], [32, 38], [9, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [13, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [2, 38, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4219, 2533, 935]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-607, 34, 935]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-2, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-2, 1, 0]] 
 ![![47, 0, 0], ![45, 1, 0], ![45, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-2, 1, 0], ![0, -2, 2], ![710, 117, -2]]]
  hmulB := by decide  
  f := ![![![53, -26, 0], ![1222, 0, 0]], ![![51, -25, 0], ![1176, 0, 0]], ![![51, -24, -1], ![1176, 24, 0]]]
  g := ![![![1, 0, 0], ![-45, 47, 0], ![-45, 0, 47]], ![![-1, 1, 0], ![0, -2, 2], ![-95, 117, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-68, 1, 1]] ![![47, 0, 0], ![-2, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-94, 47, 0]], ![![-3196, 47, 47], ![846, 47, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-2, 1, 0]]], ![![![-68, 1, 1]], ![![18, 1, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [5, 36, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 1, 5], [11, 51, 48], [0, 1]]
 g := ![![[49, 36, 38], [41, 40], [38, 19, 37], [52, 7], [1]], ![[19, 12, 42, 3], [3, 49], [43, 36, 22, 51], [12, 52], [15, 3, 28, 19]], ![[45, 28, 52, 20], [49, 29], [46, 36, 33, 31], [30, 1], [52, 5, 3, 34]]]
 h' := ![![[20, 1, 5], [14, 52, 41], [22, 20, 27], [30, 43, 14], [48, 17, 31], [0, 1]], ![[11, 51, 48], [0, 38, 19], [11, 25, 46], [35, 24, 28], [28, 9, 23], [20, 1, 5]], ![[0, 1], [35, 16, 46], [11, 8, 33], [24, 39, 11], [11, 27, 52], [11, 51, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 28], []]
 b := ![[], [18, 12, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [5, 36, 22, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-471435, -113579, -13939]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8895, -2143, -263]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-86, 24, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-86, 24, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![32, 24, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-86, 24, 1], ![710, 31, 48], ![17040, 3163, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -24, 59]], ![![-2, 0, 1], ![-14, -19, 48], ![272, 41, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [18, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 58], [0, 1]]
 g := ![![[36, 3], [5, 16], [45], [16, 53], [1, 1]], ![[39, 56], [21, 43], [45], [10, 6], [2, 58]]]
 h' := ![![[1, 58], [28, 48], [6, 4], [7, 35], [41, 42], [0, 1]], ![[0, 1], [17, 11], [10, 55], [42, 24], [24, 17], [1, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [54, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [18, 58, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27057, 5941, 899]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-29, -265, 899]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![11, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![11, 1, 0]] 
 ![![59, 0, 0], ![11, 1, 0], ![28, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![11, 1, 0], ![0, 11, 2], ![710, 117, 11]]]
  hmulB := by decide  
  f := ![![![342, 31, 0], ![-1829, 0, 0]], ![![44, 4, 0], ![-235, 0, 0]], ![![150, 8, -1], ![-802, 30, 0]]]
  g := ![![![1, 0, 0], ![-11, 59, 0], ![-28, 0, 59]], ![![0, 1, 0], ![-3, 11, 2], ![-15, 117, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-86, 24, 1]] ![![59, 0, 0], ![11, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![649, 59, 0]], ![![-5074, 1416, 59], ![-236, 295, 59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![11, 1, 0]]], ![![![-86, 24, 1]], ![![-4, 5, 1]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-80, 7, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-80, 7, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![42, 7, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-80, 7, 1], ![710, 37, 14], ![4970, 1174, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -7, 61]], ![![-2, 0, 1], ![2, -1, 14], ![56, 15, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [10, 58, 1] where
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
 g := ![![[18, 47], [1], [13, 56], [2, 1], [3, 1]], ![[37, 14], [1], [59, 5], [5, 60], [6, 60]]]
 h' := ![![[3, 60], [54, 48], [53, 1], [41, 42], [31, 60], [0, 1]], ![[0, 1], [15, 13], [56, 60], [45, 19], [28, 1], [3, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [55, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [10, 58, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4307, -179, 79]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-125, -12, 79]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-14, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-14, 1, 0]] 
 ![![61, 0, 0], ![47, 1, 0], ![24, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-14, 1, 0], ![0, -14, 2], ![710, 117, -14]]]
  hmulB := by decide  
  f := ![![![757, -54, 0], ![3294, 0, 0]], ![![575, -41, 0], ![2502, 0, 0]], ![![296, -14, -1], ![1288, 31, 0]]]
  g := ![![![1, 0, 0], ![-47, 61, 0], ![-24, 0, 61]], ![![-1, 1, 0], ![10, -14, 2], ![-73, 117, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-80, 7, 1]] ![![61, 0, 0], ![-14, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-854, 61, 0]], ![![-4880, 427, 61], ![1830, -61, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-14, 1, 0]]], ![![![-80, 7, 1]], ![![30, -1, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [46, 12, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 35, 2], [17, 31, 65], [0, 1]]
 g := ![![[47, 44, 54], [9, 38, 40], [6, 64], [24, 54], [66, 1], []], ![[22, 64, 4, 11], [9, 51, 24, 51], [13, 47], [48, 49], [14, 23], [2, 4]], ![[30, 31, 30, 29], [30, 52, 35, 24], [23, 65], [20, 56], [30, 19], [6, 4]]]
 h' := ![![[49, 35, 2], [55, 26, 56], [41, 10, 24], [7, 63, 8], [46, 33, 56], [0, 0, 1], [0, 1]], ![[17, 31, 65], [50, 40, 46], [2, 25, 27], [59, 42, 39], [49, 17, 60], [31, 6, 31], [49, 35, 2]], ![[0, 1], [19, 1, 32], [54, 32, 16], [43, 29, 20], [62, 17, 18], [13, 61, 35], [17, 31, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 21], []]
 b := ![[], [24, 14, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [46, 12, 1, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3017546, 835222, 119930]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![45038, 12466, 1790]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![0, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![0, 1, 0]] 
 ![![71, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![0, 1, 0], ![0, 0, 2], ![710, 117, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![0, 36, 0]]]
  g := ![![![1, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![0, 1, 0], ![0, 0, 2], ![10, 117, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-46, 0, 1]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-46, 0, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![25, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-46, 0, 1], ![710, 71, 0], ![0, 355, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, 0, 71]], ![![-1, 0, 1], ![10, 1, 0], ![-25, 5, 71]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P1 : CertificateIrreducibleZModOfList' 71 2 2 6 [62, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 70], [0, 1]]
 g := ![![[13, 18], [12, 32], [27, 37], [60], [57], [1]], ![[60, 53], [64, 39], [25, 34], [60], [57], [1]]]
 h' := ![![[46, 70], [37, 36], [30, 23], [9, 45], [26, 42], [9, 46], [0, 1]], ![[0, 1], [60, 35], [23, 48], [20, 26], [41, 29], [66, 25], [46, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [15, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N1 : CertifiedPrimeIdeal' SI71N1 71 where
  n := 2
  hpos := by decide
  P := [62, 25, 1]
  hirr := P71P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-28284, -3550, 726]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-654, -50, 726]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N1 B_one_repr
lemma NI71N1 : Nat.card (O ⧸ I71N1) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![0, 1, 0]] ![![71, 0, 0], ![-46, 0, 1]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-3266, 0, 71]], ![![0, 71, 0], ![710, 71, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-46, 0, 1]]], ![![![0, 1, 0]], ![![10, 1, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-79, 26, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-79, 26, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![67, 26, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-79, 26, 1], ![710, 38, 52], ![18460, 3397, 38]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-67, -26, 73]], ![![-2, 0, 1], ![-38, -18, 52], ![218, 33, 38]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [39, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 72], [0, 1]]
 g := ![![[51, 55], [46], [69], [64, 41], [32], [1]], ![[10, 18], [46], [69], [56, 32], [32], [1]]]
 h' := ![![[55, 72], [54, 36], [60, 51], [59, 19], [54, 25], [34, 55], [0, 1]], ![[0, 1], [63, 37], [18, 22], [9, 54], [42, 48], [66, 18], [55, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [39, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [39, 18, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-978, 77, 163]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-163, -57, 163]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![21, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![21, 1, 0]] 
 ![![73, 0, 0], ![21, 1, 0], ![35, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![21, 1, 0], ![0, 21, 2], ![710, 117, 21]]]
  hmulB := by decide  
  f := ![![![106, 5, 0], ![-365, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![56, -8, -1], ![-193, 37, 0]]]
  g := ![![![1, 0, 0], ![-21, 73, 0], ![-35, 0, 73]], ![![0, 1, 0], ![-7, 21, 2], ![-34, 117, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-79, 26, 1]] ![![73, 0, 0], ![21, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![1533, 73, 0]], ![![-5767, 1898, 73], ![-949, 584, 73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![21, 1, 0]]], ![![![-79, 26, 1]], ![![-13, 8, 1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![20, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![20, 1, 0]] 
 ![![79, 0, 0], ![20, 1, 0], ![37, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![20, 1, 0], ![0, 20, 2], ![710, 117, 20]]]
  hmulB := by decide  
  f := ![![![41, 2, 0], ![-158, 0, 0]], ![![-20, -1, 0], ![80, 0, 0]], ![![3, -10, -1], ![-10, 40, 0]]]
  g := ![![![1, 0, 0], ![-20, 79, 0], ![-37, 0, 79]], ![![0, 1, 0], ![-6, 20, 2], ![-30, 117, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![21, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![21, 1, 0]] 
 ![![79, 0, 0], ![21, 1, 0], ![56, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![21, 1, 0], ![0, 21, 2], ![710, 117, 21]]]
  hmulB := by decide  
  f := ![![![799, 38, 0], ![-3002, 0, 0]], ![![189, 9, 0], ![-710, 0, 0]], ![![560, 16, -1], ![-2104, 40, 0]]]
  g := ![![![1, 0, 0], ![-21, 79, 0], ![-56, 0, 79]], ![![0, 1, 0], ![-7, 21, 2], ![-37, 117, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![38, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![79, 0, 0], ![38, 1, 0]] 
 ![![79, 0, 0], ![38, 1, 0], ![68, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![38, 1, 0], ![0, 38, 2], ![710, 117, 38]]]
  hmulB := by decide  
  f := ![![![913, 24, 0], ![-1896, 0, 0]], ![![418, 11, 0], ![-868, 0, 0]], ![![808, 2, -1], ![-1678, 40, 0]]]
  g := ![![![1, 0, 0], ![-38, 79, 0], ![-68, 0, 79]], ![![0, 1, 0], ![-20, 38, 2], ![-80, 117, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![20, 1, 0]] ![![79, 0, 0], ![21, 1, 0]]
  ![![79, 0, 0], ![-106, -19, 1]] where
 M := ![![![6241, 0, 0], ![1659, 79, 0]], ![![1580, 79, 0], ![420, 41, 2]]]
 hmul := by decide  
 g := ![![![![79, 0, 0], ![0, 0, 0]], ![![21, 1, 0], ![0, 0, 0]]], ![![![20, 1, 0], ![0, 0, 0]], ![![8, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-106, -19, 1]] ![![79, 0, 0], ![38, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![3002, 79, 0]], ![![-8374, -1501, 79], ![-3318, -711, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![38, 1, 0]]], ![![![-106, -19, 1]], ![![-42, -9, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB253I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB253I1 : PrimesBelowBoundCertificateInterval O 31 79 253 where
  m := 11
  g := ![2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB253I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
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
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![71, 5041]
    · exact ![5329, 73]
    · exact ![79, 79, 79]
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
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
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
      exact NI79N1
      exact NI79N2
  β := ![I37N1, I43N1, I47N1, I59N1, I61N1, I71N0, I73N1, I79N0, I79N1, I79N2]
  Il := ![[I37N1], [], [I43N1], [I47N1], [], [I59N1], [I61N1], [], [I71N0], [I73N1], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
