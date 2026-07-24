
import IdealArithmetic.Examples.NF3_1_866700_5.RI3_1_866700_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![18, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![18, 1, 0]] 
 ![![37, 0, 0], ![18, 1, 0], ![9, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![18, 1, 0], ![-6, 24, 13], ![182, 0, 12]]]
  hmulB := by decide  
  f := ![![![523, -2526, -1365], ![222, 3885, 0]], ![![252, -1227, -663], ![112, 1887, 0]], ![![117, -615, -332], ![75, 945, 0]]]
  g := ![![![1, 0, 0], ![-18, 37, 0], ![-9, 0, 37]], ![![0, 1, 0], ![-15, 24, 13], ![2, 0, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-12, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-12, 1, 0]] 
 ![![37, 0, 0], ![25, 1, 0], ![31, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-12, 1, 0], ![-6, -6, 13], ![182, 0, -18]]]
  hmulB := by decide  
  f := ![![![-551, -617, 1326], ![185, -3774, 0]], ![![-371, -411, 884], ![112, -2516, 0]], ![![-461, -517, 1111], ![157, -3162, 0]]]
  g := ![![![1, 0, 0], ![-25, 37, 0], ![-31, 0, 37]], ![![-1, 1, 0], ![-7, -6, 13], ![20, 0, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 0, -1]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![9, 0, -1]] 
 ![![37, 0, 0], ![31, 1, 0], ![28, 0, 1]] where
  M :=![![![9, 0, -1], ![-182, 9, 6], ![168, -14, 3]]]
  hmulB := by decide  
  f := ![![![-111, -14, -9]], ![![-135, -17, -11]], ![![-112, -14, -9]]]
  g := ![![![1, 0, -1], ![-17, 9, 6], ![14, -14, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![18, 1, 0]] ![![37, 0, 0], ![-12, 1, 0]]
  ![![-111, -14, -9]] where
 M := ![![![1369, 0, 0], ![-444, 37, 0]], ![![666, 37, 0], ![-222, 12, 13]]]
 hmul := by decide  
 g := ![![![![333, 0, -37]], ![![-290, 9, 18]]], ![![![-20, 9, -12]], ![![-54, -2, 9]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-111, -14, -9]] ![![9, 0, -1]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [6, 30, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 5, 20], [8, 35, 21], [0, 1]]
 g := ![![[25, 11, 1], [40, 5], [12, 20], [3, 22, 1], []], ![[25, 8, 18, 37], [33, 21], [10, 31], [26, 33, 33, 23], [21, 31]], ![[3, 34, 19, 32], [9, 1], [19, 25], [1, 10, 20, 33], [20, 31]]]
 h' := ![![[14, 5, 20], [1, 26, 40], [6, 9, 28], [23, 24, 15], [0, 0, 1], [0, 1]], ![[8, 35, 21], [8, 27, 34], [1, 18, 12], [15, 25, 21], [29, 21, 35], [14, 5, 20]], ![[0, 1], [19, 29, 8], [27, 14, 1], [31, 33, 5], [26, 20, 5], [8, 35, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 11], []]
 b := ![[], [23, 36, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [6, 30, 19, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5507858, -148666, -96473]
  a := ![6, -7, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-134338, -3626, -2353]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![5, -17, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![5, -17, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![5, 26, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![5, -17, 1], ![284, -97, -227], ![-3262, 14, 113]]]
  hmulB := by decide  
  f := ![![![-4, 17, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -26, 43]], ![![0, -1, 1], ![33, 135, -227], ![-89, -68, 113]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [16, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 42], [0, 1]]
 g := ![![[4, 35], [42, 15], [11], [11, 11], [1]], ![[0, 8], [28, 28], [11], [38, 32], [1]]]
 h' := ![![[22, 42], [16, 11], [12, 31], [39, 21], [27, 22], [0, 1]], ![[0, 1], [0, 32], [6, 12], [28, 22], [38, 21], [22, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [15, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [16, 21, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30480, 11526, 2504]
  a := ![-13, 10, 28]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1000, -1246, 2504]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![12, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![12, 1, 0]] 
 ![![43, 0, 0], ![12, 1, 0], ![16, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![12, 1, 0], ![-6, 18, 13], ![182, 0, 6]]]
  hmulB := by decide  
  f := ![![![2953, -9411, -6786], ![645, 22446, 0]], ![![822, -2614, -1885], ![173, 6235, 0]], ![![1096, -3502, -2525], ![250, 8352, 0]]]
  g := ![![![1, 0, 0], ![-12, 43, 0], ![-16, 0, 43]], ![![0, 1, 0], ![-10, 18, 13], ![2, 0, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![5, -17, 1]] ![![43, 0, 0], ![12, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![516, 43, 0]], ![![215, -731, 43], ![344, -301, -215]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![12, 1, 0]]], ![![![5, -17, 1]], ![![8, -7, -5]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [44, 10, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 29, 5], [38, 17, 42], [0, 1]]
 g := ![![[23, 6, 25], [19, 46, 16], [28, 35, 28], [18, 13, 1], []], ![[6, 14, 28, 33], [31, 40, 28, 20], [3, 2, 29, 40], [30, 25, 43, 35], [4, 25]], ![[28, 37, 43, 42], [18, 20, 14, 8], [10, 31, 7, 42], [19, 12, 12, 25], [14, 25]]]
 h' := ![![[22, 29, 5], [10, 1, 5], [37, 15, 4], [7, 0, 13], [0, 0, 1], [0, 1]], ![[38, 17, 42], [21, 4, 43], [1, 39, 2], [16, 29, 33], [26, 42, 17], [22, 29, 5]], ![[0, 1], [5, 42, 46], [18, 40, 41], [8, 18, 1], [29, 5, 29], [38, 17, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 37], []]
 b := ![[], [5, 37, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [44, 10, 34, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-939645608250, -33503016862, -18210506636]
  a := ![326, -389, -717]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19992459750, -712830146, -387457588]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [49, 31, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 21, 45], [27, 31, 8], [0, 1]]
 g := ![![[14, 8, 7], [48, 9], [35, 22, 52], [18, 52], [1]], ![[0, 40, 47, 31], [3, 6], [16, 25, 32, 2], [50, 38], [44, 30, 14, 18]], ![[51, 26, 34, 48], [48, 17], [15, 15, 3, 35], [20, 15], [23, 48, 6, 35]]]
 h' := ![![[3, 21, 45], [23, 7, 31], [34, 16, 3], [35, 38, 23], [4, 22, 30], [0, 1]], ![[27, 31, 8], [3, 0, 4], [37, 26, 18], [16, 29, 38], [44, 12, 12], [3, 21, 45]], ![[0, 1], [49, 46, 18], [4, 11, 32], [10, 39, 45], [6, 19, 11], [27, 31, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 2], []]
 b := ![[], [46, 9, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [49, 31, 23, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-53140874, -847470, 726630]
  a := ![13, -11, -28]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1002658, -15990, 13710]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![20, 14, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![20, 14, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![20, 14, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![20, 14, 1], ![98, 104, 176], ![2380, 14, -58]]]
  hmulB := by decide  
  f := ![![![-19, -14, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -14, 59]], ![![0, 0, 1], ![-58, -40, 176], ![60, 14, -58]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [16, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 58], [0, 1]]
 g := ![![[48, 48], [12, 12], [20], [3, 48], [58, 1]], ![[0, 11], [0, 47], [20], [14, 11], [57, 58]]]
 h' := ![![[58, 58], [44, 44], [37, 37], [11, 16], [16, 44], [0, 1]], ![[0, 1], [0, 15], [0, 22], [54, 43], [31, 15], [58, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [15, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [16, 1, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4496, 2569, 390]
  a := ![6, -7, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-56, -49, 390]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![1, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![1, 1, 0]] 
 ![![59, 0, 0], ![1, 1, 0], ![58, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![1, 1, 0], ![-6, 7, 13], ![182, 0, -5]]]
  hmulB := by decide  
  f := ![![![-300, 349, 650], ![59, -2950, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-294, 344, 639], ![4, -2900, 0]]]
  g := ![![![1, 0, 0], ![-1, 59, 0], ![-58, 0, 59]], ![![0, 1, 0], ![-13, 7, 13], ![8, 0, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![20, 14, 1]] ![![59, 0, 0], ![1, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![59, 59, 0]], ![![1180, 826, 59], ![118, 118, 177]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![1, 1, 0]]], ![![![20, 14, 1]], ![![2, 2, 3]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [40, 37, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 0, 60], [38, 60, 1], [0, 1]]
 g := ![![[18, 21, 20], [48, 13], [1, 9, 1], [43, 32, 60], [1]], ![[29, 33, 43, 5], [3, 41], [11, 47, 11, 1], [38, 44, 48, 14], [39, 13, 11, 60]], ![[46, 48, 6, 39], [37, 20], [20, 54, 44, 39], [33, 42, 28, 27], [54, 51, 47, 1]]]
 h' := ![![[12, 0, 60], [46, 10, 9], [21, 52, 47], [49, 10, 1], [21, 24, 50], [0, 1]], ![[38, 60, 1], [54, 9, 42], [33, 47, 23], [21, 1, 50], [46, 50, 48], [12, 0, 60]], ![[0, 1], [46, 42, 10], [60, 23, 52], [14, 50, 10], [8, 48, 24], [38, 60, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 51], []]
 b := ![[], [36, 28, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [40, 37, 11, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![65438299, 9848816, 7175186]
  a := ![-11, 31, 24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1072759, 161456, 117626]
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

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![13, -10, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![13, -10, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![13, 57, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![13, -10, 1], ![242, -47, -136], ![-1988, 14, 79]]]
  hmulB := by decide  
  f := ![![![-12, 10, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -57, 67]], ![![0, -1, 1], ![30, 115, -136], ![-45, -67, 79]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [17, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 66], [0, 1]]
 g := ![![[11, 4], [22, 29], [21], [33], [62], [1]], ![[0, 63], [26, 38], [21], [33], [62], [1]]]
 h' := ![![[14, 66], [28, 65], [60, 37], [22, 17], [39, 57], [50, 14], [0, 1]], ![[0, 1], [0, 2], [42, 30], [59, 50], [33, 10], [45, 53], [14, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [20, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [17, 53, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17909, 7875, 117]
  a := ![11, -9, -24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-290, 18, 117]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![2, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![2, 1, 0]] 
 ![![67, 0, 0], ![2, 1, 0], ![55, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![2, 1, 0], ![-6, 8, 13], ![182, 0, -4]]]
  hmulB := by decide  
  f := ![![![1223, -1633, -2652], ![67, 13668, 0]], ![![36, -48, -78], ![1, 402, 0]], ![![1005, -1340, -2177], ![20, 11220, 0]]]
  g := ![![![1, 0, 0], ![-2, 67, 0], ![-55, 0, 67]], ![![0, 1, 0], ![-11, 8, 13], ![6, 0, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![13, -10, 1]] ![![67, 0, 0], ![2, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![134, 67, 0]], ![![871, -670, 67], ![268, -67, -134]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![2, 1, 0]]], ![![![13, -10, 1]], ![![4, -1, -2]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![293, -30, 14]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![293, -30, 14]] 
 ![![71, 0, 0], ![0, 71, 0], ![26, 8, 1]] where
  M :=![![![293, -30, 14], ![2728, 113, -474], ![-7812, 196, 557]]]
  hmulB := by decide  
  f := ![![![2195, 274, 178]], ![![30752, 3839, 2494]], ![![4550, 568, 369]]]
  g := ![![![-1, -2, 14], ![212, 55, -474], ![-314, -60, 557]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [2, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 70], [0, 1]]
 g := ![![[8, 36], [48, 3], [60, 57], [12], [43], [1]], ![[0, 35], [0, 68], [0, 14], [12], [43], [1]]]
 h' := ![![[55, 70], [46, 65], [22, 28], [26, 46], [60, 15], [69, 55], [0, 1]], ![[0, 1], [0, 6], [0, 43], [0, 25], [33, 56], [41, 16], [55, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [32, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [2, 16, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8404, 10374, 1989]
  a := ![-12, 13, 26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-610, -78, 1989]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2195, -274, -178]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-2195, -274, -178]] 
 ![![71, 0, 0], ![44, 1, 0], ![16, 0, 1]] where
  M :=![![![-2195, -274, -178], ![-30752, -3839, -2494], ![-19964, -2492, -1619]]]
  hmulB := by decide  
  f := ![![![-293, 30, -14]], ![![-220, 17, -2]], ![![44, 4, -11]]]
  g := ![![![179, -274, -178], ![2508, -3839, -2494], ![1628, -2492, -1619]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![293, -30, 14]] ![![-2195, -274, -178]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![249, 31, 20]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![249, 31, 20]] 
 ![![73, 0, 0], ![0, 73, 0], ![38, 49, 1]] where
  M :=![![![249, 31, 20], ![3454, 435, 283], ![2282, 280, 183]]]
  hmulB := by decide  
  f := ![![![5, -1, 1]], ![![188, -1, -19]], ![![124, -1, -12]]]
  g := ![![![-7, -13, 20], ![-100, -184, 283], ![-64, -119, 183]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [30, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 72], [0, 1]]
 g := ![![[7, 69], [72], [46], [36, 24], [8], [1]], ![[44, 4], [72], [46], [33, 49], [8], [1]]]
 h' := ![![[9, 72], [53, 19], [13, 46], [15, 51], [3, 43], [43, 9], [0, 1]], ![[0, 1], [5, 54], [62, 27], [36, 22], [25, 30], [51, 64], [9, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [11, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [30, 64, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![89255, 44330, 3780]
  a := ![25, -30, -55]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-745, -1930, 3780]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 1, -1]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-5, 1, -1]] 
 ![![73, 0, 0], ![26, 1, 0], ![31, 0, 1]] where
  M :=![![![-5, 1, -1], ![-188, 1, 19], ![350, -14, -17]]]
  hmulB := by decide  
  f := ![![![-249, -31, -20]], ![![-136, -17, -11]], ![![-137, -17, -11]]]
  g := ![![![0, 1, -1], ![-11, 1, 19], ![17, -14, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![249, 31, 20]] ![![-5, 1, -1]]
  ![![73, 0, 0]] where
 M := ![![![-73, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [35, 62, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 46, 36], [24, 32, 43], [0, 1]]
 g := ![![[44, 71, 26], [66, 6, 38], [50, 38, 44], [18, 43, 25], [64, 1], []], ![[26, 31, 12, 51], [78, 52, 59, 40], [52, 67, 62, 20], [28, 54, 32, 45], [18, 76], [67, 32]], ![[62, 58, 6, 39], [0, 72, 39, 48], [57, 48, 7, 57], [35, 75, 50, 48], [42, 62], [60, 32]]]
 h' := ![![[40, 46, 36], [60, 29, 42], [67, 77, 14], [2, 59, 26], [51, 26, 5], [0, 0, 1], [0, 1]], ![[24, 32, 43], [29, 35, 18], [64, 28, 60], [56, 59, 33], [52, 20, 69], [45, 65, 32], [40, 46, 36]], ![[0, 1], [27, 15, 19], [13, 53, 5], [30, 40, 20], [7, 33, 5], [56, 14, 46], [24, 32, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 11], []]
 b := ![[], [65, 17, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [35, 62, 15, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![250747659, 4687228, -9126396]
  a := ![-22, 14, 48]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3174021, 59332, -115524]
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



lemma PB264I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB264I1 : PrimesBelowBoundCertificateInterval O 31 79 264 where
  m := 11
  g := ![3, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB264I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
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
    · exact ![37, 37, 37]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![226981]
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
      exact NI37N1
      exact NI37N2
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
  β := ![I37N0, I37N1, I37N2, I43N1, I59N1, I67N1, I71N1, I73N1]
  Il := ![[I37N0, I37N1, I37N2], [], [I43N1], [], [], [I59N1], [], [I67N1], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
