
import IdealArithmetic.Examples.NF3_3_80565_1.RI3_3_80565_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [26, 22, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 4, 35], [14, 32, 2], [0, 1]]
 g := ![![[11, 20, 11], [7, 25], [16, 22, 1], [24, 1], []], ![[9, 17, 17, 24], [26, 26], [30, 31, 15, 19], [14, 25], [6, 4]], ![[19, 10, 2, 14], [6, 25], [10, 34, 17, 8], [4, 16], [2, 4]]]
 h' := ![![[10, 4, 35], [10, 23, 14], [28, 26, 32], [5, 1, 36], [0, 0, 1], [0, 1]], ![[14, 32, 2], [11, 17, 32], [13, 33, 10], [34, 12, 3], [18, 29, 32], [10, 4, 35]], ![[0, 1], [17, 34, 28], [5, 15, 32], [23, 24, 35], [33, 8, 4], [14, 32, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 5], []]
 b := ![[], [36, 8, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [26, 22, 13, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14726, -4440, -9324]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![398, -120, -252]
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


def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, -59, -28]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![127, -59, -28]] 
 ![![41, 0, 0], ![17, 1, 0], ![27, 0, 1]] where
  M :=![![![127, -59, -28], ![921, -433, -205], ![2205, -1040, -492]]]
  hmulB := by decide  
  f := ![![![164, -92, 29]], ![![41, -20, 6]], ![![183, -109, 35]]]
  g := ![![![46, -59, -28], ![337, -433, -205], ![809, -1040, -492]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, 1, 2]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-35, 1, 2]] 
 ![![41, 0, 0], ![32, 1, 0], ![28, 0, 1]] where
  M :=![![![-35, 1, 2], ![-69, 5, 5], ![-45, 10, 6]]]
  hmulB := by decide  
  f := ![![![20, -14, 5]], ![![11, -8, 3]], ![![25, -17, 6]]]
  g := ![![![-3, 1, 2], ![-9, 5, 5], ![-13, 10, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![127, -59, -28]] ![![-35, 1, 2]]
  ![![886, -448, -209]] where
 M := ![![![886, -448, -209]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![886, -448, -209]] ![![-35, 1, 2]]
  ![![41, 0, 0]] where
 M := ![![![9307, -3444, -1722]]]
 hmul := by decide  
 g := ![![![![227, -84, -42]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![189, -117, 38]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![189, -117, 38]] 
 ![![43, 0, 0], ![0, 43, 0], ![31, 32, 1]] where
  M :=![![![189, -117, 38], ![-1447, 949, -313], ![3905, -2530, 832]]]
  hmulB := by decide  
  f := ![![![-54, 28, 13]], ![![-427, 206, 97]], ![![-381, 185, 87]]]
  g := ![![![-23, -31, 38], ![192, 255, -313], ![-509, -678, 832]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [38, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 42], [0, 1]]
 g := ![![[22, 17], [31, 38], [14], [3, 17], [1]], ![[0, 26], [40, 5], [14], [24, 26], [1]]]
 h' := ![![[24, 42], [26, 24], [37, 34], [15, 10], [5, 24], [0, 1]], ![[0, 1], [0, 19], [36, 9], [40, 33], [22, 19], [24, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [39, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [38, 19, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![819, -851, 1125]
  a := ![2, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-792, -857, 1125]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![54, -28, -13]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![54, -28, -13]] 
 ![![43, 0, 0], ![32, 1, 0], ![3, 0, 1]] where
  M :=![![![54, -28, -13], ![427, -206, -97], ![1045, -495, -234]]]
  hmulB := by decide  
  f := ![![![-189, 117, -38]], ![![-107, 65, -21]], ![![-104, 67, -22]]]
  g := ![![![23, -28, -13], ![170, -206, -97], ![409, -495, -234]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![189, -117, 38]] ![![54, -28, -13]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-315, 163, -50]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-315, 163, -50]] 
 ![![47, 0, 0], ![7, 1, 0], ![31, 0, 1]] where
  M :=![![![-315, 163, -50], ![1913, -1315, 439], ![-5455, 3510, -1152]]]
  hmulB := by decide  
  f := ![![![26010, -12276, -5807]], ![![7937, -3746, -1772]], ![![26915, -12703, -6009]]]
  g := ![![![2, 163, -50], ![-53, -1315, 439], ![121, 3510, -1152]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, -8, -3]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![0, -8, -3]] 
 ![![47, 0, 0], ![12, 1, 0], ![15, 0, 1]] where
  M :=![![![0, -8, -3], ![97, -60, -27], ![295, -145, -68]]]
  hmulB := by decide  
  f := ![![![165, -109, 36]], ![![13, -9, 3]], ![![130, -85, 28]]]
  g := ![![![3, -8, -3], ![26, -60, -27], ![65, -145, -68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-233, 110, 52]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![-233, 110, 52]] 
 ![![47, 0, 0], ![27, 1, 0], ![8, 0, 1]] where
  M :=![![![-233, 110, 52], ![-1710, 807, 382], ![-4110, 1940, 917]]]
  hmulB := by decide  
  f := ![![![1061, -10, -56]], ![![651, -7, -34]], ![![194, 0, -11]]]
  g := ![![![-77, 110, 52], ![-565, 807, 382], ![-1358, 1940, 917]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-315, 163, -50]] ![![0, -8, -3]]
  ![![1061, -10, -56]] where
 M := ![![![1061, -10, -56]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![1061, -10, -56]] ![![-233, 110, 52]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-191, 2, 10]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-191, 2, 10]] 
 ![![53, 0, 0], ![0, 1, 0], ![18, 0, 1]] where
  M :=![![![-191, 2, 10], ![-348, 9, 16], ![-120, -10, 11]]]
  hmulB := by decide  
  f := ![![![-259, 122, 58]], ![![-36, 17, 8]], ![![-174, 82, 39]]]
  g := ![![![-7, 2, 10], ![-12, 9, 16], ![-6, -10, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![259, -122, -58]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![259, -122, -58]] 
 ![![53, 0, 0], ![0, 53, 0], ![33, 35, 1]] where
  M :=![![![259, -122, -58], ![1908, -901, -424], ![4560, -2150, -1023]]]
  hmulB := by decide  
  f := ![![![191, -2, -10]], ![![348, -9, -16]], ![![351, -7, -17]]]
  g := ![![![41, 36, -58], ![300, 263, -424], ![723, 635, -1023]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [15, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 52], [0, 1]]
 g := ![![[24, 46], [46], [], [], [11, 1]], ![[0, 7], [46], [], [], [22, 52]]]
 h' := ![![[11, 52], [52, 29], [0, 24], [36], [47], [0, 1]], ![[0, 1], [0, 24], [52, 29], [36], [47], [11, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [8, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [15, 42, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-75124, -91133, 354489]
  a := ![-65, 1, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-222137, -235816, 354489]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-191, 2, 10]] ![![259, -122, -58]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-54, 2, 3]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-54, 2, 3]] 
 ![![59, 0, 0], ![0, 59, 0], ![41, 40, 1]] where
  M :=![![![-54, 2, 3], ![-103, 6, 9], ![-85, 25, 8]]]
  hmulB := by decide  
  f := ![![![-3, 1, 0]], ![![1, -3, 3]], ![![-2, -1, 2]]]
  g := ![![![-3, -2, 3], ![-8, -6, 9], ![-7, -5, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [14, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 58], [0, 1]]
 g := ![![[50, 9], [18, 4], [57], [9, 22], [8, 1]], ![[4, 50], [50, 55], [57], [8, 37], [16, 58]]]
 h' := ![![[8, 58], [43, 56], [33, 57], [51, 36], [6, 50], [0, 1]], ![[0, 1], [19, 3], [17, 2], [44, 23], [52, 9], [8, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [1, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [14, 51, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![162, -478, 640]
  a := ![-2, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-442, -442, 640]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-3, 1, 0]] 
 ![![59, 0, 0], ![56, 1, 0], ![17, 0, 1]] where
  M :=![![![-3, 1, 0], ![1, -3, 3], ![-35, 20, -2]]]
  hmulB := by decide  
  f := ![![![-54, 2, 3]], ![![-53, 2, 3]], ![![-17, 1, 1]]]
  g := ![![![-1, 1, 0], ![2, -3, 3], ![-19, 20, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-54, 2, 3]] ![![-3, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [44, 42, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 47], [8, 13], [0, 1]]
 g := ![![[3, 40, 56], [12, 9], [29, 46, 16], [49, 38, 4], [1]], ![[18, 53, 57], [44, 57], [10, 54, 25], [8, 39, 52], [1]], ![[3, 29, 9], [23, 56], [18, 22, 20], [60, 45, 5], [1]]]
 h' := ![![[51, 47], [46, 4, 19], [5, 5, 3], [40, 36, 57], [17, 19, 59], [0, 1]], ![[8, 13], [15, 18, 3], [11, 38, 39], [12, 23, 9], [54, 28, 35], [51, 47]], ![[0, 1], [13, 39, 39], [54, 18, 19], [11, 2, 56], [41, 14, 28], [8, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10], []]
 b := ![[], [50, 28, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [44, 42, 2, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17507, -5307, -11529]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![287, -87, -189]
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



lemma PB64I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 63 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 63 (by omega)

def PB64I1 : PrimesBelowBoundCertificateInterval O 31 63 64 where
  m := 7
  g := ![1, 3, 2, 3, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61]
  hP := PB64I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![53, 2809]
    · exact ![3481, 59]
    · exact ![226981]
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
      exact NI41N1
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
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
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
  β := ![I41N0, I41N1, I43N1, I47N0, I47N1, I47N2, I53N0, I59N1]
  Il := ![[], [I41N0, I41N1, I41N1], [I43N1], [I47N0, I47N1, I47N2], [I53N0], [I59N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
