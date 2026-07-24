
import IdealArithmetic.Examples.NF3_3_662216_1.RI3_3_662216_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [20, 31, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 9, 17], [6, 27, 20], [0, 1]]
 g := ![![[23, 10, 12], [17, 34], [12, 32, 25], [27, 1], []], ![[28, 34, 11, 31], [36, 26], [30, 6, 13, 14], [19, 26], [6, 30]], ![[21, 22, 18, 19], [13, 10], [2, 2, 34, 8], [22, 7], [3, 30]]]
 h' := ![![[21, 9, 17], [21, 4, 7], [19, 27, 21], [15, 31, 32], [0, 0, 1], [0, 1]], ![[6, 27, 20], [21, 29, 35], [1, 0, 27], [23, 25, 22], [25, 36, 27], [21, 9, 17]], ![[0, 1], [25, 4, 32], [10, 10, 26], [25, 18, 20], [13, 1, 9], [6, 27, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 17], []]
 b := ![[], [9, 8, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [20, 31, 10, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-295593, -136493, -30118]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7989, -3689, -814]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [32, 15, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 25, 1], [31, 15, 40], [0, 1]]
 g := ![![[33, 19, 25], [25, 36], [32, 40], [26, 0, 1], []], ![[29, 38, 3, 1], [33, 8], [30, 40], [22, 3, 35, 20], [9, 1]], ![[39, 31, 22, 25], [23, 1], [], [15, 19, 31, 31], [11, 1]]]
 h' := ![![[10, 25, 1], [12, 35, 36], [22, 15, 35], [29, 20, 9], [0, 0, 1], [0, 1]], ![[31, 15, 40], [31, 30, 1], [29, 17, 7], [13, 12, 32], [17, 5, 15], [10, 25, 1]], ![[0, 1], [20, 17, 4], [31, 9, 40], [21, 9], [35, 36, 25], [31, 15, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 12], []]
 b := ![[], [30, 27, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [32, 15, 0, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1584978, 1071166, 407622]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![38658, 26126, 9942]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [34, 10, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 5, 18], [26, 37, 25], [0, 1]]
 g := ![![[33, 33, 24], [42, 1, 14], [9, 31], [1, 22, 1], []], ![[26, 39, 0, 3], [33, 7, 34, 12], [8, 9], [9, 19, 16, 3], [41, 23]], ![[15, 25, 1, 9], [20, 41, 14, 17], [35, 24], [24, 15, 3, 23], [34, 23]]]
 h' := ![![[39, 5, 18], [34, 33, 14], [33, 4, 10], [9, 16, 26], [0, 0, 1], [0, 1]], ![[26, 37, 25], [3, 31, 37], [40, 41, 12], [22, 40, 3], [41, 15, 37], [39, 5, 18]], ![[0, 1], [20, 22, 35], [24, 41, 21], [28, 30, 14], [36, 28, 5], [26, 37, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 37], []]
 b := ![[], [17, 40, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [34, 10, 21, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6789278084, -3609882766, -1037014918]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-157890188, -83950762, -24116626]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1420526, 600477, 105516]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![1420526, 600477, 105516]] 
 ![![47, 0, 0], ![0, 47, 0], ![45, 5, 1]] where
  M :=![![![1420526, 600477, 105516], ![17588553, 7434938, 1306470], ![108178041, 45728433, 8035415]]]
  hmulB := by decide  
  f := ![![![287920, 11841, -5706]], ![![-906825, -37322, 17976]], ![![206526, 8494, -4093]]]
  g := ![![![-70802, 1551, 105516], ![-876651, 19204, 1306470], ![-5391822, 118114, 8035415]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [25, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 46], [0, 1]]
 g := ![![[17, 32], [41, 6], [19, 3], [45, 4], [1]], ![[0, 15], [29, 41], [13, 44], [37, 43], [1]]]
 h' := ![![[45, 46], [9, 28], [42, 37], [3, 12], [22, 45], [0, 1]], ![[0, 1], [0, 19], [15, 10], [26, 35], [26, 2], [45, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [1, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [25, 2, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1141, 2153, 1427]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1342, -106, 1427]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-287920, -11841, 5706]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-287920, -11841, 5706]] 
 ![![47, 0, 0], ![36, 1, 0], ![34, 0, 1]] where
  M :=![![![-287920, -11841, 5706], ![906825, 37322, -17976], ![-1284447, -52983, 25481]]]
  hmulB := by decide  
  f := ![![![-1420526, -600477, -105516]], ![![-1462287, -618130, -108618]], ![![-3329275, -1407333, -247297]]]
  g := ![![![-1184, -11841, 5706], ![3711, 37322, -17976], ![-5179, -52983, 25481]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![1420526, 600477, 105516]] ![![-287920, -11841, 5706]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3351337, 137736, -66402]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![3351337, 137736, -66402]] 
 ![![53, 0, 0], ![0, 53, 0], ![21, 6, 1]] where
  M :=![![![3351337, 137736, -66402], ![-10552986, -433577, 209070], ![14937678, 613134, -295841]]]
  hmulB := by decide  
  f := ![![![1545809, 653436, 114822]], ![![19139778, 8090663, 1421694]], ![![5000367, 2113728, 371425]]]
  g := ![![![89543, 10116, -66402], ![-281952, -31849, 209070], ![399063, 45060, -295841]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [11, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 52], [0, 1]]
 g := ![![[19, 29], [38], [12, 13], [4], [3, 1]], ![[0, 24], [38], [51, 40], [4], [6, 52]]]
 h' := ![![[3, 52], [46, 20], [27, 12], [38, 38], [20, 51], [0, 1]], ![[0, 1], [0, 33], [10, 41], [46, 15], [14, 2], [3, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [9, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [11, 50, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1043, 616, 138]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-35, -4, 138]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![513856, 21123, -10182]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![513856, 21123, -10182]] 
 ![![53, 0, 0], ![40, 1, 0], ![22, 0, 1]] where
  M :=![![![513856, 21123, -10182], ![-1618179, -66518, 32064], ![2290965, 94173, -45395]]]
  hmulB := by decide  
  f := ![![![-21538, -9099, -1596]], ![![-21275, -8990, -1578]], ![![-39863, -16845, -2957]]]
  g := ![![![-2020, 21123, -10182], ![6361, -66518, 32064], ![-9005, 94173, -45395]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![3351337, 137736, -66402]] ![![513856, 21123, -10182]]
  ![![53, 0, 0]] where
 M := ![![![1347098464798, 55375092657, -26692627440]]]
 hmul := by decide  
 g := ![![![![25416952166, 1044813069, -503634480]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![4, 1, 0]] 
 ![![59, 0, 0], ![4, 1, 0], ![22, 0, 1]] where
  M :=![![![4, 1, 0], ![1, 4, 2], ![161, 57, 5]]]
  hmulB := by decide  
  f := ![![![94, 5, -2]], ![![1, 0, 0]], ![![45, 3, -1]]]
  g := ![![![0, 1, 0], ![-1, 4, 2], ![-3, 57, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 4, -2]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![103, 4, -2]] 
 ![![59, 0, 0], ![50, 1, 0], ![19, 0, 1]] where
  M :=![![![103, 4, -2], ![-318, -11, 6], ![426, 10, -7]]]
  hmulB := by decide  
  f := ![![![17, 8, 2]], ![![20, 9, 2]], ![![31, 14, 3]]]
  g := ![![![-1, 4, -2], ![2, -11, 6], ![1, 10, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![4, 1, 0]] ![![4, 1, 0]]
  ![![17, 8, 2]] where
 M := ![![![17, 8, 2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI59N1 : IdealMulLeCertificate' Table 
  ![![17, 8, 2]] ![![103, 4, -2]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32, 13, 2]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![32, 13, 2]] 
 ![![61, 0, 0], ![15, 1, 0], ![10, 0, 1]] where
  M :=![![![32, 13, 2], ![335, 146, 28], ![2311, 959, 159]]]
  hmulB := by decide  
  f := ![![![-3638, -149, 72]], ![![-707, -29, 14]], ![![-861, -35, 17]]]
  g := ![![![-3, 13, 2], ![-35, 146, 28], ![-224, 959, 159]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10527, 4450, 782]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![10527, 4450, 782]] 
 ![![61, 0, 0], ![53, 1, 0], ![60, 0, 1]] where
  M :=![![![10527, 4450, 782], ![130352, 55101, 9682], ![801688, 338888, 59551]]]
  hmulB := by decide  
  f := ![![![206035, 8466, -4082]], ![![168379, 6919, -3336]], ![![217708, 8944, -4313]]]
  g := ![![![-4463, 4450, 782], ![-55261, 55101, 9682], ![-339876, 338888, 59551]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![32, 13, 2]] ![![10527, 4450, 782]]
  ![![3634816, 1536489, 269992]] where
 M := ![![![3634816, 1536489, 269992]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![3634816, 1536489, 269992]] ![![10527, 4450, 782]]
  ![![61, 0, 0]] where
 M := ![![![454997468656, 192334060485, 33797006202]]]
 hmul := by decide  
 g := ![![![![7458974896, 3153017385, 554049282]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [53, 57, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 38, 62], [49, 28, 5], [0, 1]]
 g := ![![[61, 52, 17], [27, 8, 55], [8, 33], [54, 37], [32, 1], []], ![[43, 41, 61, 9], [11, 23, 16, 39], [66, 36], [42, 35], [37, 47], [18, 25]], ![[13, 29, 12, 51], [52, 57, 44, 7], [28, 55], [44, 22], [2, 37], [8, 25]]]
 h' := ![![[50, 38, 62], [43, 44, 34], [59, 38, 51], [58, 28, 10], [46, 66, 29], [0, 0, 1], [0, 1]], ![[49, 28, 5], [1, 18, 62], [3, 35, 32], [34, 10, 6], [7, 41, 13], [5, 42, 28], [50, 38, 62]], ![[0, 1], [5, 5, 38], [37, 61, 51], [28, 29, 51], [45, 27, 25], [34, 25, 38], [49, 28, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 33], []]
 b := ![[], [49, 34, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [53, 57, 35, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9130023, 3865833, 677973]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![136269, 57699, 10119]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10932, -4621, -812]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-10932, -4621, -812]] 
 ![![71, 0, 0], ![0, 71, 0], ![32, 46, 1]] where
  M :=![![![-10932, -4621, -812], ![-135353, -57216, -10054], ![-832489, -351905, -61837]]]
  hmulB := by decide  
  f := ![![![-182, 27, -2]], ![![-295, -296, 52]], ![![-215, -161, 29]]]
  g := ![![![212, 461, -812], ![2625, 5708, -10054], ![16145, 35107, -61837]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [10, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 70], [0, 1]]
 g := ![![[43, 64], [11, 10], [63, 24], [43], [16], [1]], ![[0, 7], [42, 61], [38, 47], [43], [16], [1]]]
 h' := ![![[67, 70], [32, 8], [9, 62], [46, 38], [11, 16], [61, 67], [0, 1]], ![[0, 1], [0, 63], [45, 9], [36, 33], [18, 55], [6, 4], [67, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [12, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [10, 4, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1902, -45, 513]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-258, -333, 513]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-182, 27, -2]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-182, 27, -2]] 
 ![![71, 0, 0], ![49, 1, 0], ![7, 0, 1]] where
  M :=![![![-182, 27, -2], ![-295, -296, 52], ![4129, 1321, -269]]]
  hmulB := by decide  
  f := ![![![-10932, -4621, -812]], ![![-9451, -3995, -702]], ![![-12803, -5412, -951]]]
  g := ![![![-21, 27, -2], ![195, -296, 52], ![-827, 1321, -269]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-10932, -4621, -812]] ![![-182, 27, -2]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![467123, 19202, -9256]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![467123, 19202, -9256]] 
 ![![73, 0, 0], ![0, 73, 0], ![63, 44, 1]] where
  M :=![![![467123, 19202, -9256], ![-1471014, -60469, 29148], ![2082618, 85610, -41267]]]
  hmulB := by decide  
  f := ![![![191, 38, -16]], ![![-2538, -721, 60]], ![![-1305, -396, 13]]]
  g := ![![![14387, 5842, -9256], ![-45306, -18397, 29148], ![64143, 26046, -41267]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [37, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 72], [0, 1]]
 g := ![![[57, 2], [50], [36], [70, 49], [64], [1]], ![[0, 71], [50], [36], [24, 24], [64], [1]]]
 h' := ![![[8, 72], [36, 32], [39, 14], [38, 6], [23, 66], [36, 8], [0, 1]], ![[0, 1], [0, 41], [5, 59], [13, 67], [40, 7], [27, 65], [8, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [59, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [37, 65, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3204, 2269, 1198]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-990, -691, 1198]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-191, -38, 16]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-191, -38, 16]] 
 ![![73, 0, 0], ![57, 1, 0], ![55, 0, 1]] where
  M :=![![![-191, -38, 16], ![2538, 721, -60], ![-4374, -422, 683]]]
  hmulB := by decide  
  f := ![![![-467123, -19202, 9256]], ![![-344589, -14165, 6828]], ![![-380471, -15640, 7539]]]
  g := ![![![15, -38, 16], ![-483, 721, -60], ![-245, -422, 683]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![467123, 19202, -9256]] ![![-191, -38, 16]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [44, 22, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 32, 11], [18, 46, 68], [0, 1]]
 g := ![![[55, 6, 51], [22, 70, 76], [40, 19, 51], [7, 9, 72], [47, 1], []], ![[64, 76, 45, 44], [35, 45, 78, 64], [1, 32, 46, 23], [20, 52, 60, 40], [13, 62], [71, 42]], ![[50, 72, 31, 15], [31, 15, 1, 68], [19, 66, 4, 43], [76, 3, 43, 35], [12, 76], [14, 42]]]
 h' := ![![[29, 32, 11], [59, 1, 29], [57, 7, 32], [8, 41, 50], [65, 28, 54], [0, 0, 1], [0, 1]], ![[18, 46, 68], [4, 75, 2], [42, 29, 48], [17, 5, 65], [45, 9, 27], [8, 26, 46], [29, 32, 11]], ![[0, 1], [62, 3, 48], [3, 43, 78], [50, 33, 43], [48, 42, 77], [24, 53, 32], [18, 46, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 6], []]
 b := ![[], [4, 39, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [44, 22, 32, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2923316, -1506925, -408035]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-37004, -19075, -5165]
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
  g := ![1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB181I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N1]
    · exact ![I67N0]
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
    · exact ![61, 61, 61]
    · exact ![300763]
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
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
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
  β := ![I47N1, I53N1, I59N0, I59N1, I61N0, I61N1, I71N1, I73N1]
  Il := ![[], [], [], [I47N1], [I53N1], [I59N0, I59N0, I59N1], [I61N0, I61N1, I61N1], [], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
