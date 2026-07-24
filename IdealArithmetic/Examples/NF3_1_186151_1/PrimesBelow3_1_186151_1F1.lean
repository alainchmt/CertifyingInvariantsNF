
import IdealArithmetic.Examples.NF3_1_186151_1.RI3_1_186151_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [20, 1, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 27, 10], [6, 9, 27], [0, 1]]
 g := ![![[8, 34, 33], [], [1, 32, 4], [31, 1], []], ![[1, 34, 16, 28], [17, 21], [20, 19, 25, 1], [31, 7], [14, 26]], ![[27, 10, 28, 28], [36, 21], [18, 33, 33, 3], [32, 26], [34, 26]]]
 h' := ![![[25, 27, 10], [30, 15, 25], [17, 32], [9, 23, 35], [0, 0, 1], [0, 1]], ![[6, 9, 27], [2, 11, 5], [3, 13, 24], [5, 25, 27], [12, 2, 9], [25, 27, 10]], ![[0, 1], [4, 11, 7], [24, 29, 13], [29, 26, 12], [22, 35, 27], [6, 9, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 13], []]
 b := ![[], [33, 33, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [20, 1, 6, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-134569, -58164, -6512]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3637, -1572, -176]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-449, -68, 11]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-449, -68, 11]] 
 ![![41, 0, 0], ![0, 41, 0], ![30, 5, 1]] where
  M :=![![![-449, -68, 11], ![3003, 398, -68], ![-18564, -2233, 398]]]
  hmulB := by decide  
  f := ![![![-160, -61, -6]], ![![-1638, -622, -61]], ![![-723, -275, -27]]]
  g := ![![![-19, -3, 11], ![123, 18, -68], ![-744, -103, 398]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [32, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 40], [0, 1]]
 g := ![![[12, 9], [25], [16], [4, 20], [1]], ![[0, 32], [25], [16], [32, 21], [1]]]
 h' := ![![[26, 40], [4, 3], [5, 5], [36, 37], [9, 26], [0, 1]], ![[0, 1], [0, 38], [12, 36], [14, 4], [29, 15], [26, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [40, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [32, 15, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3258, 1507, 736]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-618, -53, 736]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![160, 61, 6]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![160, 61, 6]] 
 ![![41, 0, 0], ![36, 1, 0], ![16, 0, 1]] where
  M :=![![![160, 61, 6], ![1638, 622, 61], ![16653, 6335, 622]]]
  hmulB := by decide  
  f := ![![![449, 68, -11]], ![![321, 50, -8]], ![![628, 81, -14]]]
  g := ![![![-52, 61, 6], ![-530, 622, 61], ![-5399, 6335, 622]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-449, -68, 11]] ![![160, 61, 6]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 10, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![23, 10, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![23, 10, 1]] where
  M :=![![![23, 10, 1], ![273, 100, 10], ![2730, 1043, 100]]]
  hmulB := by decide  
  f := ![![![-10, 1, 0]], ![![0, -10, 1]], ![![1, 0, 0]]]
  g := ![![![0, 0, 1], ![1, 0, 10], ![10, 1, 100]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [30, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 42], [0, 1]]
 g := ![![[15, 41], [11, 14], [10], [37, 13], [1]], ![[12, 2], [32, 29], [10], [35, 30], [1]]]
 h' := ![![[23, 42], [14, 16], [22, 33], [8, 28], [13, 23], [0, 1]], ![[0, 1], [38, 27], [7, 10], [7, 15], [26, 20], [23, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [3, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [30, 20, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2300, 11, 186]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-46, -43, 186]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, -1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![10, -1, 0]] 
 ![![43, 0, 0], ![33, 1, 0], ![29, 0, 1]] where
  M :=![![![10, -1, 0], ![0, 10, -1], ![-273, -77, 10]]]
  hmulB := by decide  
  f := ![![![-23, -10, -1]], ![![-24, -10, -1]], ![![-79, -31, -3]]]
  g := ![![![1, -1, 0], ![-7, 10, -1], ![46, -77, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![23, 10, 1]] ![![10, -1, 0]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![23, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![23, 1, 0]] 
 ![![47, 0, 0], ![23, 1, 0], ![35, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![23, 1, 0], ![0, 23, 1], ![273, 77, 23]]]
  hmulB := by decide  
  f := ![![![208, 9, 0], ![-423, 0, 0]], ![![92, 4, 0], ![-187, 0, 0]], ![![150, 6, 0], ![-305, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 47, 0], ![-35, 0, 47]], ![![0, 1, 0], ![-12, 23, 1], ![-49, 77, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-19, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-19, 1, 0]] 
 ![![47, 0, 0], ![28, 1, 0], ![15, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-19, 1, 0], ![0, -19, 1], ![273, 77, -19]]]
  hmulB := by decide  
  f := ![![![172, -9, 0], ![423, 0, 0]], ![![96, -5, 0], ![236, 0, 0]], ![![84, -4, 0], ![207, 1, 0]]]
  g := ![![![1, 0, 0], ![-28, 47, 0], ![-15, 0, 47]], ![![-1, 1, 0], ![11, -19, 1], ![-34, 77, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-4, 1, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-4, 1, 0]] 
 ![![47, 0, 0], ![43, 1, 0], ![31, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-4, 1, 0], ![0, -4, 1], ![273, 77, -4]]]
  hmulB := by decide  
  f := ![![![57, -14, 0], ![658, 0, 0]], ![![53, -13, 0], ![612, 0, 0]], ![![41, -10, 0], ![474, 1, 0]]]
  g := ![![![1, 0, 0], ![-43, 47, 0], ![-31, 0, 47]], ![![-1, 1, 0], ![3, -4, 1], ![-62, 77, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![23, 1, 0]] ![![47, 0, 0], ![-19, 1, 0]]
  ![![47, 0, 0], ![-61, 4, 1]] where
 M := ![![![2209, 0, 0], ![-893, 47, 0]], ![![1081, 47, 0], ![-437, 4, 1]]]
 hmul := by decide  
 g := ![![![![47, 0, 0], ![0, 0, 0]], ![![42, -3, -1], ![47, 0, 0]]], ![![![23, 1, 0], ![0, 0, 0]], ![![53, -4, -1], ![48, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-61, 4, 1]] ![![47, 0, 0], ![-4, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-188, 47, 0]], ![![-2867, 188, 47], ![517, 0, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-4, 1, 0]]], ![![![-61, 4, 1]], ![![11, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![26, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![26, 1, 0]] 
 ![![53, 0, 0], ![26, 1, 0], ![13, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![26, 1, 0], ![0, 26, 1], ![273, 77, 26]]]
  hmulB := by decide  
  f := ![![![287, 11, 0], ![-583, 0, 0]], ![![130, 5, 0], ![-264, 0, 0]], ![![39, 1, 0], ![-79, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 53, 0], ![-13, 0, 53]], ![![0, 1, 0], ![-13, 26, 1], ![-39, 77, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-23, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-23, 1, 0]] 
 ![![53, 0, 0], ![30, 1, 0], ![1, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-23, 1, 0], ![0, -23, 1], ![273, 77, -23]]]
  hmulB := by decide  
  f := ![![![921, -40, 0], ![2120, 0, 0]], ![![530, -23, 0], ![1220, 0, 0]], ![![33, -1, 0], ![76, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 53, 0], ![-1, 0, 53]], ![![-1, 1, 0], ![13, -23, 1], ![-38, 77, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-3, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-3, 1, 0]] 
 ![![53, 0, 0], ![50, 1, 0], ![44, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-3, 1, 0], ![0, -3, 1], ![273, 77, -3]]]
  hmulB := by decide  
  f := ![![![61, -20, 0], ![1060, 0, 0]], ![![58, -19, 0], ![1008, 0, 0]], ![![52, -17, 0], ![904, 1, 0]]]
  g := ![![![1, 0, 0], ![-50, 53, 0], ![-44, 0, 53]], ![![-1, 1, 0], ![2, -3, 1], ![-65, 77, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![26, 1, 0]] ![![53, 0, 0], ![-23, 1, 0]]
  ![![53, 0, 0], ![-68, 3, 1]] where
 M := ![![![2809, 0, 0], ![-1219, 53, 0]], ![![1378, 53, 0], ![-598, 3, 1]]]
 hmul := by decide  
 g := ![![![![53, 0, 0], ![0, 0, 0]], ![![45, -2, -1], ![53, 0, 0]]], ![![![26, 1, 0], ![0, 0, 0]], ![![58, -3, -1], ![54, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-68, 3, 1]] ![![53, 0, 0], ![-3, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-159, 53, 0]], ![![-3604, 159, 53], ![477, 0, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-3, 1, 0]]], ![![![-68, 3, 1]], ![![9, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![27, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![27, 1, 0]] 
 ![![59, 0, 0], ![27, 1, 0], ![38, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![27, 1, 0], ![0, 27, 1], ![273, 77, 27]]]
  hmulB := by decide  
  f := ![![![514, 19, 0], ![-1121, 0, 0]], ![![216, 8, 0], ![-471, 0, 0]], ![![310, 11, 0], ![-676, 1, 0]]]
  g := ![![![1, 0, 0], ![-27, 59, 0], ![-38, 0, 59]], ![![0, 1, 0], ![-13, 27, 1], ![-48, 77, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-15, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-15, 1, 0]] 
 ![![59, 0, 0], ![44, 1, 0], ![11, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-15, 1, 0], ![0, -15, 1], ![273, 77, -15]]]
  hmulB := by decide  
  f := ![![![91, -6, 0], ![354, 0, 0]], ![![76, -5, 0], ![296, 0, 0]], ![![19, -1, 0], ![74, 1, 0]]]
  g := ![![![1, 0, 0], ![-44, 59, 0], ![-11, 0, 59]], ![![-1, 1, 0], ![11, -15, 1], ![-50, 77, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-12, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-12, 1, 0]] 
 ![![59, 0, 0], ![47, 1, 0], ![33, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-12, 1, 0], ![0, -12, 1], ![273, 77, -12]]]
  hmulB := by decide  
  f := ![![![85, -7, 0], ![413, 0, 0]], ![![73, -6, 0], ![355, 0, 0]], ![![63, -5, 0], ![307, 1, 0]]]
  g := ![![![1, 0, 0], ![-47, 59, 0], ![-33, 0, 59]], ![![-1, 1, 0], ![9, -12, 1], ![-50, 77, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![27, 1, 0]] ![![59, 0, 0], ![-15, 1, 0]]
  ![![59, 0, 0], ![-51, 12, 1]] where
 M := ![![![3481, 0, 0], ![-885, 59, 0]], ![![1593, 59, 0], ![-405, 12, 1]]]
 hmul := by decide  
 g := ![![![![59, 0, 0], ![0, 0, 0]], ![![36, -11, -1], ![59, 0, 0]]], ![![![27, 1, 0], ![0, 0, 0]], ![![45, -12, -1], ![60, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-51, 12, 1]] ![![59, 0, 0], ![-12, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-708, 59, 0]], ![![-3009, 708, 59], ![885, -118, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-12, 1, 0]]], ![![![-51, 12, 1]], ![![15, -2, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-25, -28, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-25, -28, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![36, 33, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-25, -28, 1], ![273, 52, -28], ![-7644, -1883, 52]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -33, 61]], ![![-1, -1, 1], ![21, 16, -28], ![-156, -59, 52]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [42, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 60], [0, 1]]
 g := ![![[24, 16], [57], [48, 1], [31, 36], [29, 1]], ![[0, 45], [57], [16, 60], [38, 25], [58, 60]]]
 h' := ![![[29, 60], [55, 57], [58, 22], [40, 1], [2, 6], [0, 1]], ![[0, 1], [0, 4], [25, 39], [8, 60], [54, 55], [29, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [45, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [42, 32, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1563, 2029, 592]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-375, -287, 592]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![28, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![28, 1, 0]] 
 ![![61, 0, 0], ![28, 1, 0], ![9, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![28, 1, 0], ![0, 28, 1], ![273, 77, 28]]]
  hmulB := by decide  
  f := ![![![449, 16, 0], ![-976, 0, 0]], ![![196, 7, 0], ![-426, 0, 0]], ![![69, 2, 0], ![-150, 1, 0]]]
  g := ![![![1, 0, 0], ![-28, 61, 0], ![-9, 0, 61]], ![![0, 1, 0], ![-13, 28, 1], ![-35, 77, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-25, -28, 1]] ![![61, 0, 0], ![28, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1708, 61, 0]], ![![-1525, -1708, 61], ![-427, -732, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![28, 1, 0]]], ![![![-25, -28, 1]], ![![-7, -12, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-28, 7, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-28, 7, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![39, 7, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-28, 7, 1], ![273, 49, 7], ![1911, 812, 49]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -7, 67]], ![![-1, 0, 1], ![0, 0, 7], ![0, 7, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [14, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 66], [0, 1]]
 g := ![![[7, 24], [38, 25], [4], [39], [23], [1]], ![[0, 43], [0, 42], [4], [39], [23], [1]]]
 h' := ![![[36, 66], [4, 52], [46, 62], [54, 65], [8, 21], [53, 36], [0, 1]], ![[0, 1], [0, 15], [0, 5], [49, 2], [27, 46], [9, 31], [36, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [5, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [14, 31, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![560, 396, 47]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19, 1, 47]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-7, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-7, 1, 0]] 
 ![![67, 0, 0], ![60, 1, 0], ![18, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-7, 1, 0], ![0, -7, 1], ![273, 77, -7]]]
  hmulB := by decide  
  f := ![![![365, -52, 0], ![3484, 0, 0]], ![![330, -47, 0], ![3150, 0, 0]], ![![106, -15, 0], ![1012, 1, 0]]]
  g := ![![![1, 0, 0], ![-60, 67, 0], ![-18, 0, 67]], ![![-1, 1, 0], ![6, -7, 1], ![-63, 77, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-28, 7, 1]] ![![67, 0, 0], ![-7, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-469, 67, 0]], ![![-1876, 469, 67], ![469, 0, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-7, 1, 0]]], ![![![-28, 7, 1]], ![![7, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-667, -254, -25]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-667, -254, -25]] 
 ![![71, 0, 0], ![0, 71, 0], ![21, 13, 1]] where
  M :=![![![-667, -254, -25], ![-6825, -2592, -254], ![-69342, -26383, -2592]]]
  hmulB := by decide  
  f := ![![![-242, -17, 4]], ![![1092, 66, -17]], ![![63, 4, -1]]]
  g := ![![![-2, 1, -25], ![-21, 10, -254], ![-210, 103, -2592]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [18, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 70], [0, 1]]
 g := ![![[46, 4], [21, 8], [32, 12], [24], [8], [1]], ![[0, 67], [0, 63], [36, 59], [24], [8], [1]]]
 h' := ![![[24, 70], [48, 69], [63, 24], [18, 56], [38, 38], [53, 24], [0, 1]], ![[0, 1], [0, 2], [0, 47], [13, 15], [27, 33], [61, 47], [24, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [44, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [18, 47, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10440, 4130, 487]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, -31, 487]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![242, 17, -4]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![242, 17, -4]] 
 ![![71, 0, 0], ![58, 1, 0], ![44, 0, 1]] where
  M :=![![![242, 17, -4], ![-1092, -66, 17], ![4641, 217, -66]]]
  hmulB := by decide  
  f := ![![![667, 254, 25]], ![![641, 244, 24]], ![![1390, 529, 52]]]
  g := ![![![-8, 17, -4], ![28, -66, 17], ![-71, 217, -66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-667, -254, -25]] ![![242, 17, -4]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [26, 47, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 14, 11], [16, 58, 62], [0, 1]]
 g := ![![[60, 30, 32], [64, 1], [42, 48], [26, 22, 1], [62, 1], []], ![[16, 46, 51, 34], [38, 16], [44, 19], [72, 55, 29, 42], [25, 6], [72, 48]], ![[31, 17, 57, 14], [19, 9], [60, 6], [43, 61, 61, 7], [7, 50], [21, 48]]]
 h' := ![![[46, 14, 11], [16, 34, 55], [72, 72, 72], [54, 67, 62], [67, 53, 1], [0, 0, 1], [0, 1]], ![[16, 58, 62], [35, 5, 60], [1, 45, 4], [14, 54, 26], [48, 26, 57], [25, 14, 58], [46, 14, 11]], ![[0, 1], [13, 34, 31], [54, 29, 70], [9, 25, 58], [41, 67, 15], [2, 59, 14], [16, 58, 62]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 42], []]
 b := ![[], [22, 29, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [26, 47, 11, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![108916, 4599, -4891]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1492, 63, -67]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![38, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![38, 1, 0]] 
 ![![79, 0, 0], ![38, 1, 0], ![57, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![38, 1, 0], ![0, 38, 1], ![273, 77, 38]]]
  hmulB := by decide  
  f := ![![![913, 24, 0], ![-1896, 0, 0]], ![![418, 11, 0], ![-868, 0, 0]], ![![627, 16, 0], ![-1302, 1, 0]]]
  g := ![![![1, 0, 0], ![-38, 79, 0], ![-57, 0, 79]], ![![0, 1, 0], ![-19, 38, 1], ![-61, 77, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-29, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-29, 1, 0]] 
 ![![79, 0, 0], ![50, 1, 0], ![28, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-29, 1, 0], ![0, -29, 1], ![273, 77, -29]]]
  hmulB := by decide  
  f := ![![![1277, -44, 0], ![3476, 0, 0]], ![![784, -27, 0], ![2134, 0, 0]], ![![446, -15, 0], ![1214, 1, 0]]]
  g := ![![![1, 0, 0], ![-50, 79, 0], ![-28, 0, 79]], ![![-1, 1, 0], ![18, -29, 1], ![-35, 77, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-9, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-9, 1, 0]] 
 ![![79, 0, 0], ![70, 1, 0], ![77, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-9, 1, 0], ![0, -9, 1], ![273, 77, -9]]]
  hmulB := by decide  
  f := ![![![451, -50, 0], ![3950, 0, 0]], ![![388, -43, 0], ![3398, 0, 0]], ![![443, -49, 0], ![3880, 1, 0]]]
  g := ![![![1, 0, 0], ![-70, 79, 0], ![-77, 0, 79]], ![![-1, 1, 0], ![7, -9, 1], ![-56, 77, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![38, 1, 0]] ![![79, 0, 0], ![-29, 1, 0]]
  ![![79, 0, 0], ![-75, 9, 1]] where
 M := ![![![6241, 0, 0], ![-2291, 79, 0]], ![![3002, 79, 0], ![-1102, 9, 1]]]
 hmul := by decide  
 g := ![![![![79, 0, 0], ![0, 0, 0]], ![![46, -8, -1], ![79, 0, 0]]], ![![![38, 1, 0], ![0, 0, 0]], ![![62, -9, -1], ![80, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-75, 9, 1]] ![![79, 0, 0], ![-9, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-711, 79, 0]], ![![-5925, 711, 79], ![948, -79, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-9, 1, 0]]], ![![![-75, 9, 1]], ![![12, -1, 0]]]]
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


lemma PB123I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB123I1 : PrimesBelowBoundCertificateInterval O 31 79 123 where
  m := 11
  g := ![1, 2, 2, 3, 3, 3, 2, 2, 2, 1, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB123I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
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
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![53, 53, 53]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![389017]
    · exact ![79, 79, 79]
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
      exact NI53N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I41N1, I43N1, I47N0, I47N1, I47N2, I53N0, I53N1, I53N2, I59N0, I59N1, I59N2, I61N1, I67N1, I71N1, I79N0, I79N1, I79N2]
  Il := ![[], [I41N1], [I43N1], [I47N0, I47N1, I47N2], [I53N0, I53N1, I53N2], [I59N0, I59N1, I59N2], [I61N1], [I67N1], [I71N1], [], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
