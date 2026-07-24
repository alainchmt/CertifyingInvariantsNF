
import IdealArithmetic.Examples.NF3_1_662796_2.RI3_1_662796_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-57, -13, -2]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-57, -13, -2]] 
 ![![37, 0, 0], ![0, 37, 0], ![10, 25, 1]] where
  M :=![![![-57, -13, -2], ![-925, -222, -37], ![-5421, -1250, -198]]]
  hmulB := by decide  
  f := ![![![62, 2, -1]], ![![-471, -12, 7]], ![![-267, -7, 4]]]
  g := ![![![-1, 1, -2], ![-15, 19, -37], ![-93, 100, -198]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [30, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 36], [0, 1]]
 g := ![![[30, 21], [9], [19, 7], [33], [1]], ![[0, 16], [9], [9, 30], [33], [1]]]
 h' := ![![[25, 36], [29, 24], [22, 3], [21, 28], [7, 25], [0, 1]], ![[0, 1], [0, 13], [23, 34], [18, 9], [3, 12], [25, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [18, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [30, 12, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2625, 2067, 651]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-105, -384, 651]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![62, 2, -1]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![62, 2, -1]] 
 ![![37, 0, 0], ![0, 1, 0], ![12, 0, 1]] where
  M :=![![![62, 2, -1], ![-471, -12, 7], ![1276, 21, -17]]]
  hmulB := by decide  
  f := ![![![-57, -13, -2]], ![![-25, -6, -1]], ![![-165, -38, -6]]]
  g := ![![![2, 2, -1], ![-15, -12, 7], ![40, 21, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-57, -13, -2]] ![![62, 2, -1]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-17, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-17, 1, 0]] 
 ![![41, 0, 0], ![24, 1, 0], ![32, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-17, 1, 0], ![-1, -16, 3], ![469, 76, -18]]]
  hmulB := by decide  
  f := ![![![373, 5952, -1116], ![0, 15252, 0]], ![![218, 3472, -651], ![1, 8897, 0]], ![![299, 4645, -871], ![19, 11904, 0]]]
  g := ![![![1, 0, 0], ![-24, 41, 0], ![-32, 0, 41]], ![![-1, 1, 0], ![7, -16, 3], ![-19, 76, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-13, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-13, 1, 0]] 
 ![![41, 0, 0], ![28, 1, 0], ![16, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-13, 1, 0], ![-1, -12, 3], ![469, 76, -14]]]
  hmulB := by decide  
  f := ![![![-800, -9769, 2442], ![41, -33374, 0]], ![![-541, -6661, 1665], ![42, -22755, 0]], ![![-303, -3813, 953], ![45, -13024, 0]]]
  g := ![![![1, 0, 0], ![-28, 41, 0], ![-16, 0, 41]], ![![-1, 1, 0], ![7, -12, 3], ![-35, 76, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-11, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-11, 1, 0]] 
 ![![41, 0, 0], ![30, 1, 0], ![4, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-11, 1, 0], ![-1, -10, 3], ![469, 76, -12]]]
  hmulB := by decide  
  f := ![![![-456, -4681, 1404], ![41, -19188, 0]], ![![-330, -3421, 1026], ![42, -14022, 0]], ![![-41, -457, 137], ![17, -1872, 0]]]
  g := ![![![1, 0, 0], ![-30, 41, 0], ![-4, 0, 41]], ![![-1, 1, 0], ![7, -10, 3], ![-43, 76, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-17, 1, 0]] ![![41, 0, 0], ![-13, 1, 0]]
  ![![41, 0, 0], ![-36, 4, 1]] where
 M := ![![![1681, 0, 0], ![-533, 41, 0]], ![![-697, 41, 0], ![220, -29, 3]]]
 hmul := by decide  
 g := ![![![![41, 0, 0], ![0, 0, 0]], ![![23, -3, -1], ![41, 0, 0]]], ![![![19, -3, -1], ![41, 0, 0]], ![![8, -1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-36, 4, 1]] ![![41, 0, 0], ![-11, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-451, 41, 0]], ![![-1476, 164, 41], ![861, 0, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-11, 1, 0]]], ![![![-36, 4, 1]], ![![21, 0, 0]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [12, 36, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 36, 1], [41, 6, 42], [0, 1]]
 g := ![![[24, 33, 10], [3, 37, 41], [36, 35], [42, 11, 1], []], ![[32, 10], [30, 29, 2, 35], [24, 40], [27, 34, 15, 36], [40, 1]], ![[2, 6, 4, 33], [7, 17, 34, 18], [14, 17], [26, 12, 13, 37], [42, 1]]]
 h' := ![![[13, 36, 1], [7, 4, 28], [13, 22, 16], [12, 33, 11], [0, 0, 1], [0, 1]], ![[41, 6, 42], [37, 15], [10, 18, 32], [30, 27, 13], [33, 0, 6], [13, 36, 1]], ![[0, 1], [17, 24, 15], [10, 3, 38], [36, 26, 19], [16, 0, 36], [41, 6, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 10], []]
 b := ![[], [10, 30, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [12, 36, 32, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17634085, 10454848, 2907832]
  a := ![-3, 0, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![410095, 243136, 67624]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-55, -18, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-55, -18, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![39, 29, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-55, -18, 1], ![487, 3, -55], ![-8780, -1237, 40]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -29, 47]], ![![-2, -1, 1], ![56, 34, -55], ![-220, -51, 40]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [22, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 46], [0, 1]]
 g := ![![[2, 9], [39, 12], [2, 42], [36, 9], [1]], ![[29, 38], [28, 35], [34, 5], [16, 38], [1]]]
 h' := ![![[3, 46], [35, 3], [3, 24], [7, 18], [25, 3], [0, 1]], ![[0, 1], [44, 44], [28, 23], [14, 29], [34, 44], [3, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [19, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [22, 44, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2500833, 1240987, 346283]
  a := ![1, -64, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-234132, -187260, 346283]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![8, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![8, 1, 0]] 
 ![![47, 0, 0], ![8, 1, 0], ![7, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![8, 1, 0], ![-1, 9, 3], ![469, 76, 7]]]
  hmulB := by decide  
  f := ![![![-139, 1187, 396], ![47, -6204, 0]], ![![-22, 198, 66], ![1, -1034, 0]], ![![-27, 176, 59], ![44, -924, 0]]]
  g := ![![![1, 0, 0], ![-8, 47, 0], ![-7, 0, 47]], ![![0, 1, 0], ![-2, 9, 3], ![-4, 76, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-55, -18, 1]] ![![47, 0, 0], ![8, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![376, 47, 0]], ![![-2585, -846, 47], ![47, -141, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![8, 1, 0]]], ![![![-55, -18, 1]], ![![1, -3, -1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-73, -13, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-73, -13, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![33, 40, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-73, -13, 1], ![482, -10, -40], ![-6435, -857, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -40, 53]], ![![-2, -1, 1], ![34, 30, -40], ![-132, -29, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [25, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 52], [0, 1]]
 g := ![![[47, 17], [29], [43, 9], [9], [44, 1]], ![[0, 36], [29], [15, 44], [9], [35, 52]]]
 h' := ![![[44, 52], [30, 21], [38, 33], [50, 50], [13, 3], [0, 1]], ![[0, 1], [0, 32], [6, 20], [24, 3], [39, 50], [44, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [20, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [25, 9, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14068, 9586, 4795]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3251, -3438, 4795]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-13, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-13, 1, 0]] 
 ![![53, 0, 0], ![40, 1, 0], ![36, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-13, 1, 0], ![-1, -12, 3], ![469, 76, -14]]]
  hmulB := by decide  
  f := ![![![81, 960, -240], ![0, 4240, 0]], ![![61, 720, -180], ![1, 3180, 0]], ![![56, 652, -163], ![4, 2880, 0]]]
  g := ![![![1, 0, 0], ![-40, 53, 0], ![-36, 0, 53]], ![![-1, 1, 0], ![7, -12, 3], ![-39, 76, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-73, -13, 1]] ![![53, 0, 0], ![-13, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-689, 53, 0]], ![![-3869, -689, 53], ![1431, 159, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-13, 1, 0]]], ![![![-73, -13, 1]], ![![27, 3, -1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-74, -13, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-74, -13, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![44, 46, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-74, -13, 1], ![482, -11, -40], ![-6435, -857, 16]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -46, 59]], ![![-2, -1, 1], ![38, 31, -40], ![-121, -27, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [14, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 58], [0, 1]]
 g := ![![[56, 17], [55, 20], [17], [23, 46], [42, 1]], ![[3, 42], [10, 39], [17], [8, 13], [25, 58]]]
 h' := ![![[42, 58], [56, 31], [19, 43], [32, 31], [2, 39], [0, 1]], ![[0, 1], [1, 28], [55, 16], [36, 28], [47, 20], [42, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [45, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [14, 17, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2614, 2057, 636]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-430, -461, 636]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-19, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-19, 1, 0]] 
 ![![59, 0, 0], ![40, 1, 0], ![43, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-19, 1, 0], ![-1, -18, 3], ![469, 76, -20]]]
  hmulB := by decide  
  f := ![![![-1530, -27901, 4650], ![59, -91450, 0]], ![![-1030, -18901, 3150], ![60, -61950, 0]], ![![-1108, -20335, 3389], ![65, -66650, 0]]]
  g := ![![![1, 0, 0], ![-40, 59, 0], ![-43, 0, 59]], ![![-1, 1, 0], ![10, -18, 3], ![-29, 76, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-74, -13, 1]] ![![59, 0, 0], ![-19, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1121, 59, 0]], ![![-4366, -767, 59], ![1888, 236, -59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-19, 1, 0]]], ![![![-74, -13, 1]], ![![32, 4, -1]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-34, 12, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-34, 12, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![27, 12, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-34, 12, 1], ![457, 54, 35], ![5290, 1043, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -12, 61]], ![![-1, 0, 1], ![-8, -6, 35], ![73, 11, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [8, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 60], [0, 1]]
 g := ![![[54, 5], [16], [46, 19], [37, 45], [56, 1]], ![[29, 56], [16], [12, 42], [56, 16], [51, 60]]]
 h' := ![![[56, 60], [59, 26], [59, 4], [9, 18], [40, 17], [0, 1]], ![[0, 1], [51, 35], [39, 57], [41, 43], [16, 44], [56, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [53, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [8, 5, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![72947, 15368, 2399]
  a := ![-1, 21, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![134, -220, 2399]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![26, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![26, 1, 0]] 
 ![![61, 0, 0], ![26, 1, 0], ![30, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![26, 1, 0], ![-1, 27, 3], ![469, 76, 25]]]
  hmulB := by decide  
  f := ![![![163, -4374, -486], ![0, 9882, 0]], ![![69, -1863, -207], ![1, 4209, 0]], ![![58, -2152, -239], ![52, 4860, 0]]]
  g := ![![![1, 0, 0], ![-26, 61, 0], ![-30, 0, 61]], ![![0, 1, 0], ![-13, 27, 3], ![-37, 76, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-34, 12, 1]] ![![61, 0, 0], ![26, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1586, 61, 0]], ![![-2074, 732, 61], ![-427, 366, 61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![26, 1, 0]]], ![![![-34, 12, 1]], ![![-7, 6, 1]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [23, 49, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 66, 41], [44, 0, 26], [0, 1]]
 g := ![![[8, 38, 4], [7, 50, 49], [50, 24], [47, 35], [61, 1], []], ![[50, 52, 23, 41], [40, 35, 22, 8], [4, 24], [21, 54], [], [16, 6]], ![[31, 35, 49, 26], [60, 63, 29, 6], [41, 29], [52, 40], [25, 1], [31, 6]]]
 h' := ![![[17, 66, 41], [40, 18, 65], [38, 52, 60], [7, 65, 52], [4, 3, 54], [0, 0, 1], [0, 1]], ![[44, 0, 26], [35, 18, 1], [1, 7, 55], [19, 4, 52], [10, 30, 56], [55, 49], [17, 66, 41]], ![[0, 1], [61, 31, 1], [63, 8, 19], [66, 65, 30], [49, 34, 24], [17, 18, 66], [44, 0, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63, 34], []]
 b := ![[], [37, 29, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [23, 49, 6, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-613720, -1003727, -326089]
  a := ![1, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9160, -14981, -4867]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![13, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![13, 1, 0]] 
 ![![71, 0, 0], ![13, 1, 0], ![10, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![13, 1, 0], ![-1, 14, 3], ![469, 76, 12]]]
  hmulB := by decide  
  f := ![![![-606, 8315, 1782], ![71, -42174, 0]], ![![-121, 1511, 324], ![72, -7668, 0]], ![![-87, 1171, 251], ![19, -5940, 0]]]
  g := ![![![1, 0, 0], ![-13, 71, 0], ![-10, 0, 71]], ![![0, 1, 0], ![-3, 14, 3], ![-9, 76, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-12, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-12, 1, 0]] 
 ![![71, 0, 0], ![59, 1, 0], ![3, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-12, 1, 0], ![-1, -11, 3], ![469, 76, -13]]]
  hmulB := by decide  
  f := ![![![-1612, -17876, 4875], ![71, -115375, 0]], ![![-1337, -14851, 4050], ![72, -95850, 0]], ![![-60, -756, 206], ![51, -4875, 0]]]
  g := ![![![1, 0, 0], ![-59, 71, 0], ![-3, 0, 71]], ![![-1, 1, 0], ![9, -11, 3], ![-56, 76, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-1, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-1, 1, 0]] 
 ![![71, 0, 0], ![70, 1, 0], ![47, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-1, 1, 0], ![-1, 0, 3], ![469, 76, -2]]]
  hmulB := by decide  
  f := ![![![-4898, -1, 14700], ![71, -347900, 0]], ![![-4828, -1, 14490], ![72, -342930, 0]], ![![-3242, -1, 9731], ![71, -230300, 0]]]
  g := ![![![1, 0, 0], ![-70, 71, 0], ![-47, 0, 71]], ![![-1, 1, 0], ![-2, 0, 3], ![-67, 76, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![13, 1, 0]] ![![71, 0, 0], ![-12, 1, 0]]
  ![![71, 0, 0], ![-76, -23, 1]] where
 M := ![![![5041, 0, 0], ![-852, 71, 0]], ![![923, 71, 0], ![-157, 2, 3]]]
 hmul := by decide  
 g := ![![![![71, 0, 0], ![0, 0, 0]], ![![64, 24, -1], ![71, 0, 0]]], ![![![13, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-76, -23, 1]] ![![71, 0, 0], ![-1, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-71, 71, 0]], ![![-5396, -1633, 71], ![568, 0, -71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-1, 1, 0]]], ![![![-76, -23, 1]], ![![8, 0, -1]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-34, -39, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-34, -39, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![39, 34, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-34, -39, 1], ![508, 3, -118], ![-18629, -2833, 82]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -34, 73]], ![![-1, -1, 1], ![70, 55, -118], ![-299, -77, 82]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [4, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 72], [0, 1]]
 g := ![![[25, 55], [46], [9], [8, 65], [72], [1]], ![[0, 18], [46], [9], [5, 8], [72], [1]]]
 h' := ![![[46, 72], [23, 36], [39, 22], [41, 70], [20, 24], [69, 46], [0, 1]], ![[0, 1], [0, 37], [29, 51], [49, 3], [29, 49], [68, 27], [46, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [66, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [4, 27, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4661, 7530, 2901]
  a := ![-2, 3, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1486, -1248, 2901]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-28, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-28, 1, 0]] 
 ![![73, 0, 0], ![45, 1, 0], ![64, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-28, 1, 0], ![-1, -27, 3], ![469, 76, -29]]]
  hmulB := by decide  
  f := ![![![612, 16497, -1833], ![0, 44603, 0]], ![![377, 10152, -1128], ![1, 27448, 0]], ![![540, 14463, -1607], ![9, 39104, 0]]]
  g := ![![![1, 0, 0], ![-45, 73, 0], ![-64, 0, 73]], ![![-1, 1, 0], ![14, -27, 3], ![-15, 76, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-34, -39, 1]] ![![73, 0, 0], ![-28, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-2044, 73, 0]], ![![-2482, -2847, 73], ![1460, 1095, -146]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-28, 1, 0]]], ![![![-34, -39, 1]], ![![20, 15, -2]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-43, 30, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-43, 30, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![36, 30, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-43, 30, 1], ![439, 63, 89], ![13732, 2411, 4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -30, 79]], ![![-1, 0, 1], ![-35, -33, 89], ![172, 29, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [40, 63, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 78], [0, 1]]
 g := ![![[47, 2], [28, 18], [5, 65], [27, 73], [19], [1]], ![[0, 77], [0, 61], [18, 14], [10, 6], [19], [1]]]
 h' := ![![[16, 78], [65, 70], [37, 52], [26, 12], [50, 51], [39, 16], [0, 1]], ![[0, 1], [0, 9], [0, 27], [60, 67], [76, 28], [58, 63], [16, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [66, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [40, 63, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15015, 6785, 1635]
  a := ![0, -5, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-555, -535, 1635]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-10, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-10, 1, 0]] 
 ![![79, 0, 0], ![69, 1, 0], ![75, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-10, 1, 0], ![-1, -9, 3], ![469, 76, -11]]]
  hmulB := by decide  
  f := ![![![-4604, -41536, 13845], ![79, -364585, 0]], ![![-4019, -36271, 12090], ![80, -318370, 0]], ![![-4370, -39433, 13144], ![82, -346125, 0]]]
  g := ![![![1, 0, 0], ![-69, 79, 0], ![-75, 0, 79]], ![![-1, 1, 0], ![5, -9, 3], ![-50, 76, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-43, 30, 1]] ![![79, 0, 0], ![-10, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-790, 79, 0]], ![![-3397, 2370, 79], ![869, -237, 79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-10, 1, 0]]], ![![![-43, 30, 1]], ![![11, -3, 1]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB231I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB231I1 : PrimesBelowBoundCertificateInterval O 31 79 231 where
  m := 11
  g := ![2, 3, 1, 2, 2, 2, 2, 1, 3, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB231I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1]
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
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![71, 71, 71]
    · exact ![5329, 73]
    · exact ![6241, 79]
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
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N0, I41N1, I41N2, I47N1, I53N1, I59N1, I61N1, I71N0, I71N1, I71N2, I73N1, I79N1]
  Il := ![[I37N1], [I41N0, I41N1, I41N2], [], [I47N1], [I53N1], [I59N1], [I61N1], [], [I71N0, I71N1, I71N2], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
