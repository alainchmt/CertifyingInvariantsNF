
import IdealArithmetic.Examples.NF3_1_692259_1.RI3_1_692259_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [34, 1, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 26], [8, 10], [0, 1]]
 g := ![![[17, 36, 34], [11, 34], [34, 12, 4], [22, 1], []], ![[7, 10, 7], [6, 33], [24, 5, 3], [36, 26], []], ![[2, 28, 33], [24, 7], [16, 20, 30], [30, 10], []]]
 h' := ![![[14, 26], [3, 13, 21], [28, 29, 16], [29, 18, 2], [0, 0, 1], [0, 1]], ![[8, 10], [9, 12, 25], [18, 7, 12], [7, 0, 20], [11, 25, 10], [14, 26]], ![[0, 1], [8, 12, 28], [26, 1, 9], [5, 19, 15], [27, 12, 26], [8, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13], []]
 b := ![[], [24, 17, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [34, 1, 15, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-129981, 45954, -12765]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3513, 1242, -345]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 5, 3]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![83, 5, 3]] 
 ![![41, 0, 0], ![0, 41, 0], ![14, 29, 1]] where
  M :=![![![83, 5, 3], ![457, 30, 18], ![1094, 58, 43]]]
  hmulB := by decide  
  f := ![![![6, -1, 0]], ![![1, 7, -3]], ![![-1, 5, -2]]]
  g := ![![![1, -2, 3], ![5, -12, 18], ![12, -29, 43]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [40, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 40], [0, 1]]
 g := ![![[3, 40], [23], [32], [33, 9], [1]], ![[0, 1], [23], [32], [19, 32], [1]]]
 h' := ![![[3, 40], [14, 9], [14, 33], [33, 27], [1, 3], [0, 1]], ![[0, 1], [0, 32], [31, 8], [32, 14], [10, 38], [3, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [16, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [40, 38, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5498, 4039, -709]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![108, 600, -709]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-6, 1, 0]] 
 ![![41, 0, 0], ![35, 1, 0], ![13, 0, 1]] where
  M :=![![![-6, 1, 0], ![-1, -7, 3], ![154, -16, -5]]]
  hmulB := by decide  
  f := ![![![-83, -5, -3]], ![![-82, -5, -3]], ![![-53, -3, -2]]]
  g := ![![![-1, 1, 0], ![5, -7, 3], ![19, -16, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![83, 5, 3]] ![![-6, 1, 0]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![11, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![11, 1, 0]] 
 ![![43, 0, 0], ![11, 1, 0], ![6, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![11, 1, 0], ![-1, 10, 3], ![154, -16, 12]]]
  hmulB := by decide  
  f := ![![![-159, 1600, 480], ![0, -6880, 0]], ![![-40, 400, 120], ![1, -1720, 0]], ![![-25, 223, 67], ![11, -960, 0]]]
  g := ![![![1, 0, 0], ![-11, 43, 0], ![-6, 0, 43]], ![![0, 1, 0], ![-3, 10, 3], ![6, -16, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-58186815961, -3447220784, -2186942506]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-58186815961, -3447220784, -2186942506]] 
 ![![43, 0, 0], ![15, 1, 0], ![30, 0, 1]] where
  M :=![![![-58186815961, -3447220784, -2186942506], ![-333341925140, -19748515081, -12528604858], ![-767061791384, -45443822732, -28829899155]]]
  hmulB := by decide  
  f := ![![![-624499, 191128, -35686]], ![![-350099, 60983, 56]], ![![159178, 24052, -22527]]]
  g := ![![![1375110953, -3447220784, -2186942506], ![7877766205, -19748515081, -12528604858], ![18127733122, -45443822732, -28829899155]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![17, 1, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0], ![17, 1, 0]] 
 ![![43, 0, 0], ![17, 1, 0], ![38, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![17, 1, 0], ![-1, 16, 3], ![154, -16, 18]]]
  hmulB := by decide  
  f := ![![![1466, -23713, -4446], ![43, 63726, 0]], ![![568, -9361, -1755], ![44, 25155, 0]], ![![1290, -20956, -3929], ![52, 56316, 0]]]
  g := ![![![1, 0, 0], ![-17, 43, 0], ![-38, 0, 43]], ![![0, 1, 0], ![-9, 16, 3], ![-6, -16, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![11, 1, 0]] ![![-58186815961, -3447220784, -2186942506]]
  ![![43, 0, 0], ![26, -6, 1]] where
 M := ![![![-2502033086323, -148230493712, -94038527758]], ![![-973396900711, -57667943705, -36584972424]]]
 hmul := by decide  
 g := ![![![![-43021561623, -6946894862, -1603663493], ![-25080997559, 0, 0]]], ![![![-16737210617, -2702636495, -623893058], ![-9757570930, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![26, -6, 1]] ![![43, 0, 0], ![17, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![731, 43, 0]], ![![1118, -258, 43], ![602, -86, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![17, 1, 0]]], ![![![26, -6, 1]], ![![14, -2, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [29, 12, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 2, 16], [45, 44, 31], [0, 1]]
 g := ![![[6, 4, 36], [44, 40, 9], [42, 2, 1], [38, 12, 1], []], ![[41, 23, 25, 27], [3, 31, 11, 14], [28, 3, 13, 9], [16, 25, 2, 3], [34, 21]], ![[28, 18, 35, 44], [35, 37, 40, 19], [44, 13, 32, 46], [22, 11, 38, 30], [19, 21]]]
 h' := ![![[14, 2, 16], [40, 20, 41], [4, 20, 3], [26, 42, 1], [0, 0, 1], [0, 1]], ![[45, 44, 31], [31, 25, 9], [29, 24, 29], [12, 16, 11], [9, 26, 44], [14, 2, 16]], ![[0, 1], [39, 2, 44], [15, 3, 15], [6, 36, 35], [17, 21, 2], [45, 44, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 21], []]
 b := ![[], [41, 27, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [29, 12, 35, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1690104067, 444907640, -113212660]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-35959661, 9466120, -2408780]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![20, -23, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![20, -23, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![20, 30, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![20, -23, 1], ![177, 27, -68], ![-3434, 414, -18]]]
  hmulB := by decide  
  f := ![![![-19, 23, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -30, 53]], ![![0, -1, 1], ![29, 39, -68], ![-58, 18, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [5, 42, 1] where
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
 g := ![![[19, 10], [47], [], [47], [11, 1]], ![[23, 43], [47], [], [47], [22, 52]]]
 h' := ![![[11, 52], [30, 40], [0, 43], [34], [51, 10], [0, 1]], ![[0, 1], [46, 13], [49, 10], [34], [2, 43], [11, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [19, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [5, 42, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2820, 4144, -1360]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![460, 848, -1360]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![15, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![15, 1, 0]] 
 ![![53, 0, 0], ![15, 1, 0], ![18, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![15, 1, 0], ![-1, 14, 3], ![154, -16, 16]]]
  hmulB := by decide  
  f := ![![![676, -9661, -2070], ![53, 36570, 0]], ![![180, -2731, -585], ![54, 10335, 0]], ![![231, -3281, -703], ![13, 12420, 0]]]
  g := ![![![1, 0, 0], ![-15, 53, 0], ![-18, 0, 53]], ![![0, 1, 0], ![-5, 14, 3], ![2, -16, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![20, -23, 1]] ![![53, 0, 0], ![15, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![795, 53, 0]], ![![1060, -1219, 53], ![477, -318, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![15, 1, 0]]], ![![![20, -23, 1]], ![![9, -6, -1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-18, 9, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-18, 9, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![41, 9, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-18, 9, 1], ![145, -43, 28], ![1494, -98, -24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -9, 59]], ![![-1, 0, 1], ![-17, -5, 28], ![42, 2, -24]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [51, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 58], [0, 1]]
 g := ![![[25, 22], [11, 25], [19], [27, 36], [23, 1]], ![[0, 37], [55, 34], [19], [29, 23], [46, 58]]]
 h' := ![![[23, 58], [29, 9], [21, 54], [39, 14], [7, 6], [0, 1]], ![[0, 1], [0, 50], [24, 5], [7, 45], [27, 53], [23, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [46, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [51, 36, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1060, 414, -249]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![191, 45, -249]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-28, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-28, 1, 0]] 
 ![![59, 0, 0], ![31, 1, 0], ![24, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-28, 1, 0], ![-1, -29, 3], ![154, -16, -27]]]
  hmulB := by decide  
  f := ![![![-1719, -49880, 5160], ![0, -101480, 0]], ![![-902, -26187, 2709], ![1, -53277, 0]], ![![-676, -20291, 2099], ![49, -41280, 0]]]
  g := ![![![1, 0, 0], ![-31, 59, 0], ![-24, 0, 59]], ![![-1, 1, 0], ![14, -29, 3], ![22, -16, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-18, 9, 1]] ![![59, 0, 0], ![-28, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1652, 59, 0]], ![![-1062, 531, 59], ![649, -295, 0]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-28, 1, 0]]], ![![![-18, 9, 1]], ![![11, -5, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-3, -12, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-3, -12, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![58, 49, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-3, -12, 1], ![166, -7, -35], ![-1740, 238, -30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-58, -49, 61]], ![![-1, -1, 1], ![36, 28, -35], ![0, 28, -30]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [16, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 60], [0, 1]]
 g := ![![[22, 42], [52], [60, 5], [6, 9], [14, 1]], ![[0, 19], [52], [8, 56], [10, 52], [28, 60]]]
 h' := ![![[14, 60], [34, 15], [16, 33], [26, 35], [20, 58], [0, 1]], ![[0, 1], [0, 46], [51, 28], [28, 26], [39, 3], [14, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [38, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [16, 47, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23550, -1082, 1056]
  a := ![-1, 18, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-618, -866, 1056]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-26, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-26, 1, 0]] 
 ![![61, 0, 0], ![35, 1, 0], ![30, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-26, 1, 0], ![-1, -27, 3], ![154, -16, -25]]]
  hmulB := by decide  
  f := ![![![433, 10961, -1218], ![61, 24766, 0]], ![![259, 6263, -696], ![62, 14152, 0]], ![![204, 5391, -599], ![9, 12180, 0]]]
  g := ![![![1, 0, 0], ![-35, 61, 0], ![-30, 0, 61]], ![![-1, 1, 0], ![14, -27, 3], ![24, -16, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-3, -12, 1]] ![![61, 0, 0], ![-26, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1586, 61, 0]], ![![-183, -732, 61], ![244, 305, -61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-26, 1, 0]]], ![![![-3, -12, 1]], ![![4, 5, -1]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-18, -26, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-18, -26, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![49, 41, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-18, -26, 1], ![180, -8, -77], ![-3896, 462, -59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -41, 67]], ![![-1, -1, 1], ![59, 47, -77], ![-15, 43, -59]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [33, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 66], [0, 1]]
 g := ![![[61, 65], [53, 40], [29], [29], [9], [1]], ![[0, 2], [0, 27], [29], [29], [9], [1]]]
 h' := ![![[64, 66], [60, 20], [62, 43], [58, 30], [55, 37], [34, 64], [0, 1]], ![[0, 1], [0, 47], [0, 24], [35, 37], [11, 30], [43, 3], [64, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [18, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [33, 3, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3179, 1252, -244]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![131, 168, -244]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![10, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![10, 1, 0]] 
 ![![67, 0, 0], ![10, 1, 0], ![59, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![10, 1, 0], ![-1, 9, 3], ![154, -16, 11]]]
  hmulB := by decide  
  f := ![![![-281, 2538, 846], ![0, -18894, 0]], ![![-42, 378, 126], ![1, -2814, 0]], ![![-247, 2235, 745], ![-3, -16638, 0]]]
  g := ![![![1, 0, 0], ![-10, 67, 0], ![-59, 0, 67]], ![![0, 1, 0], ![-4, 9, 3], ![-5, -16, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-18, -26, 1]] ![![67, 0, 0], ![10, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![670, 67, 0]], ![![-1206, -1742, 67], ![0, -268, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![10, 1, 0]]], ![![![-18, -26, 1]], ![![0, -4, -1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![22, -33, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![22, -33, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![22, 38, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![22, -33, 1], ![187, 39, -98], ![-4974, 574, -26]]]
  hmulB := by decide  
  f := ![![![-21, 33, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -38, 71]], ![![0, -1, 1], ![33, 53, -98], ![-62, 22, -26]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [57, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 70], [0, 1]]
 g := ![![[21, 5], [69, 57], [43, 20], [4], [29], [1]], ![[0, 66], [0, 14], [30, 51], [4], [29], [1]]]
 h' := ![![[10, 70], [43, 17], [34, 25], [5, 34], [34, 2], [14, 10], [0, 1]], ![[0, 1], [0, 54], [0, 46], [61, 37], [54, 69], [43, 61], [10, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [21, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [57, 61, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1978, 1790, -207]
  a := ![-2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![92, 136, -207]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![27, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![27, 1, 0]] 
 ![![71, 0, 0], ![27, 1, 0], ![26, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![27, 1, 0], ![-1, 26, 3], ![154, -16, 28]]]
  hmulB := by decide  
  f := ![![![674, -18201, -2100], ![71, 49700, 0]], ![![239, -6917, -798], ![72, 18886, 0]], ![![251, -6665, -769], ![15, 18200, 0]]]
  g := ![![![1, 0, 0], ![-27, 71, 0], ![-26, 0, 71]], ![![0, 1, 0], ![-11, 26, 3], ![-2, -16, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![22, -33, 1]] ![![71, 0, 0], ![27, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![1917, 71, 0]], ![![1562, -2343, 71], ![781, -852, -71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![27, 1, 0]]], ![![![22, -33, 1]], ![![11, -12, -1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-35, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-35, 1, 0]] 
 ![![73, 0, 0], ![38, 1, 0], ![42, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-35, 1, 0], ![-1, -36, 3], ![154, -16, -34]]]
  hmulB := by decide  
  f := ![![![536, 17999, -1500], ![73, 36500, 0]], ![![296, 9359, -780], ![74, 18980, 0]], ![![294, 10356, -863], ![12, 21000, 0]]]
  g := ![![![1, 0, 0], ![-38, 73, 0], ![-42, 0, 73]], ![![-1, 1, 0], ![17, -36, 3], ![30, -16, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-3, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-3, 1, 0]] 
 ![![73, 0, 0], ![70, 1, 0], ![20, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-3, 1, 0], ![-1, -4, 3], ![154, -16, -2]]]
  hmulB := by decide  
  f := ![![![-263, -1056, 792], ![0, -19272, 0]], ![![-252, -1012, 759], ![1, -18469, 0]], ![![-70, -290, 217], ![50, -5280, 0]]]
  g := ![![![1, 0, 0], ![-70, 73, 0], ![-20, 0, 73]], ![![-1, 1, 0], ![3, -4, 3], ![18, -16, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-35, 1, 0]] ![![73, 0, 0], ![-35, 1, 0]]
  ![![73, 0, 0], ![43, 25, 1]] where
 M := ![![![5329, 0, 0], ![-2555, 73, 0]], ![![-2555, 73, 0], ![1224, -71, 3]]]
 hmul := by decide  
 g := ![![![![30, -25, -1], ![73, 0, 0]], ![![-35, 1, 0], ![0, 0, 0]]], ![![![-35, 1, 0], ![0, 0, 0]], ![![-28, -27, -1], ![76, 0, 0]]]]
 hle2 := by decide  
def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![43, 25, 1]] ![![73, 0, 0], ![-3, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-219, 73, 0]], ![![3139, 1825, 73], ![0, -73, 73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-3, 1, 0]]], ![![![43, 25, 1]], ![![0, -1, 1]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N0
    exact isPrimeI73N1
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [3, 17, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 14, 13], [60, 64, 66], [0, 1]]
 g := ![![[21, 71, 19], [10, 3, 18], [51, 5, 1], [2, 67, 64], [76, 1], []], ![[65, 67, 26, 8], [28, 49, 11, 76], [41, 18, 4, 22], [49, 27, 3, 16], [55, 67], [15, 11]], ![[50, 65, 35, 59], [55, 29], [57, 10, 23, 30], [73, 41, 37, 12], [67, 38], [41, 11]]]
 h' := ![![[16, 14, 13], [49, 4, 16], [5, 23, 27], [73, 4, 1], [9, 48, 71], [0, 0, 1], [0, 1]], ![[60, 64, 66], [13, 9, 49], [66, 60, 52], [32, 58, 37], [37, 24, 33], [53, 2, 64], [16, 14, 13]], ![[0, 1], [68, 66, 14], [69, 75], [77, 17, 41], [37, 7, 54], [1, 77, 14], [60, 64, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74, 32], []]
 b := ![[], [1, 38, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [3, 17, 3, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-674897, 181700, -48585]
  a := ![0, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8543, 2300, -615]
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



lemma PB236I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB236I1 : PrimesBelowBoundCertificateInterval O 31 79 236 where
  m := 11
  g := ![1, 2, 3, 1, 2, 2, 2, 2, 2, 3, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB236I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N0, I73N1]
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
    · exact ![1681, 41]
    · exact ![43, 43, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
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
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
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
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I41N1, I43N0, I43N1, I43N2, I53N1, I59N1, I61N1, I67N1, I71N1, I73N0, I73N1]
  Il := ![[], [I41N1], [I43N0, I43N1, I43N2], [], [I53N1], [I59N1], [I61N1], [I67N1], [I71N1], [I73N0, I73N0, I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
