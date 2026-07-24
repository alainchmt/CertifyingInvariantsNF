
import IdealArithmetic.Examples.NF3_1_42316_1.RI3_1_42316_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [26, 15, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 26, 15], [0, 10, 22], [0, 1]]
 g := ![![[4, 25, 9], [29, 33], [11, 35, 9], [7, 1], []], ![[26, 4, 6, 31], [8, 9], [35, 32, 0, 24], [34, 26], [24, 3]], ![[0, 1, 2, 23], [30, 3], [30, 29], [33, 10], [17, 3]]]
 h' := ![![[7, 26, 15], [12, 31, 34], [10, 7, 12], [3, 17, 34], [0, 0, 1], [0, 1]], ![[0, 10, 22], [30, 29, 28], [4, 34, 3], [34, 35, 3], [17, 0, 10], [7, 26, 15]], ![[0, 1], [6, 14, 12], [34, 33, 22], [34, 22], [2, 0, 26], [0, 10, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 31], []]
 b := ![[], [23, 7, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [26, 15, 30, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7955, 629, -2442]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![215, 17, -66]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [25, 19, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 38, 28], [32, 2, 13], [0, 1]]
 g := ![![[1, 0, 23], [], [37, 39], [30, 7, 1], []], ![[27, 7, 24, 26], [2, 40], [7, 18], [16, 12, 6, 30], [31, 5]], ![[18, 30, 20, 19], [40, 40], [9, 1], [19, 9, 18, 35], [5, 5]]]
 h' := ![![[16, 38, 28], [4, 13, 8], [39, 7], [29, 34, 11], [0, 0, 1], [0, 1]], ![[32, 2, 13], [37, 0, 11], [28, 20, 32], [30, 8, 31], [14, 10, 2], [16, 38, 28]], ![[0, 1], [27, 28, 22], [17, 14, 9], [18, 40, 40], [38, 31, 38], [32, 2, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 22], []]
 b := ![[], [25, 2, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [25, 19, 34, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![92619, -38540, 6109]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2259, -940, 149]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![17, -15, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![17, -15, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![17, 28, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![17, -15, 1], ![23, 5, -29], ![-557, 193, -10]]]
  hmulB := by decide  
  f := ![![![-16, 15, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -28, 43]], ![![0, -1, 1], ![12, 19, -29], ![-9, 11, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [26, 33, 1] where
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
 g := ![![[36, 4], [38, 36], [25], [7, 14], [1]], ![[33, 39], [11, 7], [25], [18, 29], [1]]]
 h' := ![![[10, 42], [1, 41], [9, 6], [33, 38], [17, 10], [0, 1]], ![[0, 1], [24, 2], [26, 37], [26, 5], [31, 33], [10, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [19, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [26, 33, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-90, 474, -453]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![177, 306, -453]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-14, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-14, 1, 0]] 
 ![![43, 0, 0], ![29, 1, 0], ![10, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-14, 1, 0], ![1, -14, 2], ![38, -12, -13]]]
  hmulB := by decide  
  f := ![![![-85, 1594, -228], ![86, 4902, 0]], ![![-47, 1062, -152], ![87, 3268, 0]], ![![-10, 370, -53], ![50, 1140, 0]]]
  g := ![![![1, 0, 0], ![-29, 43, 0], ![-10, 0, 43]], ![![-1, 1, 0], ![9, -14, 2], ![12, -12, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![17, -15, 1]] ![![43, 0, 0], ![-14, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-602, 43, 0]], ![![731, -645, 43], ![-215, 215, -43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-14, 1, 0]]], ![![![17, -15, 1]], ![![-5, 5, -1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![23, 16, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![23, 16, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![23, 16, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![23, 16, 1], ![54, 11, 33], ![621, -179, 27]]]
  hmulB := by decide  
  f := ![![![-22, -16, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -16, 47]], ![![0, 0, 1], ![-15, -11, 33], ![0, -13, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [19, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 46], [0, 1]]
 g := ![![[45, 34], [27, 24], [1, 4], [36, 34], [1]], ![[21, 13], [46, 23], [12, 43], [12, 13], [1]]]
 h' := ![![[38, 46], [4, 38], [28, 27], [21, 2], [28, 38], [0, 1]], ![[0, 1], [38, 9], [20, 20], [3, 45], [15, 9], [38, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [17, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [19, 9, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![216, -3, -56]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![32, 19, -56]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![14, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![14, 1, 0]] 
 ![![47, 0, 0], ![14, 1, 0], ![20, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![14, 1, 0], ![1, 14, 2], ![38, -12, 15]]]
  hmulB := by decide  
  f := ![![![-1398, -23291, -3330], ![-893, 78255, 0]], ![![-425, -6925, -990], ![-234, 23265, 0]], ![![-594, -9911, -1417], ![-383, 33300, 0]]]
  g := ![![![1, 0, 0], ![-14, 47, 0], ![-20, 0, 47]], ![![0, 1, 0], ![-5, 14, 2], ![-2, -12, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![23, 16, 1]] ![![47, 0, 0], ![14, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![658, 47, 0]], ![![1081, 752, 47], ![376, 235, 47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![14, 1, 0]]], ![![![23, 16, 1]], ![![8, 5, 1]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![212, 13, 15]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![212, 13, 15]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 15, 1]] where
  M :=![![![212, 13, 15], ![583, 32, 41], ![689, 39, 45]]]
  hmulB := by decide  
  f := ![![![-3, 0, 1]], ![![38, -15, 1]], ![![11, -4, 0]]]
  g := ![![![4, -4, 15], ![11, -11, 41], ![13, -12, 45]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [40, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 52], [0, 1]]
 g := ![![[44, 4], [44], [47, 47], [42], [42, 1]], ![[0, 49], [44], [7, 6], [42], [31, 52]]]
 h' := ![![[42, 52], [31, 51], [28, 37], [7, 10], [16, 28], [0, 1]], ![[0, 1], [0, 2], [45, 16], [3, 43], [26, 25], [42, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [3, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [40, 11, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4876, -966, 773]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![92, -237, 773]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, -1]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![3, 0, -1]] 
 ![![53, 0, 0], ![22, 1, 0], ![50, 0, 1]] where
  M :=![![![3, 0, -1], ![-38, 15, -1], ![-13, -13, 15]]]
  hmulB := by decide  
  f := ![![![-212, -13, -15]], ![![-99, -6, -7]], ![![-213, -13, -15]]]
  g := ![![![1, 0, -1], ![-6, 15, -1], ![-9, -13, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![212, 13, 15]] ![![3, 0, -1]]
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


lemma PB59I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 58 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 58 (by omega)

def PB59I1 : PrimesBelowBoundCertificateInterval O 31 58 59 where
  m := 5
  g := ![1, 1, 2, 2, 2]
  P := ![37, 41, 43, 47, 53]
  hP := PB59I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
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
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
  β := ![I43N1, I47N1, I53N1]
  Il := ![[], [], [I43N1], [I47N1], [I53N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
