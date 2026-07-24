
import IdealArithmetic.Examples.NF3_1_311116_1.RI3_1_311116_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![550885, -71426, 659]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![550885, -71426, 659]] 
 ![![139, 0, 0], ![0, 139, 0], ![61, 123, 1]] where
  M :=![![![550885, -71426, 659], ![-143106, 404079, -429215], ![-7751571, 441077, 618357]]]
  hmulB := by decide  
  f := ![![![3159582322, 319837675, 218639011]], ![![24572526213, 2487423606, 1700387039]], ![![23289462526, 2357541848, 1611600691]]]
  g := ![![![3674, -1097, 659], ![187331, 382716, -429215], ![-327132, -544006, 618357]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [46, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 138], [0, 1]]
 g := ![![[113, 136], [14, 122], [45], [27, 96], [65], [106], [1]], ![[0, 3], [115, 17], [45], [29, 43], [65], [106], [1]]]
 h' := ![![[84, 138], [51, 54], [96, 119], [9, 36], [51, 97], [20, 64], [93, 84], [0, 1]], ![[0, 1], [0, 85], [84, 20], [114, 103], [137, 42], [114, 75], [60, 55], [84, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [31, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [46, 55, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1405, 805, -754]
  a := ![-4, -3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![341, 673, -754]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3159582322, 319837675, 218639011]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![3159582322, 319837675, 218639011]] 
 ![![139, 0, 0], ![97, 1, 0], ![68, 0, 1]] where
  M :=![![![3159582322, 319837675, 218639011], ![24572526213, 2487423606, 1700387039], ![22080045273, 2235115159, 1527910581]]]
  hmulB := by decide  
  f := ![![![550885, -71426, 659]], ![![383401, -46937, -2628]], ![![213731, -31769, 4771]]]
  g := ![![![-307425359, 319837675, 218639011], ![-2390891239, 2487423606, 1700387039], ![-2148374422, 2235115159, 1527910581]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![550885, -71426, 659]] ![![3159582322, 319837675, 218639011]]
  ![![139, 0, 0]] where
 M := ![![![139, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [120, 138, 114, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 95, 7], [68, 53, 142], [0, 1]]
 g := ![![[4, 117, 82], [113, 127], [1, 125, 132], [135, 103], [49, 41, 148], [35, 1], []], ![[131, 33], [38, 42], [118, 12, 138, 107], [58, 112], [39, 15, 71, 85], [129, 127], [65, 49]], ![[35, 145, 115, 22], [17, 144], [27, 71, 129, 143], [72, 104], [12, 135, 101, 69], [76, 85], [79, 49]]]
 h' := ![![[116, 95, 7], [95, 60, 23], [29, 24, 96], [34, 69, 70], [80, 128, 111], [121, 116, 44], [0, 0, 1], [0, 1]], ![[68, 53, 142], [63, 18], [2, 117, 41], [19, 126, 21], [107, 137, 74], [52, 27, 15], [143, 38, 53], [116, 95, 7]], ![[0, 1], [65, 71, 126], [67, 8, 12], [56, 103, 58], [59, 33, 113], [114, 6, 90], [61, 111, 95], [68, 53, 142]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [145, 90], []]
 b := ![[], [8, 85, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [120, 138, 114, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2560118, -3576, -13112]
  a := ![5, 3, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17182, -24, -88]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀

instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [5, 63, 66, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [83, 127, 32], [2, 23, 119], [0, 1]]
 g := ![![[74, 34, 22], [139, 28, 17], [128, 53, 144], [31, 37], [99, 112, 148], [85, 1], []], ![[125, 54, 4, 29], [106, 77, 97, 136], [131, 50, 35, 139], [97, 20], [46, 92, 102, 32], [12, 76], [38, 118]], ![[69, 13, 46, 66], [50, 12, 113, 15], [60, 84, 86, 63], [76, 110], [92, 51, 93, 132], [37, 123], [102, 118]]]
 h' := ![![[83, 127, 32], [60, 100, 18], [115, 113, 116], [99, 124, 139], [109, 27, 43], [28, 76, 65], [0, 0, 1], [0, 1]], ![[2, 23, 119], [139, 73, 141], [19, 21, 93], [67, 6, 68], [34, 67, 41], [96, 68, 1], [55, 129, 23], [83, 127, 32]], ![[0, 1], [61, 129, 143], [82, 17, 93], [77, 21, 95], [149, 57, 67], [57, 7, 85], [98, 22, 127], [2, 23, 119]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120, 35], []]
 b := ![[], [51, 95, 98], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [5, 63, 66, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13652366171, 1152072922, -444313574]
  a := ![-130, -65, -196]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-90413021, 7629622, -2942474]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def PBC151 : ContainsPrimesAboveP 151 ![I151N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![151, 0, 0]]) timesTableT_eq_Table B_one_repr 151 (by decide) 𝕀

instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [38, 81, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [155, 120, 111], [136, 36, 46], [0, 1]]
 g := ![![[124, 125, 145], [35, 101], [102, 81, 132], [45, 133, 64], [1, 124, 58], [134, 1], []], ![[76, 53, 0, 126], [16, 100], [106, 39, 155, 31], [145, 24, 82, 81], [147, 107, 112, 130], [6, 40], [109, 75]], ![[4, 143, 142, 105], [106, 113], [78, 53, 66, 12], [26, 73, 78, 99], [108, 156, 107, 33], [71, 113], [17, 75]]]
 h' := ![![[155, 120, 111], [129, 66, 50], [49, 96, 27], [17, 124, 17], [119, 145, 149], [89, 98, 134], [0, 0, 1], [0, 1]], ![[136, 36, 46], [23, 24, 20], [72, 53, 10], [73, 31, 89], [120, 62, 107], [82, 25, 2], [101, 87, 36], [155, 120, 111]], ![[0, 1], [111, 67, 87], [34, 8, 120], [51, 2, 51], [127, 107, 58], [77, 34, 21], [109, 70, 120], [136, 36, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89, 74], []]
 b := ![[], [42, 52, 104], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [38, 81, 23, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4015903, 418091, -138003]
  a := ![-6, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-25579, 2663, -879]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def PBC157 : ContainsPrimesAboveP 157 ![I157N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![157, 0, 0]]) timesTableT_eq_Table B_one_repr 157 (by decide) 𝕀



lemma PB158I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 157 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 157 (by omega)

def PB158I3 : PrimesBelowBoundCertificateInterval O 137 157 158 where
  m := 4
  g := ![2, 1, 1, 1]
  P := ![139, 149, 151, 157]
  hP := PB158I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0]
    · exact ![I157N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![3307949]
    · exact ![3442951]
    · exact ![3869893]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
  β := ![I139N1]
  Il := ![[I139N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
