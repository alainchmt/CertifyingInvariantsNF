
import IdealArithmetic.Examples.NF3_1_314847_3.RI3_1_314847_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0]] 
 ![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [60, 55, 117, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 65, 73], [1, 73, 66], [0, 1]]
 g := ![![[90, 47, 81], [121, 25, 89], [132, 81], [81, 48, 64], [71, 5], [22, 1], []], ![[81, 9, 34, 70], [82, 70, 50, 50], [129, 113], [98, 128, 56, 27], [15, 79], [97, 47], [99, 47]], ![[17, 105, 127, 116], [87, 102, 84, 44], [90, 129], [53, 35, 73, 107], [113, 52], [45, 55], [106, 47]]]
 h' := ![![[21, 65, 73], [107, 135, 130], [28, 102, 28], [5, 138, 130], [84, 85, 131], [70, 120, 12], [0, 0, 1], [0, 1]], ![[1, 73, 66], [30, 71, 24], [125, 102, 38], [130, 127, 104], [130, 43, 61], [125, 38, 45], [61, 25, 73], [21, 65, 73]], ![[0, 1], [66, 72, 124], [137, 74, 73], [106, 13, 44], [28, 11, 86], [54, 120, 82], [35, 114, 65], [1, 73, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 78], []]
 b := ![[], [24, 106, 77], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [60, 55, 117, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-632867, -2363, 14178]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4553, -17, 102]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![24, -7, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![24, -7, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![24, 142, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![24, -7, 1], ![97, 40, -27], ![-717, -33, 26]]]
  hmulB := by decide  
  f := ![![![-23, 7, -1], ![149, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -142, 149]], ![![0, -1, 1], ![5, 26, -27], ![-9, -25, 26]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [41, 131, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 148], [0, 1]]
 g := ![![[25, 81], [82], [20, 24], [113], [136, 33], [26], [1]], ![[142, 68], [82], [5, 125], [113], [134, 116], [26], [1]]]
 h' := ![![[18, 148], [28, 9], [74, 126], [81, 60], [86, 115], [19, 35], [108, 18], [0, 1]], ![[0, 1], [41, 140], [107, 23], [118, 89], [70, 34], [53, 114], [134, 131], [18, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108]]
 b := ![[], [110, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [41, 131, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1261, 672, 1394]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-233, -1324, 1394]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![27, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![27, 1, 0]] 
 ![![149, 0, 0], ![27, 1, 0], ![123, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![27, 1, 0], ![2, 26, 4], ![111, 9, 28]]]
  hmulB := by decide  
  f := ![![![15502, 211663, 32568], ![4321, -1213158, 0]], ![![2788, 38344, 5900], ![895, -219775, 0]], ![![12810, 174729, 26885], ![3495, -1001466, 0]]]
  g := ![![![1, 0, 0], ![-27, 149, 0], ![-123, 0, 149]], ![![0, 1, 0], ![-8, 26, 4], ![-24, 9, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![24, -7, 1]] ![![149, 0, 0], ![27, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![4023, 149, 0]], ![![3576, -1043, 149], ![745, -149, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![27, 1, 0]]], ![![![24, -7, 1]], ![![5, -1, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [71, 38, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [143, 61, 44], [135, 89, 107], [0, 1]]
 g := ![![[15, 34, 34], [66, 76, 38], [99, 111, 4], [90, 25], [111, 72, 128], [127, 1], []], ![[88, 134, 84, 64], [30, 71, 11, 103], [146, 38, 56, 31], [81, 64], [37, 123, 130, 127], [55, 69], [127, 124]], ![[97, 106, 134, 24], [80, 96, 104, 142], [85, 86, 48, 26], [7, 18], [66, 113, 24, 149], [69, 97], [64, 124]]]
 h' := ![![[143, 61, 44], [146, 42, 100], [68, 69, 75], [38, 14, 2], [122, 69, 5], [43, 86, 85], [0, 0, 1], [0, 1]], ![[135, 89, 107], [91, 18, 27], [142, 36, 47], [140, 30, 39], [105, 35, 8], [145, 124, 24], [107, 41, 89], [143, 61, 44]], ![[0, 1], [118, 91, 24], [51, 46, 29], [147, 107, 110], [77, 47, 138], [60, 92, 42], [91, 110, 61], [135, 89, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 49], []]
 b := ![[], [137, 101, 119], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [71, 38, 24, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1141158642, -175952599, -54798504]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7557342, -1165249, -362904]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-37, 66, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-37, 66, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![120, 66, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-37, 66, 1], ![243, -94, 265], ![7386, 624, 38]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-120, -66, 157]], ![![-1, 0, 1], ![-201, -112, 265], ![18, -12, 38]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [117, 152, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 156], [0, 1]]
 g := ![![[59, 51], [27], [119, 30], [112, 111], [63, 90], [25], [1]], ![[0, 106], [27], [112, 127], [39, 46], [42, 67], [25], [1]]]
 h' := ![![[5, 156], [126, 69], [50, 59], [84, 40], [8, 41], [88, 54], [40, 5], [0, 1]], ![[0, 1], [0, 88], [31, 98], [127, 117], [56, 116], [44, 103], [65, 152], [5, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [112]]
 b := ![[], [17, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [117, 152, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1591, 2367, -585]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![437, 261, -585]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![49, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![49, 1, 0]] 
 ![![157, 0, 0], ![49, 1, 0], ![119, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![49, 1, 0], ![2, 48, 4], ![111, 9, 50]]]
  hmulB := by decide  
  f := ![![![12938, 358663, 29892], ![6437, -1173261, 0]], ![![4027, 111923, 9328], ![2042, -366124, 0]], ![![9814, 271853, 22657], ![4855, -889287, 0]]]
  g := ![![![1, 0, 0], ![-49, 157, 0], ![-119, 0, 157]], ![![0, 1, 0], ![-18, 48, 4], ![-40, 9, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-37, 66, 1]] ![![157, 0, 0], ![49, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![7693, 157, 0]], ![![-5809, 10362, 157], ![-1570, 3140, 314]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![49, 1, 0]]], ![![![-37, 66, 1]], ![![-10, 20, 2]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)


lemma PB159I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 158 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 158 (by omega)

def PB159I3 : PrimesBelowBoundCertificateInterval O 137 158 159 where
  m := 4
  g := ![1, 2, 1, 2]
  P := ![139, 149, 151, 157]
  hP := PB159I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
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
    · exact ![2685619]
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![24649, 157]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
  β := ![I149N1, I157N1]
  Il := ![[], [I149N1], [], [I157N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
