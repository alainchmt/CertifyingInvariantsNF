
import IdealArithmetic.Examples.NF3_1_946979_1.RI3_1_946979_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![389406, -1091437, 1005838]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![389406, -1091437, 1005838]] 
 ![![263, 0, 0], ![0, 263, 0], ![185, 165, 1]] where
  M :=![![![389406, -1091437, 1005838], ![188091706, -3633946, -12005807], ![-204098719, 21464994, -3633946]]]
  hmulB := by decide  
  f := ![![![-1030076573198, -67011724390, -63721456089]], ![![-11915912288643, -775190748842, -737128968290]], ![![-8247988160185, -536573613791, -510227908339]]]
  g := ![![![-706048, -635189, 1005838], ![9160327, 7518343, -12005807], ![1780157, 2361468, -3633946]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 2 2 8 [42, 100, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [163, 262], [0, 1]]
 g := ![![[65, 93], [227, 52], [70, 223], [70], [124], [210], [6], [1]], ![[233, 170], [24, 211], [125, 40], [70], [124], [210], [6], [1]]]
 h' := ![![[163, 262], [197, 206], [216, 29], [160, 111], [101, 99], [7, 85], [197, 173], [221, 163], [0, 1]], ![[0, 1], [111, 57], [209, 234], [106, 152], [195, 164], [186, 178], [255, 90], [227, 100], [163, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [124, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 2
  hpos := by decide
  P := [42, 100, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![416, -91, -93]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![67, 58, -93]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1030076573198, 67011724390, 63721456089]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![1030076573198, 67011724390, 63721456089]] 
 ![![263, 0, 0], ![26, 1, 0], ![82, 0, 1]] where
  M :=![![![1030076573198, 67011724390, 63721456089], ![11915912288643, 775190748842, 737128968290], ![12531192460930, 815217855953, 775190748842]]]
  hmulB := by decide  
  f := ![![![-389406, 1091437, -1005838]], ![![-753674, 121716, -53787]], ![![654629, 258680, -299790]]]
  g := ![![![-22575618480, 67011724390, 63721456089], ![-261154458483, 775190748842, 737128968290], ![-274639213684, 815217855953, 775190748842]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![389406, -1091437, 1005838]] ![![1030076573198, 67011724390, 63721456089]]
  ![![263, 0, 0]] where
 M := ![![![-263, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC263 : ContainsPrimesAboveP 263 ![I263N0, I263N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 263 (by decide) (𝕀 ⊙ MulI263N0)
instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3170436, -206253, -196126]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![-3170436, -206253, -196126]] 
 ![![269, 0, 0], ![10, 1, 0], ![211, 0, 1]] where
  M :=![![![-3170436, -206253, -196126], ![-36675562, -2385932, -2268783], ![-38569311, -2509130, -2385932]]]
  hmulB := by decide  
  f := ![![![-19834, 2416, -667]], ![![-1201, 26, 74]], ![![-13878, 1817, -587]]]
  g := ![![![149720, -206253, -196126], ![1731959, -2385932, -2268783], ![1821389, -2509130, -2385932]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N0 : Nat.card (O ⧸ I269N0) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N0)

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := prime_ideal_of_norm_prime hp269.out _ NI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7824, -509, -484]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![-7824, -509, -484]] 
 ![![269, 0, 0], ![37, 1, 0], ![169, 0, 1]] where
  M :=![![![-7824, -509, -484], ![-90508, -5888, -5599], ![-95183, -6192, -5888]]]
  hmulB := by decide  
  f := ![![![464, 64, -99]], ![![-5, 12, -11]], ![![336, 33, -59]]]
  g := ![![![345, -509, -484], ![3991, -5888, -5599], ![4197, -6192, -5888]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1

def I269N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![230160, -7813, -11490]] i)))

def SI269N2: IdealEqSpanCertificate' Table ![![230160, -7813, -11490]] 
 ![![269, 0, 0], ![222, 1, 0], ![166, 0, 1]] where
  M :=![![![230160, -7813, -11490], ![-2148630, 276120, -85943], ![-1461031, -164078, 276120]]]
  hmulB := by decide  
  f := ![![![-62140898846, -4042581780, -3844091459]], ![![-53955853705, -3510102930, -3337757262]], ![![-41157442384, -2677501127, -2546036116]]]
  g := ![![![14394, -7813, -11490], ![-182828, 276120, -85943], ![-40415, -164078, 276120]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N2 : Nat.card (O ⧸ I269N2) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N2)

lemma isPrimeI269N2 : Ideal.IsPrime I269N2 := prime_ideal_of_norm_prime hp269.out _ NI269N2
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![-3170436, -206253, -196126]] ![![-7824, -509, -484]]
  ![![62140898846, 4042581780, 3844091459]] where
 M := ![![![62140898846, 4042581780, 3844091459]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI269N1 : IdealMulLeCertificate' Table 
  ![![62140898846, 4042581780, 3844091459]] ![![230160, -7813, -11490]]
  ![![269, 0, 0]] where
 M := ![![![-269, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC269 : ContainsPrimesAboveP 269 ![I269N0, I269N1, I269N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
    exact isPrimeI269N1
    exact isPrimeI269N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 269 (by decide) (𝕀 ⊙ MulI269N0 ⊙ MulI269N1)
instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![271, 0, 0]] 
 ![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 3 2 8 [101, 214, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 88, 238], [215, 182, 33], [0, 1]]
 g := ![![[209, 16, 32], [115, 30, 195], [13, 233, 211], [133, 270, 121], [261, 247], [43, 187], [244, 1], []], ![[114, 10, 242, 219], [14, 231, 99, 89], [71, 132, 12, 36], [33, 229, 217, 212], [139, 160], [10, 177], [199, 62], [19, 5]], ![[40, 109, 139, 66], [123, 10, 204, 12], [75, 219, 17, 181], [13, 249, 87, 267], [169, 106], [44, 124], [82, 156], [224, 5]]]
 h' := ![![[29, 88, 238], [38, 140, 158], [42, 111, 174], [117, 135, 32], [47, 247, 11], [11, 161, 104], [17, 257, 244], [0, 0, 1], [0, 1]], ![[215, 182, 33], [168, 58, 17], [240, 72, 92], [159, 210, 14], [230, 228, 84], [155, 224, 65], [262, 95, 155], [6, 262, 182], [29, 88, 238]], ![[0, 1], [55, 73, 96], [170, 88, 5], [100, 197, 225], [29, 67, 176], [266, 157, 102], [153, 190, 143], [24, 9, 88], [215, 182, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [156, 183], []]
 b := ![[], [223, 131, 178], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 3
  hpos := by decide
  P := [101, 214, 27, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![55826, 7046, -10569]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![206, 26, -39]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 19902511 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def PBC271 : ContainsPrimesAboveP 271 ![I271N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI271N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![271, 0, 0]]) timesTableT_eq_Table B_one_repr 271 (by decide) 𝕀



lemma PB276I5_primes (p : ℕ) :
  p ∈ Set.range ![263, 269, 271] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 275 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 275 (by omega)

def PB276I5 : PrimesBelowBoundCertificateInterval O 257 275 276 where
  m := 3
  g := ![2, 3, 1]
  P := ![263, 269, 271]
  hP := PB276I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0, I263N1]
    · exact ![I269N0, I269N1, I269N2]
    · exact ![I271N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC263
    · exact PBC269
    · exact PBC271
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![69169, 263]
    · exact ![269, 269, 269]
    · exact ![19902511]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
      exact NI269N1
      exact NI269N2
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
  β := ![I263N1, I269N0, I269N1, I269N2]
  Il := ![[I263N1], [I269N0, I269N1, I269N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
