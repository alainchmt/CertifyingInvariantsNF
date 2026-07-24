
import IdealArithmetic.Examples.NF3_1_936091_2.RI3_1_936091_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![93, -88, 1]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0], ![93, -88, 1]] 
 ![![263, 0, 0], ![0, 263, 0], ![93, 175, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![93, -88, 1], ![278, -116, -441], ![-9024, 2931, 149]]]
  hmulB := by decide  
  f := ![![![-92, 88, -1], ![263, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-93, -175, 263]], ![![0, -1, 1], ![157, 293, -441], ![-87, -88, 149]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 2 2 8 [225, 252, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 262], [0, 1]]
 g := ![![[201, 173], [197, 6], [151, 18], [32], [48], [24], [121], [1]], ![[0, 90], [0, 257], [86, 245], [32], [48], [24], [121], [1]]]
 h' := ![![[11, 262], [122, 228], [215, 100], [124, 196], [111, 177], [172, 171], [256, 63], [38, 11], [0, 1]], ![[0, 1], [0, 35], [0, 163], [176, 67], [217, 86], [212, 92], [160, 200], [159, 252], [11, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [210]]
 b := ![[], [80, 105]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 2
  hpos := by decide
  P := [225, 252, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2575, -1065, -2065]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![740, 1370, -2065]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![-85, 1, 0]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![263, 0, 0], ![-85, 1, 0]] 
 ![![263, 0, 0], ![178, 1, 0], ![114, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![-85, 1, 0], ![-2, -83, 5], ![102, -33, -86]]]
  hmulB := by decide  
  f := ![![![-46525, -2029627, 122265], ![7364, -6431139, 0]], ![![-31482, -1373586, 82745], ![4998, -4352387, 0]], ![![-20105, -879763, 52997], ![3383, -2787642, 0]]]
  g := ![![![1, 0, 0], ![-178, 263, 0], ![-114, 0, 263]], ![![-1, 1, 0], ![54, -83, 5], ![60, -33, -86]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![93, -88, 1]] ![![263, 0, 0], ![-85, 1, 0]]
  ![![263, 0, 0]] where
 M := ![![![69169, 0, 0], ![-22355, 263, 0]], ![![24459, -23144, 263], ![-7627, 7364, -526]]]
 hmul := by decide  
 g := ![![![![263, 0, 0]], ![![-85, 1, 0]]], ![![![93, -88, 1]], ![![-29, 28, -2]]]]
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

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![89, -76, 1]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![269, 0, 0], ![89, -76, 1]] 
 ![![269, 0, 0], ![0, 269, 0], ![89, 193, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![89, -76, 1], ![254, -96, -381], ![-7800, 2535, 133]]]
  hmulB := by decide  
  f := ![![![-88, 76, -1], ![269, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-89, -193, 269]], ![![0, -1, 1], ![127, 273, -381], ![-73, -86, 133]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 2 2 8 [214, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [261, 268], [0, 1]]
 g := ![![[83, 44], [115], [252, 189], [127, 172], [66], [57], [64], [1]], ![[0, 225], [115], [85, 80], [96, 97], [66], [57], [64], [1]]]
 h' := ![![[261, 268], [113, 115], [141, 121], [260, 171], [55, 21], [27, 55], [89, 222], [55, 261], [0, 1]], ![[0, 1], [0, 154], [249, 148], [237, 98], [156, 248], [125, 214], [196, 47], [119, 8], [261, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [197]]
 b := ![[], [125, 233]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 2
  hpos := by decide
  P := [214, 8, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1825, 2308, -4660]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1535, 3352, -4660]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![112, 1, 0]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![269, 0, 0], ![112, 1, 0]] 
 ![![269, 0, 0], ![112, 1, 0], ![136, 0, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![112, 1, 0], ![-2, 114, 5], ![102, -33, 111]]]
  hmulB := by decide  
  f := ![![![126757, -7793357, -341810], ![23941, 18389378, 0]], ![![52780, -3244705, -142310], ![9954, 7656278, 0]], ![![64072, -3940136, -172811], ![12136, 9297232, 0]]]
  g := ![![![1, 0, 0], ![-112, 269, 0], ![-136, 0, 269]], ![![0, 1, 0], ![-50, 114, 5], ![-42, -33, 111]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![269, 0, 0], ![89, -76, 1]] ![![269, 0, 0], ![112, 1, 0]]
  ![![269, 0, 0]] where
 M := ![![![72361, 0, 0], ![30128, 269, 0]], ![![23941, -20444, 269], ![10222, -8608, -269]]]
 hmul := by decide  
 g := ![![![![269, 0, 0]], ![![112, 1, 0]]], ![![![89, -76, 1]], ![![38, -32, -1]]]]
 hle2 := by decide  


def PBC269 : ContainsPrimesAboveP 269 ![I269N0, I269N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
    exact isPrimeI269N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 269 (by decide) (𝕀 ⊙ MulI269N0)
instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0], ![13, -63, 1]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![271, 0, 0], ![13, -63, 1]] 
 ![![271, 0, 0], ![0, 271, 0], ![13, 208, 1]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]], ![![13, -63, 1], ![228, -146, -316], ![-6474, 2106, 44]]]
  hmulB := by decide  
  f := ![![![-12, 63, -1], ![271, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -208, 271]], ![![0, -1, 1], ![16, 242, -316], ![-26, -26, 44]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 2 2 8 [222, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [224, 270], [0, 1]]
 g := ![![[82, 62], [81, 195], [208, 57], [183, 225], [114], [28], [41], [1]], ![[149, 209], [130, 76], [239, 214], [177, 46], [114], [28], [41], [1]]]
 h' := ![![[224, 270], [175, 182], [165, 97], [24, 190], [75, 256], [73, 83], [74, 242], [49, 224], [0, 1]], ![[0, 1], [22, 89], [213, 174], [37, 81], [238, 15], [237, 188], [82, 29], [90, 47], [224, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [105, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 2
  hpos := by decide
  P := [222, 47, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3295818, -619224, -1244772]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![71874, 953112, -1244772]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0], ![45, 1, 0]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![271, 0, 0], ![45, 1, 0]] 
 ![![271, 0, 0], ![45, 1, 0], ![227, 0, 1]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]], ![![45, 1, 0], ![-2, 47, 5], ![102, -33, 44]]]
  hmulB := by decide  
  f := ![![![125536, -2989237, -318000], ![10027, 17235600, 0]], ![![20805, -496327, -52800], ![1898, 2861760, 0]], ![![105182, -2503899, -266369], ![8229, 14437200, 0]]]
  g := ![![![1, 0, 0], ![-45, 271, 0], ![-227, 0, 271]], ![![0, 1, 0], ![-12, 47, 5], ![-31, -33, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![271, 0, 0], ![13, -63, 1]] ![![271, 0, 0], ![45, 1, 0]]
  ![![271, 0, 0]] where
 M := ![![![73441, 0, 0], ![12195, 271, 0]], ![![3523, -17073, 271], ![813, -2981, -271]]]
 hmul := by decide  
 g := ![![![![271, 0, 0]], ![![45, 1, 0]]], ![![![13, -63, 1]], ![![3, -11, -1]]]]
 hle2 := by decide  


def PBC271 : ContainsPrimesAboveP 271 ![I271N0, I271N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI271N0
    exact isPrimeI271N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 271 (by decide) (𝕀 ⊙ MulI271N0)


lemma PB274I5_primes (p : ℕ) :
  p ∈ Set.range ![263, 269, 271] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 273 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 273 (by omega)

def PB274I5 : PrimesBelowBoundCertificateInterval O 257 273 274 where
  m := 3
  g := ![2, 2, 2]
  P := ![263, 269, 271]
  hP := PB274I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0, I263N1]
    · exact ![I269N0, I269N1]
    · exact ![I271N0, I271N1]
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
    · exact ![72361, 269]
    · exact ![73441, 271]
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
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
  β := ![I263N1, I269N1, I271N1]
  Il := ![[I263N1], [I269N1], [I271N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
