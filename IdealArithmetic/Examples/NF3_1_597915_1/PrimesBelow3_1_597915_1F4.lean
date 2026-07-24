
import IdealArithmetic.Examples.NF3_1_597915_1.RI3_1_597915_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-30455176328357530, -464422491770256, 1597704826456215]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-30455176328357530, -464422491770256, 1597704826456215]] 
 ![![197, 0, 0], ![0, 197, 0], ![108, 20, 1]] where
  M :=![![![-30455176328357530, -464422491770256, 1597704826456215], ![272278680340472253, -4687461753912643, -8508494413530693], ![-277531644573284436, 16070390036748873, 1294482849621323]]]
  hmulB := by decide  
  f := ![![![-663284187828635996432653535900, -133385414595545894157208121139, -58074702765484121261833172049]], ![![-10197545002088876524087888662657, -2050710378628503740355441824150, -892859208467914789472165452965]], ![![-1478138249138012867821825535589, -297251294104038443632930706630, -129420301343232373115010919198]]]
  g := ![![![-1030493896373750, -164561010258348, 1597704826456215], ![6046680593917701, 840012317343661, -8508494413530693], ![-2118455798641560, -49843994698871, 1294482849621323]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [80, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [166, 196], [0, 1]]
 g := ![![[190, 39], [193], [137, 109], [85], [154], [178], [166, 1]], ![[163, 158], [193], [107, 88], [85], [154], [178], [135, 196]]]
 h' := ![![[166, 196], [185, 32], [72, 169], [118, 75], [107, 171], [4, 101], [116, 93], [0, 1]], ![[0, 1], [178, 165], [152, 28], [157, 122], [125, 26], [25, 96], [188, 104], [166, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [126]]
 b := ![[], [90, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [80, 31, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2710, 4150, 2276]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1234, -210, 2276]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![663284187828635996432653535900, 133385414595545894157208121139, 58074702765484121261833172049]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![663284187828635996432653535900, 133385414595545894157208121139, 58074702765484121261833172049]] 
 ![![197, 0, 0], ![40, 1, 0], ![130, 0, 1]] where
  M :=![![![663284187828635996432653535900, 133385414595545894157208121139, 58074702765484121261833172049], ![10197545002088876524087888662657, 2050710378628503740355441824150, 892859208467914789472165452965], ![15607642752918316864415275380693, 3138672589606542019600035640098, 1366547296586196617935859441414]]]
  hmulB := by decide  
  f := ![![![30455176328357530, 464422491770256, -1597704826456215]], ![![4801666866973751, 118093205201639, -281216744389431]], ![![21506114554618088, 224896111133931, -1060893960857509]]]
  g := ![![![-62039816017797642304030373990, 133385414595545894157208121139, 58074702765484121261833172049], ![-953820138293808100109194381669, 2050710378628503740355441824150, 892859208467914789472165452965], ![-1459849793845426011427654201051, 3138672589606542019600035640098, 1366547296586196617935859441414]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-30455176328357530, -464422491770256, 1597704826456215]] ![![663284187828635996432653535900, 133385414595545894157208121139, 58074702765484121261833172049]]
  ![![197, 0, 0]] where
 M := ![![![-197, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0]] 
 ![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [198, 49, 68, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 27, 135], [99, 171, 64], [0, 1]]
 g := ![![[32, 137, 90], [142, 72, 89], [166, 1, 161], [72, 193], [128, 20], [85, 47], [1]], ![[85, 131, 44, 163], [178, 129, 181, 74], [68, 113, 39, 186], [136, 128], [62, 56], [190, 46], [178, 104, 12, 138]], ![[40, 31, 137, 184], [113, 190, 101, 117], [41, 156, 80, 178], [71, 72], [143, 40], [83, 9], [149, 108, 38, 61]]]
 h' := ![![[32, 27, 135], [142, 173, 182], [166, 31, 41], [123, 82, 34], [161, 120, 118], [86, 162, 152], [1, 150, 131], [0, 1]], ![[99, 171, 64], [28, 151, 150], [117, 44, 52], [117, 110, 168], [141, 152, 160], [173, 177, 102], [111, 99, 65], [32, 27, 135]], ![[0, 1], [105, 74, 66], [195, 124, 106], [182, 7, 196], [132, 126, 120], [136, 59, 144], [124, 149, 3], [99, 171, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 38], []]
 b := ![[], [132, 38, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [198, 49, 68, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1418671, 668640, 297505]
  a := ![2, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7129, 3360, 1495]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 7880599 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def PBC199 : ContainsPrimesAboveP 199 ![I199N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![199, 0, 0]]) timesTableT_eq_Table B_one_repr 199 (by decide) 𝕀

instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0]] 
 ![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [104, 109, 201, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [163, 103, 11], [58, 107, 200], [0, 1]]
 g := ![![[179, 139, 203], [172, 111, 126], [142, 64], [182, 36], [45, 4, 151], [86, 100], [1]], ![[29, 91, 109, 69], [29, 13, 104, 125], [97, 209], [52, 24], [172, 44, 101, 123], [44, 183], [104, 183, 59, 65]], ![[72, 82, 48, 159], [106, 171, 18, 8], [121, 51], [71, 109], [150, 4, 14, 118], [47, 24], [63, 160, 0, 146]]]
 h' := ![![[163, 103, 11], [47, 93, 25], [210, 62, 166], [29, 48, 8], [173, 50, 205], [184, 155, 183], [107, 102, 10], [0, 1]], ![[58, 107, 200], [174, 78, 111], [111, 109, 87], [55, 30, 118], [140, 79, 119], [203, 37, 186], [128, 38, 82], [163, 103, 11]], ![[0, 1], [10, 40, 75], [120, 40, 169], [172, 133, 85], [148, 82, 98], [166, 19, 53], [137, 71, 119], [58, 107, 200]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [160, 48], []]
 b := ![[], [184, 155, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [104, 109, 201, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-393713216987, -89565833875, -33185869844]
  a := ![-129, -193, -452]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1865939417, -424482625, -157279004]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def PBC211 : ContainsPrimesAboveP 211 ![I211N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![211, 0, 0]]) timesTableT_eq_Table B_one_repr 211 (by decide) 𝕀



lemma PB219I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 218 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 218 (by omega)

def PB219I4 : PrimesBelowBoundCertificateInterval O 193 218 219 where
  m := 3
  g := ![2, 1, 1]
  P := ![197, 199, 211]
  hP := PB219I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0]
    · exact ![I211N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![7880599]
    · exact ![9393931]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
  β := ![I197N1]
  Il := ![[I197N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
