
import IdealArithmetic.Examples.NF3_1_936684_4.RI3_1_936684_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0]] 
 ![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 3 2 8 [85, 136, 168, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 137, 222], [59, 125, 41], [0, 1]]
 g := ![![[145, 142, 39], [210, 166, 124], [168, 120, 221], [56, 253], [110, 138], [57, 179], [95, 1], []], ![[140, 212, 86, 258], [257, 76, 245, 143], [234, 207, 149, 96], [105, 122], [194, 11], [102, 23], [102, 108], [129, 103]], ![[27, 237, 18, 120], [248, 120, 204, 246], [217, 100, 120, 154], [185, 24], [193, 95], [137, 1], [19, 96], [47, 103]]]
 h' := ![![[36, 137, 222], [34, 234, 202], [185, 238, 85], [66, 62, 241], [108, 17, 76], [187, 179, 140], [78, 145, 210], [0, 0, 1], [0, 1]], ![[59, 125, 41], [205, 214, 139], [84, 75, 78], [145, 23, 231], [172, 152, 124], [57, 151, 167], [171, 139, 54], [62, 134, 125], [36, 137, 222]], ![[0, 1], [221, 78, 185], [256, 213, 100], [41, 178, 54], [182, 94, 63], [67, 196, 219], [107, 242, 262], [12, 129, 137], [59, 125, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135, 114], []]
 b := ![[], [105, 183, 99], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 3
  hpos := by decide
  P := [85, 136, 168, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-93365, 5786, 5786]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-355, 22, 22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 18191447 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def PBC263 : ContainsPrimesAboveP 263 ![I263N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![263, 0, 0]]) timesTableT_eq_Table B_one_repr 263 (by decide) 𝕀

instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![12, 74, 1]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![269, 0, 0], ![12, 74, 1]] 
 ![![269, 0, 0], ![0, 269, 0], ![12, 74, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![12, 74, 1], ![350, 96, 74], ![25900, 6566, 96]]]
  hmulB := by decide  
  f := ![![![-11, -74, -1], ![269, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -74, 269]], ![![0, 0, 1], ![-2, -20, 74], ![92, -2, 96]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 2 2 8 [122, 176, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 268], [0, 1]]
 g := ![![[72, 89], [52], [206, 120], [130, 70], [169], [249], [41], [1]], ![[10, 180], [52], [68, 149], [184, 199], [169], [249], [41], [1]]]
 h' := ![![[93, 268], [156, 147], [154, 66], [11, 89], [6, 96], [218, 256], [198, 220], [147, 93], [0, 1]], ![[0, 1], [108, 122], [105, 203], [218, 180], [57, 173], [85, 13], [214, 49], [188, 176], [93, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [266]]
 b := ![[], [137, 133]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 2
  hpos := by decide
  P := [122, 176, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4253, 1794, 1282]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-73, -346, 1282]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![-74, 1, 0]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![269, 0, 0], ![-74, 1, 0]] 
 ![![269, 0, 0], ![195, 1, 0], ![173, 0, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![-74, 1, 0], ![0, -74, 1], ![350, 84, -74]]]
  hmulB := by decide  
  f := ![![![4293, -58, 0], ![15602, 0, 0]], ![![3183, -43, 0], ![11568, 0, 0]], ![![2833, -38, 0], ![10296, 1, 0]]]
  g := ![![![1, 0, 0], ![-195, 269, 0], ![-173, 0, 269]], ![![-1, 1, 0], ![53, -74, 1], ![-12, 84, -74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![269, 0, 0], ![12, 74, 1]] ![![269, 0, 0], ![-74, 1, 0]]
  ![![269, 0, 0]] where
 M := ![![![72361, 0, 0], ![-19906, 269, 0]], ![![3228, 19906, 269], ![-538, -5380, 0]]]
 hmul := by decide  
 g := ![![![![269, 0, 0]], ![![-74, 1, 0]]], ![![![12, 74, 1]], ![![-2, -20, 0]]]]
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

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![271, 0, 0]] 
 ![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 3 2 8 [70, 80, 89, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [166, 144, 243], [16, 126, 28], [0, 1]]
 g := ![![[137, 4, 64], [138, 73, 219], [266, 171, 180], [225, 31, 252], [202, 50], [17, 53], [182, 1], []], ![[145, 170, 72, 132], [134, 135, 56, 216], [208, 129, 21, 235], [247, 58, 10, 222], [261, 166], [184, 229], [156, 158], [208, 242]], ![[121, 88, 18, 122], [51, 2, 122, 129], [89, 147, 47, 268], [181, 143, 108, 238], [116, 174], [193, 55], [133, 140], [152, 242]]]
 h' := ![![[166, 144, 243], [96, 118, 263], [79, 23, 225], [239, 84, 198], [147, 22, 184], [174, 55, 62], [268, 4, 253], [0, 0, 1], [0, 1]], ![[16, 126, 28], [268, 186, 24], [113, 37, 64], [154, 0, 103], [236, 8, 75], [159, 92, 39], [64, 25, 59], [259, 136, 126], [166, 144, 243]], ![[0, 1], [233, 238, 255], [67, 211, 253], [2, 187, 241], [122, 241, 12], [58, 124, 170], [254, 242, 230], [185, 135, 144], [16, 126, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63, 179], []]
 b := ![[], [122, 47, 229], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 3
  hpos := by decide
  P := [70, 80, 89, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![135500, -56368, -15989]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![500, -208, -59]
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



lemma PB274I5_primes (p : ℕ) :
  p ∈ Set.range ![263, 269, 271] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 273 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 273 (by omega)

def PB274I5 : PrimesBelowBoundCertificateInterval O 257 273 274 where
  m := 3
  g := ![1, 2, 1]
  P := ![263, 269, 271]
  hP := PB274I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0]
    · exact ![I269N0, I269N1]
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
    · exact ![18191447]
    · exact ![72361, 269]
    · exact ![19902511]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
      exact NI269N1
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
  β := ![I269N1]
  Il := ![[], [I269N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
