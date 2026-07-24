
import IdealArithmetic.Examples.NF3_1_948300_2.RI3_1_948300_2
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


def P263P0 : CertificateIrreducibleZModOfList' 263 3 2 8 [57, 192, 120, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 206, 135], [142, 56, 128], [0, 1]]
 g := ![![[203, 197, 206], [208, 38, 36], [44, 79, 66], [33, 24], [102, 4], [60, 36], [143, 1], []], ![[127, 182, 115, 142], [36, 116, 221, 30], [75, 159, 88, 130], [187, 83], [6, 147], [41, 11], [164, 243], [235, 78]], ![[33, 77, 152, 222], [117, 154, 138, 69], [242, 175, 183, 244], [148, 235], [104, 6], [174, 210], [71, 93], [242, 78]]]
 h' := ![![[1, 206, 135], [242, 134, 39], [122, 144, 6], [58, 109, 132], [244, 92, 63], [3, 249, 261], [2, 102, 6], [0, 0, 1], [0, 1]], ![[142, 56, 128], [65, 253, 23], [117, 107, 51], [45, 244, 15], [218, 139, 168], [214, 218, 102], [218, 134, 167], [19, 27, 56], [1, 206, 135]], ![[0, 1], [229, 139, 201], [141, 12, 206], [48, 173, 116], [130, 32, 32], [3, 59, 163], [106, 27, 90], [58, 236, 206], [142, 56, 128]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [210, 146], []]
 b := ![[], [129, 131, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 3
  hpos := by decide
  P := [57, 192, 120, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-314811, 3156, 4734]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1197, 12, 18]
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

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![304116994, -8789594, -5979299]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![304116994, -8789594, -5979299]] 
 ![![269, 0, 0], ![0, 269, 0], ![77, 138, 1]] where
  M :=![![![304116994, -8789594, -5979299], ![-1169132309, 175741420, -20389483], ![-906406756, -528570521, 187341309]]]
  hmulB := by decide  
  f := ![![![82328431286573, 17870391201425, 4572586521578]], ![![882929153549441, 191650552919558, 49038587082697]], ![![487260083738260, 105765750387399, 27062812403762]]]
  g := ![![![2842093, 3034772, -5979299], ![1490178, 11113346, -20389483], ![-56995121, -98073127, 187341309]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 2 2 8 [123, 165, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 268], [0, 1]]
 g := ![![[126, 188], [150], [217, 62], [54, 16], [185], [65], [56], [1]], ![[41, 81], [150], [209, 207], [104, 253], [185], [65], [56], [1]]]
 h' := ![![[104, 268], [214, 69], [209, 42], [83, 84], [135, 4], [264, 202], [171, 146], [146, 104], [0, 1]], ![[0, 1], [127, 200], [4, 227], [211, 185], [13, 265], [21, 67], [22, 123], [202, 165], [104, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [116]]
 b := ![[], [212, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 2
  hpos := by decide
  P := [123, 165, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9195, 3776, 2616]
  a := ![-3, 0, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-783, -1328, 2616]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-82328431286573, -17870391201425, -4572586521578]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![-82328431286573, -17870391201425, -4572586521578]] 
 ![![269, 0, 0], ![125, 1, 0], ![40, 0, 1]] where
  M :=![![![-82328431286573, -17870391201425, -4572586521578], ![-882929153549441, -191650552919558, -49038587082697], ![-2889450126702961, -627190428801602, -160482357038286]]]
  hmulB := by decide  
  f := ![![![-304116994, 8789594, 5979299]], ![![-136972089, 3431070, 2854282]], ![![-41852316, 3271949, 192679]]]
  g := ![![![8677969999088, -17870391201425, -4572586521578], ![93066667080681, -191650552919558, -49038587082697], ![304567463773341, -627190428801602, -160482357038286]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![304116994, -8789594, -5979299]] ![![-82328431286573, -17870391201425, -4572586521578]]
  ![![269, 0, 0]] where
 M := ![![![-269, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P271P0 : CertificateIrreducibleZModOfList' 271 3 2 8 [74, 172, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 217, 54], [210, 53, 217], [0, 1]]
 g := ![![[245, 248, 170], [92, 121, 99], [117, 182, 238], [16, 1, 175], [269, 112], [36, 244], [237, 1], []], ![[55, 43, 232, 260], [186, 109, 191, 108], [161, 197, 78, 102], [210, 53, 36, 107], [26, 67], [35, 25], [218, 99], [172, 206]], ![[204, 95, 149, 80], [87, 164, 186, 50], [125, 88, 56, 205], [182, 33, 184, 213], [157, 233], [14, 185], [7, 206], [9, 206]]]
 h' := ![![[27, 217, 54], [238, 79, 21], [14, 256, 218], [171, 103, 77], [46, 170, 208], [13, 187, 58], [77, 83, 171], [0, 0, 1], [0, 1]], ![[210, 53, 217], [254, 146, 230], [61, 102, 175], [158, 227, 158], [147, 77, 150], [170, 126, 164], [62, 47, 266], [196, 223, 53], [27, 217, 54]], ![[0, 1], [225, 46, 20], [259, 184, 149], [128, 212, 36], [190, 24, 184], [215, 229, 49], [80, 141, 105], [74, 48, 217], [210, 53, 217]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 21], []]
 b := ![[], [166, 53, 105], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 3
  hpos := by decide
  P := [74, 172, 34, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6075507808, -1183085730, -254452740]
  a := ![1, -64, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-22418848, -4365630, -938940]
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
  g := ![1, 2, 1]
  P := ![263, 269, 271]
  hP := PB276I5_primes
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
