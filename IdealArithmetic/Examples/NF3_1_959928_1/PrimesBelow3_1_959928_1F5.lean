
import IdealArithmetic.Examples.NF3_1_959928_1.RI3_1_959928_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![71, 1, 0]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0], ![71, 1, 0]] 
 ![![263, 0, 0], ![71, 1, 0], ![74, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![71, 1, 0], ![0, 72, 2], ![246, 48, 71]]]
  hmulB := by decide  
  f := ![![![7456, 105, 0], ![-27615, 0, 0]], ![![1988, 28, 0], ![-7363, 0, 0]], ![![1998, -8, -1], ![-7400, 132, 0]]]
  g := ![![![1, 0, 0], ![-71, 263, 0], ![-74, 0, 263]], ![![0, 1, 0], ![-20, 72, 2], ![-32, 48, 71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N0 : Nat.card (O ⧸ I263N0) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N0)

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := prime_ideal_of_norm_prime hp263.out _ NI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![-51, 1, 0]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![263, 0, 0], ![-51, 1, 0]] 
 ![![263, 0, 0], ![212, 1, 0], ![40, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![-51, 1, 0], ![0, -50, 2], ![246, 48, -51]]]
  hmulB := by decide  
  f := ![![![6427, -126, 0], ![33138, 0, 0]], ![![5254, -103, 0], ![27090, 0, 0]], ![![1076, 4, -1], ![5548, 132, 0]]]
  g := ![![![1, 0, 0], ![-212, 263, 0], ![-40, 0, 263]], ![![-1, 1, 0], ![40, -50, 2], ![-30, 48, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1

def I263N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![-21, 1, 0]] i)))

def SI263N2: IdealEqSpanCertificate' Table ![![263, 0, 0], ![-21, 1, 0]] 
 ![![263, 0, 0], ![242, 1, 0], ![53, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![-21, 1, 0], ![0, -20, 2], ![246, 48, -21]]]
  hmulB := by decide  
  f := ![![![5083, -242, 0], ![63646, 0, 0]], ![![4684, -223, 0], ![58650, 0, 0]], ![![1051, -40, -1], ![13160, 132, 0]]]
  g := ![![![1, 0, 0], ![-242, 263, 0], ![-53, 0, 263]], ![![-1, 1, 0], ![18, -20, 2], ![-39, 48, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N2 : Nat.card (O ⧸ I263N2) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N2)

lemma isPrimeI263N2 : Ideal.IsPrime I263N2 := prime_ideal_of_norm_prime hp263.out _ NI263N2
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![71, 1, 0]] ![![263, 0, 0], ![-51, 1, 0]]
  ![![263, 0, 0], ![-101, -121, 1]] where
 M := ![![![69169, 0, 0], ![-13413, 263, 0]], ![![18673, 263, 0], ![-3621, 21, 2]]]
 hmul := by decide  
 g := ![![![![263, 0, 0], ![0, 0, 0]], ![![50, 122, -1], ![263, 0, 0]]], ![![![71, 1, 0], ![0, 0, 0]], ![![88, 122, -1], ![265, 0, 0]]]]
 hle2 := by decide  

def MulI263N1 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![-101, -121, 1]] ![![263, 0, 0], ![-21, 1, 0]]
  ![![263, 0, 0]] where
 M := ![![![69169, 0, 0], ![-5523, 263, 0]], ![![-26563, -31823, 263], ![2367, 2367, -263]]]
 hmul := by decide  
 g := ![![![![263, 0, 0]], ![![-21, 1, 0]]], ![![![-101, -121, 1]], ![![9, 9, -1]]]]
 hle2 := by decide  


def PBC263 : ContainsPrimesAboveP 263 ![I263N0, I263N1, I263N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
    exact isPrimeI263N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 263 (by decide) (𝕀 ⊙ MulI263N0 ⊙ MulI263N1)
instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![269, 0, 0]] 
 ![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [116, 103, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [228, 229, 85], [20, 39, 184], [0, 1]]
 g := ![![[165, 187, 232], [105, 149], [212, 57, 70], [67, 76, 120], [92, 87], [123, 188], [248, 1], []], ![[258, 90, 147, 234], [168, 212], [6, 188, 24, 206], [216, 31, 8, 7], [201, 196], [158, 57], [68, 176], [185, 231]], ![[266, 183, 254, 110], [40, 119], [229, 17, 14, 147], [17, 45, 167, 42], [240, 176], [75, 215], [154, 255], [86, 231]]]
 h' := ![![[228, 229, 85], [51, 142, 140], [156, 100, 35], [29, 198, 173], [154, 205, 89], [214, 33, 25], [15, 164, 69], [0, 0, 1], [0, 1]], ![[20, 39, 184], [173, 262, 45], [232, 41, 181], [163, 49, 174], [93, 185, 183], [153, 183, 14], [171, 246, 222], [127, 200, 39], [228, 229, 85]], ![[0, 1], [257, 134, 84], [18, 128, 53], [77, 22, 191], [147, 148, 266], [77, 53, 230], [256, 128, 247], [108, 69, 229], [20, 39, 184]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [192, 133], []]
 b := ![[], [38, 53, 163], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [116, 103, 21, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1260265, -419371, -66712]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4685, -1559, -248]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 19465109 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def PBC269 : ContainsPrimesAboveP 269 ![I269N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![269, 0, 0]]) timesTableT_eq_Table B_one_repr 269 (by decide) 𝕀

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


def P271P0 : CertificateIrreducibleZModOfList' 271 3 2 8 [154, 250, 160, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [177, 245, 5], [205, 25, 266], [0, 1]]
 g := ![![[71, 269, 258], [141, 224, 53], [9, 137, 14], [126, 249, 170], [260, 268], [185, 200], [111, 1], []], ![[10, 117, 16, 245], [227, 140, 178, 62], [39, 146, 9, 11], [29, 23, 189, 198], [167, 233], [12, 56], [264, 83], [76, 25]], ![[140, 122, 270, 107], [75, 94, 217, 257], [168, 207, 20, 137], [87, 19, 186, 30], [157, 64], [175, 180], [82, 134], [86, 25]]]
 h' := ![![[177, 245, 5], [237, 49, 23], [240, 240, 253], [108, 140, 234], [136, 153, 250], [135, 78, 214], [250, 9, 147], [0, 0, 1], [0, 1]], ![[205, 25, 266], [127, 230, 7], [36, 6, 208], [111, 256, 46], [183, 57, 240], [183, 136, 49], [26, 247, 197], [113, 195, 25], [177, 245, 5]], ![[0, 1], [165, 263, 241], [212, 25, 81], [215, 146, 262], [265, 61, 52], [253, 57, 8], [153, 15, 198], [55, 76, 245], [205, 25, 266]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [243, 115], []]
 b := ![[], [228, 158, 248], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 3
  hpos := by decide
  P := [154, 250, 160, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2125995, 1239283, 273168]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7845, 4573, 1008]
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

instance hp277 : Fact (Nat.Prime 277) := {out := by norm_num}

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 0, 0]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![277, 0, 0]] 
 ![![277, 0, 0], ![0, 277, 0], ![0, 0, 277]] where
  M :=![![![277, 0, 0], ![0, 277, 0], ![0, 0, 277]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 3 2 8 [61, 134, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [236, 174, 169], [30, 102, 108], [0, 1]]
 g := ![![[37, 132, 243], [91, 10], [259, 173, 7], [25, 267], [106, 47, 88], [183, 169], [266, 1], []], ![[271, 90, 256, 267], [113, 187], [256, 206, 107, 165], [251, 264], [92, 118, 68, 12], [151, 76], [75, 155], [35, 30]], ![[204, 1, 189, 194], [197, 196], [182, 104, 3, 228], [153, 192], [262, 117, 99, 187], [79, 52], [10, 83], [96, 30]]]
 h' := ![![[236, 174, 169], [89, 203, 215], [267, 56, 29], [21, 136, 227], [182, 84, 199], [33, 252, 229], [117, 28, 264], [0, 0, 1], [0, 1]], ![[30, 102, 108], [247, 118, 6], [40, 226, 234], [248, 215, 156], [18, 118, 146], [136, 152, 20], [162, 55, 82], [100, 264, 102], [236, 174, 169]], ![[0, 1], [164, 233, 56], [47, 272, 14], [108, 203, 171], [85, 75, 209], [59, 150, 28], [13, 194, 208], [30, 13, 174], [30, 102, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 148], []]
 b := ![[], [231, 130, 145], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 3
  hpos := by decide
  P := [61, 134, 11, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-227694, -34071, -21883]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-822, -123, -79]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 21253933 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def PBC277 : ContainsPrimesAboveP 277 ![I277N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI277N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![277, 0, 0]]) timesTableT_eq_Table B_one_repr 277 (by decide) 𝕀



lemma PB278I5_primes (p : ℕ) :
  p ∈ Set.range ![263, 269, 271, 277] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 277 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 277 (by omega)

def PB278I5 : PrimesBelowBoundCertificateInterval O 257 277 278 where
  m := 4
  g := ![3, 1, 1, 1]
  P := ![263, 269, 271, 277]
  hP := PB278I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0, I263N1, I263N2]
    · exact ![I269N0]
    · exact ![I271N0]
    · exact ![I277N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC263
    · exact PBC269
    · exact PBC271
    · exact PBC277
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![263, 263, 263]
    · exact ![19465109]
    · exact ![19902511]
    · exact ![21253933]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
      exact NI263N2
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
  β := ![I263N0, I263N1, I263N2]
  Il := ![[I263N0, I263N1, I263N2], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
