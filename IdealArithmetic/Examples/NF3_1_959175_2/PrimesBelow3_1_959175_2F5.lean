
import IdealArithmetic.Examples.NF3_1_959175_2.RI3_1_959175_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![33, 1, 0]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0], ![33, 1, 0]] 
 ![![263, 0, 0], ![33, 1, 0], ![103, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![33, 1, 0], ![-5, 31, 13], ![185, -8, 35]]]
  hmulB := by decide  
  f := ![![![-6453, 40426, 16952], ![-526, -342952, 0]], ![![-815, 5053, 2119], ![1, -42869, 0]], ![![-2535, 15832, 6639], ![-144, -134312, 0]]]
  g := ![![![1, 0, 0], ![-33, 263, 0], ![-103, 0, 263]], ![![0, 1, 0], ![-9, 31, 13], ![-12, -8, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N0 : Nat.card (O ⧸ I263N0) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N0)

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := prime_ideal_of_norm_prime hp263.out _ NI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![101, 1, 0]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![263, 0, 0], ![101, 1, 0]] 
 ![![263, 0, 0], ![101, 1, 0], ![242, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![101, 1, 0], ![-5, 99, 13], ![185, -8, 103]]]
  hmulB := by decide  
  f := ![![![97439, -2153362, -282750], ![29456, 5720250, 0]], ![![37417, -826891, -108576], ![11310, 2196576, 0]], ![![89714, -1981420, -260173], ![26960, 5263500, 0]]]
  g := ![![![1, 0, 0], ![-101, 263, 0], ![-242, 0, 263]], ![![0, 1, 0], ![-50, 99, 13], ![-91, -8, 103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1

def I263N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![129, 1, 0]] i)))

def SI263N2: IdealEqSpanCertificate' Table ![![263, 0, 0], ![129, 1, 0]] 
 ![![263, 0, 0], ![129, 1, 0], ![196, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![129, 1, 0], ![-5, 127, 13], ![185, -8, 131]]]
  hmulB := by decide  
  f := ![![![143527, -4320746, -442260], ![54178, 8947260, 0]], ![![70401, -2119223, -216918], ![26564, 4388418, 0]], ![![106916, -3220024, -329593], ![40472, 6667920, 0]]]
  g := ![![![1, 0, 0], ![-129, 263, 0], ![-196, 0, 263]], ![![0, 1, 0], ![-72, 127, 13], ![-93, -8, 131]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N2 : Nat.card (O ⧸ I263N2) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N2)

lemma isPrimeI263N2 : Ideal.IsPrime I263N2 := prime_ideal_of_norm_prime hp263.out _ NI263N2
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![33, 1, 0]] ![![263, 0, 0], ![101, 1, 0]]
  ![![263, 0, 0], ![-7, -91, 1]] where
 M := ![![![69169, 0, 0], ![26563, 263, 0]], ![![8679, 263, 0], ![3328, 132, 13]]]
 hmul := by decide  
 g := ![![![![263, 0, 0], ![0, 0, 0]], ![![101, 1, 0], ![0, 0, 0]]], ![![![33, 1, 0], ![0, 0, 0]], ![![13, 5, 0], ![13, 0, 0]]]]
 hle2 := by decide  

def MulI263N1 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![-7, -91, 1]] ![![263, 0, 0], ![129, 1, 0]]
  ![![263, 0, 0]] where
 M := ![![![69169, 0, 0], ![33927, 263, 0]], ![![-1841, -23933, 263], ![-263, -11572, -1052]]]
 hmul := by decide  
 g := ![![![![263, 0, 0]], ![![129, 1, 0]]], ![![![-7, -91, 1]], ![![-1, -44, -4]]]]
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


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [207, 119, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 59, 88], [137, 209, 181], [0, 1]]
 g := ![![[127, 204, 9], [73, 66], [61, 29, 125], [153, 118, 93], [208, 180], [98, 202], [210, 1], []], ![[29, 160, 169, 194], [132, 149], [49, 107, 5, 72], [64, 121, 24, 141], [216, 208], [263, 224], [170, 103], [28, 212]], ![[32, 83, 251, 104], [127, 30], [45, 244, 248, 210], [188, 81, 92, 157], [64, 105], [219, 96], [196, 253], [204, 212]]]
 h' := ![![[73, 59, 88], [209, 257, 3], [16, 118, 214], [71, 258, 177], [180, 198, 239], [255, 180, 51], [108, 89, 134], [0, 0, 1], [0, 1]], ![[137, 209, 181], [84, 232, 109], [152, 130, 234], [268, 204, 248], [130, 130, 125], [69, 238, 137], [248, 73, 61], [71, 134, 209], [73, 59, 88]], ![[0, 1], [11, 49, 157], [163, 21, 90], [219, 76, 113], [203, 210, 174], [1, 120, 81], [224, 107, 74], [213, 135, 59], [137, 209, 181]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [190, 166], []]
 b := ![[], [84, 63, 261], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [207, 119, 59, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4667688, 645331, -314730]
  a := ![5, 1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17352, 2399, -1170]
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

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0], ![-8, -117, 1]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![271, 0, 0], ![-8, -117, 1]] 
 ![![271, 0, 0], ![0, 271, 0], ![263, 154, 1]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]], ![![-8, -117, 1], ![770, 218, -1519], ![-21585, 949, -249]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-263, -154, 271]], ![![-1, -1, 1], ![1477, 864, -1519], ![162, 145, -249]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 2 2 8 [202, 151, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 270], [0, 1]]
 g := ![![[96, 229], [157, 124], [236, 195], [24, 35], [136], [74], [37], [1]], ![[205, 42], [132, 147], [59, 76], [159, 236], [136], [74], [37], [1]]]
 h' := ![![[120, 270], [264, 59], [24, 128], [30, 174], [242, 72], [237, 223], [268, 133], [69, 120], [0, 1]], ![[0, 1], [27, 212], [208, 143], [43, 97], [210, 199], [168, 48], [239, 138], [106, 151], [120, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [258]]
 b := ![[], [119, 129]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 2
  hpos := by decide
  P := [202, 151, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-24341, 14978, -3021]
  a := ![-12, -7, 31]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2842, 1772, -3021]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0], ![-107, 1, 0]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![271, 0, 0], ![-107, 1, 0]] 
 ![![271, 0, 0], ![164, 1, 0], ![249, 0, 1]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]], ![![-107, 1, 0], ![-5, -109, 13], ![185, -8, -105]]]
  hmulB := by decide  
  f := ![![![251757, 6146356, -733018], ![-76422, 15280606, 0]], ![![152314, 3719469, -443586], ![-46340, 9247062, 0]], ![![231301, 5647390, -673511], ![-70264, 14040114, 0]]]
  g := ![![![1, 0, 0], ![-164, 271, 0], ![-249, 0, 271]], ![![-1, 1, 0], ![54, -109, 13], ![102, -8, -105]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![271, 0, 0], ![-8, -117, 1]] ![![271, 0, 0], ![-107, 1, 0]]
  ![![271, 0, 0]] where
 M := ![![![73441, 0, 0], ![-28997, 271, 0]], ![![-2168, -31707, 271], ![1626, 12737, -1626]]]
 hmul := by decide  
 g := ![![![![271, 0, 0]], ![![-107, 1, 0]]], ![![![-8, -117, 1]], ![![6, 47, -6]]]]
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


def P277P0 : CertificateIrreducibleZModOfList' 277 3 2 8 [60, 144, 121, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [272, 45, 118], [161, 231, 159], [0, 1]]
 g := ![![[254, 146, 120], [157, 255], [168, 2, 189], [121, 117], [202, 246, 57], [138, 62], [156, 1], []], ![[31, 63, 117, 158], [119, 55], [85, 211, 162, 246], [248, 222], [214, 70, 39, 226], [37, 210], [29, 177], [4, 74]], ![[149, 103, 133, 77], [109, 87], [207, 5, 52, 227], [108, 191], [97, 34, 257, 158], [202, 270], [108, 86], [240, 74]]]
 h' := ![![[272, 45, 118], [28, 125, 216], [169, 15, 55], [134, 75, 110], [68, 109, 35], [70, 110, 210], [58, 190, 93], [0, 0, 1], [0, 1]], ![[161, 231, 159], [53, 3, 105], [180, 36, 71], [208, 158, 189], [31, 16, 172], [75, 269, 273], [165, 197, 137], [62, 74, 231], [272, 45, 118]], ![[0, 1], [177, 149, 233], [247, 226, 151], [56, 44, 255], [89, 152, 70], [144, 175, 71], [195, 167, 47], [164, 203, 45], [161, 231, 159]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84, 79], []]
 b := ![[], [66, 70, 166], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 3
  hpos := by decide
  P := [60, 144, 121, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-362248395380, 34820113814, -11759379341]
  a := ![197, 67, -525]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1307755940, 125704382, -42452633]
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
  g := ![3, 1, 2, 1]
  P := ![263, 269, 271, 277]
  hP := PB278I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0, I263N1, I263N2]
    · exact ![I269N0]
    · exact ![I271N0, I271N1]
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
    · exact ![73441, 271]
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
      exact NI271N1
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
  β := ![I263N0, I263N1, I263N2, I271N1]
  Il := ![[I263N0, I263N1, I263N2], [], [I271N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
