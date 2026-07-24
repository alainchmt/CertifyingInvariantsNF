
import IdealArithmetic.Examples.NF3_1_960204_2.RI3_1_960204_2
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


def P263P0 : CertificateIrreducibleZModOfList' 263 3 2 8 [142, 23, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 34, 213], [196, 228, 50], [0, 1]]
 g := ![![[170, 180, 4], [129, 178, 124], [73, 24, 176], [36, 111], [34, 128], [9, 136], [252, 1], []], ![[174, 253, 23, 113], [32, 97, 155, 47], [200, 115, 200, 174], [30, 108], [127, 39], [45, 129], [59, 173], [134, 133]], ![[160, 32, 216, 216], [72, 223, 1, 108], [71, 221, 195, 109], [14, 83], [153, 111], [200, 181], [3, 104], [34, 133]]]
 h' := ![![[56, 34, 213], [92, 207, 261], [154, 204, 85], [174, 82, 121], [17, 150, 233], [30, 73, 172], [247, 111, 98], [0, 0, 1], [0, 1]], ![[196, 228, 50], [73, 226, 240], [217, 45, 238], [156, 163, 81], [205, 230, 125], [108, 246, 61], [221, 133, 225], [151, 250, 228], [56, 34, 213]], ![[0, 1], [51, 93, 25], [14, 14, 203], [212, 18, 61], [137, 146, 168], [214, 207, 30], [90, 19, 203], [187, 13, 34], [196, 228, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [151, 151], []]
 b := ![[], [176, 76, 124], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 3
  hpos := by decide
  P := [142, 23, 11, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![55230, 7101, -52074]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![210, 27, -198]
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

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![103, 1, 0]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![269, 0, 0], ![103, 1, 0]] 
 ![![269, 0, 0], ![103, 1, 0], ![174, 0, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![103, 1, 0], ![-1, 102, 3], ![51, -42, 104]]]
  hmulB := by decide  
  f := ![![![9666, -996337, -29304], ![269, 2627592, 0]], ![![3637, -381481, -11220], ![270, 1006060, 0]], ![![6229, -644471, -18955], ![235, 1699632, 0]]]
  g := ![![![1, 0, 0], ![-103, 269, 0], ![-174, 0, 269]], ![![0, 1, 0], ![-41, 102, 3], ![-51, -42, 104]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N0 : Nat.card (O ⧸ I269N0) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N0)

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := prime_ideal_of_norm_prime hp269.out _ NI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![-88, 1, 0]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![269, 0, 0], ![-88, 1, 0]] 
 ![![269, 0, 0], ![181, 1, 0], ![79, 0, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![-88, 1, 0], ![-1, -89, 3], ![51, -42, -87]]]
  hmulB := by decide  
  f := ![![![-32237, -2869182, 96714], ![0, -8672022, 0]], ![![-21690, -1930499, 65073], ![1, -5834879, 0]], ![![-9399, -842623, 28403], ![209, -2546802, 0]]]
  g := ![![![1, 0, 0], ![-181, 269, 0], ![-79, 0, 269]], ![![-1, 1, 0], ![59, -89, 3], ![54, -42, -87]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1

def I269N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![-15, 1, 0]] i)))

def SI269N2: IdealEqSpanCertificate' Table ![![269, 0, 0], ![-15, 1, 0]] 
 ![![269, 0, 0], ![254, 1, 0], ![99, 0, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![-15, 1, 0], ![-1, -16, 3], ![51, -42, -14]]]
  hmulB := by decide  
  f := ![![![-21836, -349392, 65511], ![0, -5874153, 0]], ![![-20618, -329904, 61857], ![1, -5546511, 0]], ![![-8031, -128587, 24110], ![95, -2161863, 0]]]
  g := ![![![1, 0, 0], ![-254, 269, 0], ![-99, 0, 269]], ![![-1, 1, 0], ![14, -16, 3], ![45, -42, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N2 : Nat.card (O ⧸ I269N2) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N2)

lemma isPrimeI269N2 : Ideal.IsPrime I269N2 := prime_ideal_of_norm_prime hp269.out _ NI269N2
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![269, 0, 0], ![103, 1, 0]] ![![269, 0, 0], ![-88, 1, 0]]
  ![![269, 0, 0], ![27, -85, 1]] where
 M := ![![![72361, 0, 0], ![-23672, 269, 0]], ![![27707, 269, 0], ![-9065, 14, 3]]]
 hmul := by decide  
 g := ![![![![242, 85, -1], ![269, 0, 0]], ![![-88, 1, 0], ![0, 0, 0]]], ![![![76, 86, -1], ![269, 0, 0]], ![![-34, 1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI269N1 : IdealMulLeCertificate' Table 
  ![![269, 0, 0], ![27, -85, 1]] ![![269, 0, 0], ![-15, 1, 0]]
  ![![269, 0, 0]] where
 M := ![![![72361, 0, 0], ![-4035, 269, 0]], ![![7263, -22865, 269], ![-269, 1345, -269]]]
 hmul := by decide  
 g := ![![![![269, 0, 0]], ![![-15, 1, 0]]], ![![![27, -85, 1]], ![![-1, 5, -1]]]]
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


def P271P0 : CertificateIrreducibleZModOfList' 271 3 2 8 [78, 104, 131, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 235, 145], [111, 35, 126], [0, 1]]
 g := ![![[17, 17, 252], [105, 174, 160], [28, 77, 144], [111, 93, 140], [166, 88], [196, 256], [140, 1], []], ![[158, 259, 130, 21], [250, 107, 155, 24], [227, 22, 249, 182], [181, 124, 72, 269], [158, 100], [140, 155], [236, 141], [27, 158]], ![[192, 69, 101, 258], [192, 250, 31, 4], [182, 36, 46, 225], [160, 219, 80, 174], [152, 98], [249, 35], [126, 212], [46, 158]]]
 h' := ![![[29, 235, 145], [211, 154, 87], [255, 221, 206], [14, 148, 259], [104, 191, 127], [55, 125, 140], [191, 267, 255], [0, 0, 1], [0, 1]], ![[111, 35, 126], [41, 95, 172], [1, 244, 231], [245, 230, 173], [0, 200, 162], [20, 123, 261], [261, 57, 215], [90, 124, 35], [29, 235, 145]], ![[0, 1], [119, 22, 12], [225, 77, 105], [263, 164, 110], [55, 151, 253], [248, 23, 141], [126, 218, 72], [61, 147, 235], [111, 35, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103, 155], []]
 b := ![[], [265, 234, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 3
  hpos := by decide
  P := [78, 104, 131, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![992402, -1343889, 516526]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3662, -4959, 1906]
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


def P277P0 : CertificateIrreducibleZModOfList' 277 3 2 8 [208, 193, 253, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 138, 210], [16, 138, 67], [0, 1]]
 g := ![![[245, 271, 230], [90, 117], [128, 79, 202], [239, 214], [84, 30, 7], [71, 156], [24, 1], []], ![[116, 109, 145, 63], [], [195, 181, 261, 250], [115, 198], [110, 194, 43, 10], [102, 210], [191, 208], [50, 57]], ![[121, 162, 214, 247], [263, 117], [13, 112, 54, 123], [256, 52], [136, 235, 178, 100], [68, 48], [98, 208], [193, 57]]]
 h' := ![![[8, 138, 210], [32, 208, 28], [245, 254, 35], [35, 189, 57], [256, 93, 136], [226, 18, 227], [271, 146, 106], [0, 0, 1], [0, 1]], ![[16, 138, 67], [91, 256, 177], [63, 46], [189, 25, 189], [248, 139, 72], [11, 100, 204], [250, 261, 137], [190, 92, 138], [8, 138, 210]], ![[0, 1], [36, 90, 72], [154, 254, 242], [12, 63, 31], [82, 45, 69], [237, 159, 123], [114, 147, 34], [0, 185, 138], [16, 138, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [231, 54], []]
 b := ![[], [192, 88, 253], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 3
  hpos := by decide
  P := [208, 193, 253, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![541072964, 128769821, -568912018]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1953332, 464873, -2053834]
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
  g := ![1, 3, 1, 1]
  P := ![263, 269, 271, 277]
  hP := PB278I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0]
    · exact ![I269N0, I269N1, I269N2]
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
    · exact ![18191447]
    · exact ![269, 269, 269]
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
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
      exact NI269N1
      exact NI269N2
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
  β := ![I269N0, I269N1, I269N2]
  Il := ![[], [I269N0, I269N1, I269N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
