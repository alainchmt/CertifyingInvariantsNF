
import IdealArithmetic.Examples.NF3_3_866133_1.RI3_3_866133_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0]] 
 ![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [78, 84, 174, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [195, 150, 38], [25, 46, 159], [0, 1]]
 g := ![![[96], [10, 53], [84, 189, 34], [137, 160], [95, 161], [29, 135], [1]], ![[19, 31, 171, 129], [179, 146], [122, 27, 77, 152], [177, 63], [191, 146], [187, 104], [42, 146, 168, 106]], ![[177, 63, 21, 68], [169, 109], [89, 135, 93, 189], [44, 85], [54, 155], [111, 181], [124, 15, 31, 91]]]
 h' := ![![[195, 150, 38], [48, 80], [146, 132, 29], [121, 63, 25], [13, 84, 95], [79, 138, 84], [119, 113, 23], [0, 1]], ![[25, 46, 159], [85, 180, 85], [116, 186, 46], [122, 7, 195], [170, 2, 76], [80, 169, 46], [65, 83, 33], [195, 150, 38]], ![[0, 1], [78, 134, 112], [88, 76, 122], [153, 127, 174], [32, 111, 26], [86, 87, 67], [43, 1, 141], [25, 46, 159]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 136], []]
 b := ![[], [115, 168, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [78, 84, 174, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7643797, -1883517, -498804]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-38801, -9561, -2532]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def PBC197 : ContainsPrimesAboveP 197 ![I197N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![197, 0, 0]]) timesTableT_eq_Table B_one_repr 197 (by decide) 𝕀

instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2890, -104, 55]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-2890, -104, 55]] 
 ![![199, 0, 0], ![0, 199, 0], ![56, 56, 1]] where
  M :=![![![-2890, -104, 55], ![18987, 679, -361], ![-24966, -887, 471]]]
  hmulB := by decide  
  f := ![![![2, -1, -1]], ![![-351, -60, -5]], ![![-101, -18, -2]]]
  g := ![![![-30, -16, 55], ![197, 105, -361], ![-258, -137, 471]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [183, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [139, 198], [0, 1]]
 g := ![![[46, 155], [19, 91], [62, 33], [32], [123], [161], [139, 1]], ![[99, 44], [131, 108], [72, 166], [32], [123], [161], [79, 198]]]
 h' := ![![[139, 198], [105, 126], [196, 115], [116, 86], [179, 119], [20, 83], [35, 34], [0, 1]], ![[0, 1], [107, 73], [62, 84], [130, 113], [4, 80], [15, 116], [184, 165], [139, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131]]
 b := ![[], [174, 165]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [183, 60, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4174, 2194, 3543]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1018, -986, 3543]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -1, -1]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![2, -1, -1]] 
 ![![199, 0, 0], ![173, 1, 0], ![24, 0, 1]] where
  M :=![![![2, -1, -1], ![-351, -60, -5], ![-555, -166, -62]]]
  hmulB := by decide  
  f := ![![![-2890, -104, 55]], ![![-2417, -87, 46]], ![![-474, -17, 9]]]
  g := ![![![1, -1, -1], ![51, -60, -5], ![149, -166, -62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-2890, -104, 55]] ![![2, -1, -1]]
  ![![199, 0, 0]] where
 M := ![![![199, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)


lemma PB207I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 206 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 206 (by omega)

def PB207I4 : PrimesBelowBoundCertificateInterval O 193 206 207 where
  m := 2
  g := ![1, 2]
  P := ![197, 199]
  hP := PB207I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0, I199N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![7645373]
    · exact ![39601, 199]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
  β := ![I199N1]
  Il := ![[], [I199N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
