
import IdealArithmetic.Examples.NF3_3_806284_1.RI3_3_806284_1
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


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [192, 135, 112, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 7, 80], [82, 189, 117], [0, 1]]
 g := ![![[40, 144, 182], [63, 104], [168, 138, 154], [144, 88], [112, 65], [175, 133], [1]], ![[158, 169, 3, 122], [125, 85], [150, 99, 32, 195], [15, 156], [49, 157], [137, 158], [119, 189, 185, 194]], ![[157, 171, 133, 102], [165, 49], [108, 20, 101, 141], [187, 1], [75, 133], [12, 173], [28, 151, 118, 3]]]
 h' := ![![[3, 7, 80], [64, 165, 24], [52, 67, 33], [92, 10, 101], [102, 14, 132], [112, 118, 38], [5, 62, 85], [0, 1]], ![[82, 189, 117], [143, 15, 6], [75, 182, 171], [13, 99, 189], [23, 132, 64], [70, 6, 74], [31, 41, 143], [3, 7, 80]], ![[0, 1], [84, 17, 167], [21, 145, 190], [186, 88, 104], [32, 51, 1], [53, 73, 85], [105, 94, 166], [82, 189, 117]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 106], []]
 b := ![[], [87, 158, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [192, 135, 112, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-180058, -120958, -21670]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-914, -614, -110]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![18, 31, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![18, 31, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![18, 31, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![18, 31, 1], ![103, 100, 61], ![3090, 1607, 39]]]
  hmulB := by decide  
  f := ![![![-17, -31, -1], ![199, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -31, 199]], ![![0, 0, 1], ![-5, -9, 61], ![12, 2, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [65, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [193, 198], [0, 1]]
 g := ![![[95, 49], [131, 80], [189, 177], [9], [25], [45], [193, 1]], ![[0, 150], [49, 119], [122, 22], [9], [25], [45], [187, 198]]]
 h' := ![![[193, 198], [42, 7], [53, 94], [14, 66], [20, 3], [124, 194], [191, 170], [0, 1]], ![[0, 1], [0, 192], [86, 105], [16, 133], [2, 196], [154, 5], [166, 29], [193, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [48, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [65, 6, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-764, 829, 842]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-80, -127, 842]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-61, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-61, 1, 0]] 
 ![![199, 0, 0], ![138, 1, 0], ![160, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-61, 1, 0], ![0, -60, 2], ![103, 51, -62]]]
  hmulB := by decide  
  f := ![![![6955, -114, 0], ![22686, 0, 0]], ![![4820, -79, 0], ![15722, 0, 0]], ![![5622, -62, -1], ![18338, 100, 0]]]
  g := ![![![1, 0, 0], ![-138, 199, 0], ![-160, 0, 199]], ![![-1, 1, 0], ![40, -60, 2], ![15, 51, -62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![18, 31, 1]] ![![199, 0, 0], ![-61, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-12139, 199, 0]], ![![3582, 6169, 199], ![-995, -1791, 0]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-61, 1, 0]]], ![![![18, 31, 1]], ![![-5, -9, 0]]]]
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


lemma PB200I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 199 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 199 (by omega)

def PB200I4 : PrimesBelowBoundCertificateInterval O 193 199 200 where
  m := 2
  g := ![1, 2]
  P := ![197, 199]
  hP := PB200I4_primes
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
