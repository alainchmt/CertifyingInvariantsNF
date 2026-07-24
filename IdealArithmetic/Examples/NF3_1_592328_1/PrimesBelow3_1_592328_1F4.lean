
import IdealArithmetic.Examples.NF3_1_592328_1.RI3_1_592328_1
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


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [36, 157, 186, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 28, 106], [120, 168, 91], [0, 1]]
 g := ![![[107, 98, 81], [93, 23], [8, 105, 121], [56, 154], [10, 34], [44, 121], [1]], ![[23, 39, 178, 147], [162, 100], [183, 55, 185, 11], [149, 155], [13, 173], [103, 164], [23, 32, 82, 151]], ![[125, 39, 6, 139], [16, 150], [46, 112, 24, 115], [55, 171], [84, 36], [1, 64], [178, 163, 94, 46]]]
 h' := ![![[88, 28, 106], [8, 55, 188], [106, 21, 90], [59, 195, 11], [41, 170, 96], [106, 40, 25], [161, 40, 11], [0, 1]], ![[120, 168, 91], [44, 191, 181], [153, 91, 10], [151, 170, 60], [183, 106, 67], [116, 183, 166], [9, 164, 178], [88, 28, 106]], ![[0, 1], [147, 148, 25], [59, 85, 97], [186, 29, 126], [183, 118, 34], [45, 171, 6], [9, 190, 8], [120, 168, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120, 62], []]
 b := ![[], [83, 194, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [36, 157, 186, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2637830, 353418, 30338]
  a := ![-4, -3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13390, 1794, 154]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![9, 12, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![9, 12, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![9, 12, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![9, 12, 1], ![-157, 56, 71], ![-2208, 240, 20]]]
  hmulB := by decide  
  f := ![![![-8, -12, -1], ![199, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -12, 199]], ![![0, 0, 1], ![-4, -4, 71], ![-12, 0, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [150, 113, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [86, 198], [0, 1]]
 g := ![![[18, 28], [122, 130], [33, 40], [13], [139], [157], [86, 1]], ![[38, 171], [158, 69], [90, 159], [13], [139], [157], [172, 198]]]
 h' := ![![[86, 198], [8, 174], [25, 145], [83, 55], [21, 150], [162, 138], [35, 82], [0, 1]], ![[0, 1], [47, 25], [157, 54], [37, 144], [185, 49], [90, 61], [122, 117], [86, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106]]
 b := ![[], [109, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [150, 113, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1097, -2451, 4124]
  a := ![5, 3, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-181, -261, 4124]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-71, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-71, 1, 0]] 
 ![![199, 0, 0], ![128, 1, 0], ![179, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-71, 1, 0], ![3, -69, 6], ![-193, 23, -72]]]
  hmulB := by decide  
  f := ![![![-1828, 50227, -4368], ![995, 144872, 0]], ![![-1190, 32289, -2808], ![598, 93132, 0]], ![![-1640, 45179, -3929], ![907, 130312, 0]]]
  g := ![![![1, 0, 0], ![-128, 199, 0], ![-179, 0, 199]], ![![-1, 1, 0], ![39, -69, 6], ![49, 23, -72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![9, 12, 1]] ![![199, 0, 0], ![-71, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-14129, 199, 0]], ![![1791, 2388, 199], ![-796, -796, 0]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-71, 1, 0]]], ![![![9, 12, 1]], ![![-4, -4, 0]]]]
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
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![0, -6, 1]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![0, -6, 1]] 
 ![![211, 0, 0], ![0, 211, 0], ![0, 205, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![0, -6, 1], ![-211, 11, -37], ![1266, -174, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -205, 211]], ![![0, -1, 1], ![-1, 36, -37], ![6, -29, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [190, 154, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 210], [0, 1]]
 g := ![![[63, 5], [82, 9], [103], [122], [152, 139], [53], [57, 1]], ![[137, 206], [173, 202], [103], [122], [57, 72], [53], [114, 210]]]
 h' := ![![[57, 210], [34, 65], [104, 3], [126, 37], [27, 79], [177, 136], [142, 105], [0, 1]], ![[0, 1], [152, 146], [64, 208], [125, 174], [99, 132], [122, 75], [8, 106], [57, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [87, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [190, 154, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-758967, -781596, 904214]
  a := ![-130, -65, -196]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3597, -882206, 904214]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![37, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![37, 1, 0]] 
 ![![211, 0, 0], ![37, 1, 0], ![182, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![37, 1, 0], ![3, 39, 6], ![-193, 23, 36]]]
  hmulB := by decide  
  f := ![![![93099, 1261154, 194040], ![22366, -6823740, 0]], ![![16307, 221111, 34020], ![4010, -1196370, 0]], ![![80302, 1087820, 167371], ![19300, -5885880, 0]]]
  g := ![![![1, 0, 0], ![-37, 211, 0], ![-182, 0, 211]], ![![0, 1, 0], ![-12, 39, 6], ![-36, 23, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![0, -6, 1]] ![![211, 0, 0], ![37, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![7807, 211, 0]], ![![0, -1266, 211], ![-211, -211, 0]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![37, 1, 0]]], ![![![0, -6, 1]], ![![-1, -1, 0]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)


lemma PB218I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 217 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 217 (by omega)

def PB218I4 : PrimesBelowBoundCertificateInterval O 193 217 218 where
  m := 3
  g := ![1, 2, 2]
  P := ![197, 199, 211]
  hP := PB218I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
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
    · exact ![7645373]
    · exact ![39601, 199]
    · exact ![44521, 211]
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
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
  β := ![I199N1, I211N1]
  Il := ![[], [I199N1], [I211N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
