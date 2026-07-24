
import IdealArithmetic.Examples.NF3_1_31496_1.RI3_1_31496_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [27, 16, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 25, 11], [15, 11, 26], [0, 1]]
 g := ![![[22, 13, 25], [25, 21], [15, 10, 25], [13, 1], []], ![[15, 13, 22, 21], [2, 34], [24, 27, 22, 10], [12, 10], [14, 10]], ![[35, 15, 21, 30], [22, 9], [19, 18, 28, 34], [11, 33], [36, 10]]]
 h' := ![![[35, 25, 11], [32, 28, 5], [2, 36, 13], [19, 24, 5], [0, 0, 1], [0, 1]], ![[15, 11, 26], [30, 24, 30], [26, 23, 21], [25, 35, 23], [33, 35, 11], [35, 25, 11]], ![[0, 1], [10, 22, 2], [7, 15, 3], [11, 15, 9], [30, 2, 25], [15, 11, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 28], []]
 b := ![[], [9, 12, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [27, 16, 24, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8029, 1702, -4218]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![217, 46, -114]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [14, 31, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 7, 20], [20, 33, 21], [0, 1]]
 g := ![![[16, 35, 9], [6, 25], [40, 8], [11, 1, 1], []], ![[4, 12, 34, 9], [17, 16], [10, 33], [1, 37, 16, 9], [24, 31]], ![[6, 23, 31, 40], [6, 40], [26, 20], [10, 7, 3, 4], [23, 31]]]
 h' := ![![[22, 7, 20], [38, 23, 38], [32, 35, 5], [10, 14, 7], [0, 0, 1], [0, 1]], ![[20, 33, 21], [18, 24, 33], [25, 36, 4], [1, 35, 19], [25, 32, 33], [22, 7, 20]], ![[0, 1], [18, 35, 11], [15, 11, 32], [16, 33, 15], [37, 9, 7], [20, 33, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 20], []]
 b := ![[], [40, 4, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [14, 31, 40, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![128002, -44116, 7052]
  a := ![2, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3122, -1076, 172]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [35, 32, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 7, 3], [2, 35, 40], [0, 1]]
 g := ![![[23, 36, 31], [6, 14, 6], [33, 6], [35, 14, 1], []], ![[2, 24, 25, 19], [13, 27, 33, 30], [17, 41], [15, 25, 6, 20], [39, 9]], ![[30, 23, 34, 13], [27, 42, 12, 10], [15, 13], [23, 42, 20, 25], [2, 9]]]
 h' := ![![[12, 7, 3], [5, 37, 26], [17, 5, 36], [22, 24, 7], [0, 0, 1], [0, 1]], ![[2, 35, 40], [7, 23, 32], [24, 39, 28], [19, 35, 16], [26, 24, 35], [12, 7, 3]], ![[0, 1], [40, 26, 28], [16, 42, 22], [38, 27, 20], [20, 19, 7], [2, 35, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 3], []]
 b := ![[], [23, 35, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [35, 32, 29, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-468030275, 305125334, -192771580]
  a := ![-65, 1, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10884425, 7095938, -4483060]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3635606459025097527778, -223551136648676378729, -328389834461125870033]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-3635606459025097527778, -223551136648676378729, -328389834461125870033]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 14, 1]] where
  M :=![![![-3635606459025097527778, -223551136648676378729, -328389834461125870033], ![-11060415673865830089818, -680097948874964697481, -999043244407155006220], ![-10004306185095327458321, -615158445850919551703, -903649085523641076210]]]
  hmulB := by decide  
  f := ![![![-28794456050, 11125747253, -1836217181]], ![![-49469419720, -12268501421, 31541024578]], ![![-7236424557, -6097457077, 9370884892]]]
  g := ![![![-77353328915427606974, 93061841400150761739, -328389834461125870033], ![-235327993060975108294, 283117180272876710417, -999043244407155006220], ![-212857578406283562943, 256083590457022457771, -903649085523641076210]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [23, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 46], [0, 1]]
 g := ![![[42, 17], [37, 12], [7, 28], [23, 18], [1]], ![[23, 30], [7, 35], [31, 19], [25, 29], [1]]]
 h' := ![![[21, 46], [42, 8], [27, 23], [35, 34], [24, 21], [0, 1]], ![[0, 1], [22, 39], [40, 24], [44, 13], [42, 26], [21, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [41, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [23, 26, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-94, 540, -606]
  a := ![-2, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, 192, -606]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28794456050, 11125747253, -1836217181]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-28794456050, 11125747253, -1836217181]] 
 ![![47, 0, 0], ![4, 1, 0], ![42, 0, 1]] where
  M :=![![![-28794456050, 11125747253, -1836217181], ![-49469419720, -12268501421, 31541024578], ![352459921901, -114821462725, -1142754168]]]
  hmulB := by decide  
  f := ![![![-3635606459025097527778, -223551136648676378729, -328389834461125870033]], ![![-544741308722685536190, -33495797775950430051, -49204310260673584816]], ![![-3461697392854243055851, -212857578406283562943, -312681321976402715268]]]
  g := ![![![81354820, 11125747253, -1836217181], ![-28194009496, -12268501421, 31541024578], ![18292371231, -114821462725, -1142754168]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-3635606459025097527778, -223551136648676378729, -328389834461125870033]] ![![-28794456050, 11125747253, -1836217181]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)


lemma PB51I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 50 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 50 (by omega)

def PB51I1 : PrimesBelowBoundCertificateInterval O 31 50 51 where
  m := 4
  g := ![1, 1, 1, 2]
  P := ![37, 41, 43, 47]
  hP := PB51I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![68921]
    · exact ![79507]
    · exact ![2209, 47]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
  β := ![I47N1]
  Il := ![[], [], [], [I47N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
