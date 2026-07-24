
import IdealArithmetic.Examples.NF3_1_925444_2.RI3_1_925444_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![80, -11, 1]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0], ![80, -11, 1]] 
 ![![263, 0, 0], ![0, 263, 0], ![80, 252, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![80, -11, 1], ![254, 90, -56], ![-2704, -312, 124]]]
  hmulB := by decide  
  f := ![![![-79, 11, -1], ![263, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-80, -252, 263]], ![![0, -1, 1], ![18, 54, -56], ![-48, -120, 124]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 2 2 8 [31, 135, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 262], [0, 1]]
 g := ![![[191, 17], [209, 210], [95, 150], [138], [27], [243], [78], [1]], ![[0, 246], [0, 53], [96, 113], [138], [27], [243], [78], [1]]]
 h' := ![![[128, 262], [96, 65], [211, 173], [194, 26], [1, 123], [7, 194], [121, 207], [232, 128], [0, 1]], ![[0, 1], [0, 198], [0, 90], [103, 237], [228, 140], [117, 69], [54, 56], [47, 135], [128, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103]]
 b := ![[], [123, 183]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 2
  hpos := by decide
  P := [31, 135, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3447, 1561, 145]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-31, -133, 145]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![56, 1, 0]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![263, 0, 0], ![56, 1, 0]] 
 ![![263, 0, 0], ![56, 1, 0], ![139, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![56, 1, 0], ![-2, 58, 5], ![232, 32, 55]]]
  hmulB := by decide  
  f := ![![![1495, -44951, -3875], ![263, 203825, 0]], ![![274, -9571, -825], ![264, 43395, 0]], ![![755, -23758, -2048], ![304, 107725, 0]]]
  g := ![![![1, 0, 0], ![-56, 263, 0], ![-139, 0, 263]], ![![0, 1, 0], ![-15, 58, 5], ![-35, 32, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![80, -11, 1]] ![![263, 0, 0], ![56, 1, 0]]
  ![![263, 0, 0]] where
 M := ![![![69169, 0, 0], ![14728, 263, 0]], ![![21040, -2893, 263], ![4734, -526, 0]]]
 hmul := by decide  
 g := ![![![![263, 0, 0]], ![![56, 1, 0]]], ![![![80, -11, 1]], ![![18, -2, 0]]]]
 hle2 := by decide  


def PBC263 : ContainsPrimesAboveP 263 ![I263N0, I263N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 263 (by decide) (𝕀 ⊙ MulI263N0)
instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![44, 1, 0]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![269, 0, 0], ![44, 1, 0]] 
 ![![269, 0, 0], ![44, 1, 0], ![79, 0, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![44, 1, 0], ![-2, 46, 5], ![232, 32, 43]]]
  hmulB := by decide  
  f := ![![![104781, -2441343, -265360], ![8339, 14276368, 0]], ![![17140, -399285, -43400], ![1346, 2334920, 0]], ![![30743, -716975, -77931], ![2627, 4192688, 0]]]
  g := ![![![1, 0, 0], ![-44, 269, 0], ![-79, 0, 269]], ![![0, 1, 0], ![-9, 46, 5], ![-17, 32, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N0 : Nat.card (O ⧸ I269N0) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N0)

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := prime_ideal_of_norm_prime hp269.out _ NI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![66, 1, 0]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![269, 0, 0], ![66, 1, 0]] 
 ![![269, 0, 0], ![66, 1, 0], ![178, 0, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![66, 1, 0], ![-2, 68, 5], ![232, 32, 65]]]
  hmulB := by decide  
  f := ![![![-25985, 908219, 66780], ![-2959, -3592764, 0]], ![![-6420, 222770, 16380], ![-537, -881244, 0]], ![![-17236, 600977, 44189], ![-1789, -2377368, 0]]]
  g := ![![![1, 0, 0], ![-66, 269, 0], ![-178, 0, 269]], ![![0, 1, 0], ![-20, 68, 5], ![-50, 32, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1

def I269N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![-111, 1, 0]] i)))

def SI269N2: IdealEqSpanCertificate' Table ![![269, 0, 0], ![-111, 1, 0]] 
 ![![269, 0, 0], ![158, 1, 0], ![216, 0, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![-111, 1, 0], ![-2, -109, 5], ![232, 32, -112]]]
  hmulB := by decide  
  f := ![![![-11081, -652373, 29925], ![2152, -1609965, 0]], ![![-6474, -383140, 17575], ![1346, -945535, 0]], ![![-8847, -523839, 24029], ![1851, -1292760, 0]]]
  g := ![![![1, 0, 0], ![-158, 269, 0], ![-216, 0, 269]], ![![-1, 1, 0], ![60, -109, 5], ![72, 32, -112]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N2 : Nat.card (O ⧸ I269N2) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N2)

lemma isPrimeI269N2 : Ideal.IsPrime I269N2 := prime_ideal_of_norm_prime hp269.out _ NI269N2
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![269, 0, 0], ![44, 1, 0]] ![![269, 0, 0], ![66, 1, 0]]
  ![![269, 0, 0], ![-119, 130, 1]] where
 M := ![![![72361, 0, 0], ![17754, 269, 0]], ![![11836, 269, 0], ![2902, 112, 5]]]
 hmul := by decide  
 g := ![![![![269, 0, 0], ![0, 0, 0]], ![![66, 1, 0], ![0, 0, 0]]], ![![![44, 1, 0], ![0, 0, 0]], ![![13, -2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI269N1 : IdealMulLeCertificate' Table 
  ![![269, 0, 0], ![-119, 130, 1]] ![![269, 0, 0], ![-111, 1, 0]]
  ![![269, 0, 0]] where
 M := ![![![72361, 0, 0], ![-29859, 269, 0]], ![![-32011, 34970, 269], ![13181, -14257, 538]]]
 hmul := by decide  
 g := ![![![![269, 0, 0]], ![![-111, 1, 0]]], ![![![-119, 130, 1]], ![![49, -53, 2]]]]
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

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0], ![-42, -40, 1]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![271, 0, 0], ![-42, -40, 1]] 
 ![![271, 0, 0], ![0, 271, 0], ![229, 231, 1]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]], ![![-42, -40, 1], ![312, -90, -201], ![-9432, -1240, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-229, -231, 271]], ![![-1, -1, 1], ![171, 171, -201], ![-61, -31, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 2 2 8 [223, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [260, 270], [0, 1]]
 g := ![![[28, 175], [138, 185], [41, 53], [233, 169], [151], [265], [121], [1]], ![[0, 96], [0, 86], [0, 218], [0, 102], [151], [265], [121], [1]]]
 h' := ![![[260, 270], [120, 208], [71, 105], [73, 253], [143, 13], [36, 91], [253, 52], [48, 260], [0, 1]], ![[0, 1], [0, 63], [0, 166], [0, 18], [0, 258], [119, 180], [223, 219], [169, 11], [260, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [258]]
 b := ![[], [32, 129]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 2
  hpos := by decide
  P := [223, 11, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10567, 7306, 4736]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4041, -4010, 4736]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0], ![-70, 1, 0]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![271, 0, 0], ![-70, 1, 0]] 
 ![![271, 0, 0], ![201, 1, 0], ![240, 0, 1]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]], ![![-70, 1, 0], ![-2, -68, 5], ![232, 32, -71]]]
  hmulB := by decide  
  f := ![![![-12059, -424326, 31200], ![1626, -1691040, 0]], ![![-8905, -314709, 23140], ![1356, -1254188, 0]], ![![-10670, -375787, 27631], ![1477, -1497600, 0]]]
  g := ![![![1, 0, 0], ![-201, 271, 0], ![-240, 0, 271]], ![![-1, 1, 0], ![46, -68, 5], ![40, 32, -71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![271, 0, 0], ![-42, -40, 1]] ![![271, 0, 0], ![-70, 1, 0]]
  ![![271, 0, 0]] where
 M := ![![![73441, 0, 0], ![-18970, 271, 0]], ![![-11382, -10840, 271], ![3252, 2710, -271]]]
 hmul := by decide  
 g := ![![![![271, 0, 0]], ![![-70, 1, 0]]], ![![![-42, -40, 1]], ![![12, 10, -1]]]]
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


lemma PB273I5_primes (p : ℕ) :
  p ∈ Set.range ![263, 269, 271] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 272 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 272 (by omega)

def PB273I5 : PrimesBelowBoundCertificateInterval O 257 272 273 where
  m := 3
  g := ![2, 3, 2]
  P := ![263, 269, 271]
  hP := PB273I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0, I263N1]
    · exact ![I269N0, I269N1, I269N2]
    · exact ![I271N0, I271N1]
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
    · exact ![69169, 263]
    · exact ![269, 269, 269]
    · exact ![73441, 271]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
      exact NI269N1
      exact NI269N2
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
  β := ![I263N1, I269N0, I269N1, I269N2, I271N1]
  Il := ![[I263N1], [I269N0, I269N1, I269N2], [I271N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
