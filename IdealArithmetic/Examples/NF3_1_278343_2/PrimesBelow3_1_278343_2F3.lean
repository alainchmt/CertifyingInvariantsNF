
import IdealArithmetic.Examples.NF3_1_278343_2.RI3_1_278343_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![56, -48, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![56, -48, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![56, 91, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![56, -48, 1], ![-15, -7, -385], ![-3912, 732, 89]]]
  hmulB := by decide  
  f := ![![![-55, 48, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -91, 139]], ![![0, -1, 1], ![155, 252, -385], ![-64, -53, 89]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [22, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [96, 138], [0, 1]]
 g := ![![[122, 31], [24, 57], [46], [60, 125], [29], [42], [1]], ![[40, 108], [75, 82], [46], [106, 14], [29], [42], [1]]]
 h' := ![![[96, 138], [28, 93], [135, 125], [70, 18], [30, 79], [116, 86], [117, 96], [0, 1]], ![[0, 1], [60, 46], [42, 14], [130, 121], [108, 60], [32, 53], [20, 43], [96, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127]]
 b := ![[], [10, 133]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [22, 43, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![342, 938, -2620]
  a := ![-3, -2, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1058, 1722, -2620]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-32, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-32, 1, 0]] 
 ![![139, 0, 0], ![107, 1, 0], ![50, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-32, 1, 0], ![2, -31, 8], ![81, -15, -33]]]
  hmulB := by decide  
  f := ![![![-2375, 40293, -10400], ![973, 180700, 0]], ![![-1839, 30995, -8000], ![696, 139000, 0]], ![![-858, 14494, -3741], ![334, 65000, 0]]]
  g := ![![![1, 0, 0], ![-107, 139, 0], ![-50, 0, 139]], ![![-1, 1, 0], ![21, -31, 8], ![24, -15, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![56, -48, 1]] ![![139, 0, 0], ![-32, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-4448, 139, 0]], ![![7784, -6672, 139], ![-1807, 1529, -417]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-32, 1, 0]]], ![![![56, -48, 1]], ![![-13, 11, -3]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![64, -45, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![64, -45, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![64, 104, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![64, -45, 1], ![-9, 4, -361], ![-3669, 687, 94]]]
  hmulB := by decide  
  f := ![![![-63, 45, -1], ![149, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -104, 149]], ![![0, -1, 1], ![155, 252, -361], ![-65, -61, 94]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [62, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [80, 148], [0, 1]]
 g := ![![[66, 47], [95], [105, 22], [119], [21, 116], [142], [1]], ![[101, 102], [95], [77, 127], [119], [63, 33], [142], [1]]]
 h' := ![![[80, 148], [100, 135], [46, 63], [103, 52], [39, 62], [106, 99], [87, 80], [0, 1]], ![[0, 1], [23, 14], [20, 86], [91, 97], [82, 87], [129, 50], [80, 69], [80, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [137, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [62, 69, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1740, 972, -558]
  a := ![2, 0, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![228, 396, -558]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![63, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![63, 1, 0]] 
 ![![149, 0, 0], ![63, 1, 0], ![55, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![63, 1, 0], ![2, 64, 8], ![81, -15, 62]]]
  hmulB := by decide  
  f := ![![![1648, 70839, 8856], ![1341, -164943, 0]], ![![684, 29948, 3744], ![597, -69732, 0]], ![![569, 26148, 3269], ![588, -60885, 0]]]
  g := ![![![1, 0, 0], ![-63, 149, 0], ![-55, 0, 149]], ![![0, 1, 0], ![-30, 64, 8], ![-16, -15, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![64, -45, 1]] ![![149, 0, 0], ![63, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![9387, 149, 0]], ![![9536, -6705, 149], ![4023, -2831, -298]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![63, 1, 0]]], ![![![64, -45, 1]], ![![27, -19, -2]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)


lemma PB150I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 149 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 149 (by omega)

def PB150I3 : PrimesBelowBoundCertificateInterval O 137 149 150 where
  m := 2
  g := ![2, 2]
  P := ![139, 149]
  hP := PB150I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![22201, 149]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
  β := ![I139N1, I149N1]
  Il := ![[I139N1], [I149N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
