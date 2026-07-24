
import IdealArithmetic.Examples.NF3_1_508248_2.RI3_1_508248_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1174899, -13352, -77412]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![1174899, -13352, -77412]] 
 ![![197, 0, 0], ![0, 197, 0], ![196, 180, 1]] where
  M :=![![![1174899, -13352, -77412], ![-10656152, 838547, 21304], ![2492496, -1059764, 814543]]]
  hmulB := by decide  
  f := ![![![-3581775641, -471645832, -328066748]], ![![-44329919560, -5837334297, -4060324824]], ![![-44305223012, -5834082272, -4058062785]]]
  g := ![![![82983, 70664, -77412], ![-75288, -15209, 21304], ![-797756, -749632, 814543]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [108, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 196], [0, 1]]
 g := ![![[], [40], [], [], [], [41], [0, 1]], ![[], [40], [], [], [], [41], [0, 196]]]
 h' := ![![[0, 196], [14], [0, 51], [53], [168], [103], [0, 89], [0, 1]], ![[0, 1], [14], [0, 146], [53], [168], [103], [0, 108], [0, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [166]]
 b := ![[], [0, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [108, 0, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1461, 409, 115]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-107, -103, 115]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3581775641, -471645832, -328066748]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-3581775641, -471645832, -328066748]] 
 ![![197, 0, 0], ![172, 1, 0], ![159, 0, 1]] where
  M :=![![![-3581775641, -471645832, -328066748], ![-44329919560, -5837334297, -4060324824], ![-46715386928, -6151451052, -4278817717]]]
  hmulB := by decide  
  f := ![![![1174899, -13352, -77412]], ![![971708, -7401, -67480]], ![![960921, -16156, -58345]]]
  g := ![![![658395535, -471645832, -328066748], ![8148645820, -5837334297, -4060324824], ![8587138127, -6151451052, -4278817717]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![1174899, -13352, -77412]] ![![-3581775641, -471645832, -328066748]]
  ![![197, 0, 0]] where
 M := ![![![197, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2072144479021, -272858605560, -189794607132]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-2072144479021, -272858605560, -189794607132]] 
 ![![199, 0, 0], ![0, 199, 0], ![125, 41, 1]] where
  M :=![![![-2072144479021, -272858605560, -189794607132], ![-25645938573096, -3377040118669, -2348996841336], ![-27025989567888, -3558764314956, -2475400303561]]]
  hmulB := by decide  
  f := ![![![-1002307, 153432, -68748]], ![![-9794088, -970435, 1671816]], ![![-2521721, -104969, 292955]]]
  g := ![![![108804931721, 37732262748, -189794607132], ![1346626465296, 466994122493, -2348996841336], ![1419090695363, 492123859955, -2475400303561]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [103, 154, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 198], [0, 1]]
 g := ![![[44, 114], [49, 94], [112, 51], [122], [23], [47], [45, 1]], ![[0, 85], [100, 105], [19, 148], [122], [23], [47], [90, 198]]]
 h' := ![![[45, 198], [127, 121], [6, 33], [131, 38], [110, 91], [115, 53], [141, 131], [0, 1]], ![[0, 1], [0, 78], [98, 166], [50, 161], [26, 108], [112, 146], [66, 68], [45, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123]]
 b := ![[], [59, 161]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [103, 154, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11326, 2548, 3052]
  a := ![-3, 0, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1974, -616, 3052]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1002307, -153432, 68748]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![1002307, -153432, 68748]] 
 ![![199, 0, 0], ![189, 1, 0], ![151, 0, 1]] where
  M :=![![![1002307, -153432, 68748], ![9794088, 970435, -1671816], ![-25023504, 279996, 1652911]]]
  hmulB := by decide  
  f := ![![![2072144479021, 272858605560, 189794607132]], ![![2096890678935, 276117168691, 192061193916]], ![![1708139728141, 224926702284, 156454200907]]]
  g := ![![![98593, -153432, 68748], ![396111, 970435, -1671816], ![-1645891, 279996, 1652911]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-2072144479021, -272858605560, -189794607132]] ![![1002307, -153432, 68748]]
  ![![199, 0, 0]] where
 M := ![![![-199, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB202I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 201 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 201 (by omega)

def PB202I4 : PrimesBelowBoundCertificateInterval O 193 201 202 where
  m := 2
  g := ![2, 2]
  P := ![197, 199]
  hP := PB202I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
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
    · exact ![38809, 197]
    · exact ![39601, 199]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
  β := ![I197N1, I199N1]
  Il := ![[I197N1], [I199N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
