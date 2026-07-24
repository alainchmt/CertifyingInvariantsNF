
import IdealArithmetic.Examples.NF3_1_516059_1.RI3_1_516059_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![37, 1, 0]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![197, 0, 0], ![37, 1, 0]] 
 ![![197, 0, 0], ![37, 1, 0], ![45, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![37, 1, 0], ![-3, 34, 7], ![50, -26, 40]]]
  hmulB := by decide  
  f := ![![![-8694, 100645, 20720], ![-985, -583120, 0]], ![![-1628, 18871, 3885], ![-196, -109335, 0]], ![![-1985, 22990, 4733], ![-230, -133200, 0]]]
  g := ![![![1, 0, 0], ![-37, 197, 0], ![-45, 0, 197]], ![![0, 1, 0], ![-8, 34, 7], ![-4, -26, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![62, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![62, 1, 0]] 
 ![![197, 0, 0], ![62, 1, 0], ![68, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![62, 1, 0], ![-3, 59, 7], ![50, -26, 65]]]
  hmulB := by decide  
  f := ![![![17699, -371247, -44044], ![3743, 1239524, 0]], ![![5568, -116826, -13860], ![1183, 390060, 0]], ![![6058, -128147, -15203], ![1455, 427856, 0]]]
  g := ![![![1, 0, 0], ![-62, 197, 0], ![-68, 0, 197]], ![![0, 1, 0], ![-21, 59, 7], ![-14, -26, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![98, 1, 0]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![197, 0, 0], ![98, 1, 0]] 
 ![![197, 0, 0], ![98, 1, 0], ![133, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![98, 1, 0], ![-3, 95, 7], ![50, -26, 101]]]
  hmulB := by decide  
  f := ![![![83979, -3075284, -226590], ![26398, 6376890, 0]], ![![41740, -1529757, -112714], ![13200, 3172094, 0]], ![![56693, -2076207, -152977], ![17829, 4305210, 0]]]
  g := ![![![1, 0, 0], ![-98, 197, 0], ![-133, 0, 197]], ![![0, 1, 0], ![-52, 95, 7], ![-55, -26, 101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![37, 1, 0]] ![![197, 0, 0], ![62, 1, 0]]
  ![![197, 0, 0], ![74, 70, 1]] where
 M := ![![![38809, 0, 0], ![12214, 197, 0]], ![![7289, 197, 0], ![2291, 96, 7]]]
 hmul := by decide  
 g := ![![![![123, -70, -1], ![197, 0, 0]], ![![-12, -69, -1], ![197, 0, 0]]], ![![![-37, -69, -1], ![197, 0, 0]], ![![9, -2, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![74, 70, 1]] ![![197, 0, 0], ![98, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![19306, 197, 0]], ![![14578, 13790, 197], ![7092, 6698, 591]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![98, 1, 0]]], ![![![74, 70, 1]], ![![36, 34, 3]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1, I197N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
    exact isPrimeI197N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0 ⊙ MulI197N1)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-33, -12, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-33, -12, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![166, 187, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-33, -12, 1], ![86, -23, -81], ![-546, 308, -92]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-166, -187, 199]], ![![-1, -1, 1], ![68, 76, -81], ![74, 88, -92]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [55, 133, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [66, 198], [0, 1]]
 g := ![![[158, 25], [163, 9], [20, 1], [65], [140], [158], [66, 1]], ![[17, 174], [160, 190], [86, 198], [65], [140], [158], [132, 198]]]
 h' := ![![[66, 198], [189, 194], [94, 3], [176, 1], [186, 142], [181, 109], [151, 122], [0, 1]], ![[0, 1], [58, 5], [93, 196], [43, 198], [6, 57], [12, 90], [44, 77], [66, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [54, 125]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [55, 133, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1697, 798, -2156]
  a := ![3, 2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1807, 2030, -2156]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![81, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![81, 1, 0]] 
 ![![199, 0, 0], ![81, 1, 0], ![92, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![81, 1, 0], ![-3, 78, 7], ![50, -26, 84]]]
  hmulB := by decide  
  f := ![![![14200, -409207, -36722], ![3781, 1043954, 0]], ![![5757, -166538, -14945], ![1593, 424865, 0]], ![![6494, -189182, -16977], ![1922, 482632, 0]]]
  g := ![![![1, 0, 0], ![-81, 199, 0], ![-92, 0, 199]], ![![0, 1, 0], ![-35, 78, 7], ![-28, -26, 84]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![-33, -12, 1]] ![![199, 0, 0], ![81, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![16119, 199, 0]], ![![-6567, -2388, 199], ![-2587, -995, 0]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![81, 1, 0]]], ![![![-33, -12, 1]], ![![-13, -5, 0]]]]
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


lemma PB204I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 203 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 203 (by omega)

def PB204I4 : PrimesBelowBoundCertificateInterval O 193 203 204 where
  m := 2
  g := ![3, 2]
  P := ![197, 199]
  hP := PB204I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
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
    · exact ![197, 197, 197]
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
      exact NI197N2
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
  β := ![I197N0, I197N1, I197N2, I199N1]
  Il := ![[I197N0, I197N1, I197N2], [I199N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
