
import IdealArithmetic.Examples.NF3_3_936117_1.RI3_3_936117_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-102, -64, 7]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-102, -64, 7]] 
 ![![197, 0, 0], ![0, 197, 0], ![98, 19, 1]] where
  M :=![![![-102, -64, 7], ![623, 360, -64], ![-5696, -3601, 360]]]
  hmulB := by decide  
  f := ![![![512, 11, -8]], ![![-712, -16, 11]], ![![191, 4, -3]]]
  g := ![![![-4, -1, 7], ![35, 8, -64], ![-208, -53, 360]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [157, 146, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 196], [0, 1]]
 g := ![![[85, 64], [193], [11, 169], [154], [15], [96], [51, 1]], ![[0, 133], [193], [159, 28], [154], [15], [96], [102, 196]]]
 h' := ![![[51, 196], [183, 8], [46, 28], [169, 13], [71, 96], [72, 139], [70, 80], [0, 1]], ![[0, 1], [0, 189], [95, 169], [44, 184], [42, 101], [69, 58], [13, 117], [51, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [130]]
 b := ![[], [17, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [157, 146, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![335, 75, -79]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![41, 8, -79]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-512, -11, 8]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-512, -11, 8]] 
 ![![197, 0, 0], ![178, 1, 0], ![33, 0, 1]] where
  M :=![![![-512, -11, 8], ![712, 16, -11], ![-979, -14, 16]]]
  hmulB := by decide  
  f := ![![![102, 64, -7]], ![![89, 56, -6]], ![![46, 29, -3]]]
  g := ![![![6, -11, 8], ![-9, 16, -11], ![5, -14, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-102, -64, 7]] ![![-512, -11, 8]]
  ![![197, 0, 0]] where
 M := ![![![-197, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17679, 15136, 1734]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![17679, 15136, 1734]] 
 ![![199, 0, 0], ![0, 199, 0], ![25, 115, 1]] where
  M :=![![![17679, 15136, 1734], ![154326, 132123, 15136], ![1347104, 1153302, 132123]]]
  hmulB := by decide  
  f := ![![![-543, -60, 14]], ![![1246, 381, -60]], ![![625, 199, -31]]]
  g := ![![![-129, -926, 1734], ![-1126, -8083, 15136], ![-9829, -70557, 132123]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [136, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [152, 198], [0, 1]]
 g := ![![[34, 180], [187, 175], [189, 61], [56], [36], [123], [152, 1]], ![[131, 19], [121, 24], [108, 138], [56], [36], [123], [105, 198]]]
 h' := ![![[152, 198], [40, 141], [166, 162], [25, 85], [173, 97], [166, 193], [24, 83], [0, 1]], ![[0, 1], [179, 58], [114, 37], [10, 114], [191, 102], [50, 6], [103, 116], [152, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [182, 139]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [136, 47, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-978, -81, 733]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-97, -424, 733]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![543, 60, -14]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![543, 60, -14]] 
 ![![199, 0, 0], ![84, 1, 0], ![108, 0, 1]] where
  M :=![![![543, 60, -14], ![-1246, -381, 60], ![5340, 2714, -381]]]
  hmulB := by decide  
  f := ![![![-17679, -15136, -1734]], ![![-8238, -7053, -808]], ![![-16364, -14010, -1605]]]
  g := ![![![-15, 60, -14], ![122, -381, 60], ![-912, 2714, -381]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![17679, 15136, 1734]] ![![543, 60, -14]]
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
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![30, 1, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0], ![30, 1, 0]] 
 ![![211, 0, 0], ![30, 1, 0], ![155, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![30, 1, 0], ![0, 30, 1], ![89, 66, 30]]]
  hmulB := by decide  
  f := ![![![4441, 148, 0], ![-31228, 0, 0]], ![![630, 21, 0], ![-4430, 0, 0]], ![![3245, 108, 0], ![-22818, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 211, 0], ![-155, 0, 211]], ![![0, 1, 0], ![-5, 30, 1], ![-31, 66, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N0 : Nat.card (O ⧸ I211N0) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N0)

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := prime_ideal_of_norm_prime hp211.out _ NI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![77, 1, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![211, 0, 0], ![77, 1, 0]] 
 ![![211, 0, 0], ![77, 1, 0], ![190, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![77, 1, 0], ![0, 77, 1], ![89, 66, 77]]]
  hmulB := by decide  
  f := ![![![4313, 56, 0], ![-11816, 0, 0]], ![![1463, 19, 0], ![-4008, 0, 0]], ![![3956, 51, 0], ![-10838, 1, 0]]]
  g := ![![![1, 0, 0], ![-77, 211, 0], ![-190, 0, 211]], ![![0, 1, 0], ![-29, 77, 1], ![-93, 66, 77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0], ![104, 1, 0]] i)))

def SI211N2: IdealEqSpanCertificate' Table ![![211, 0, 0], ![104, 1, 0]] 
 ![![211, 0, 0], ![104, 1, 0], ![156, 0, 1]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]], ![![104, 1, 0], ![0, 104, 1], ![89, 66, 104]]]
  hmulB := by decide  
  f := ![![![6865, 66, 0], ![-13926, 0, 0]], ![![3224, 31, 0], ![-6540, 0, 0]], ![![5044, 48, 0], ![-10232, 1, 0]]]
  g := ![![![1, 0, 0], ![-104, 211, 0], ![-156, 0, 211]], ![![0, 1, 0], ![-52, 104, 1], ![-109, 66, 104]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N2 : Nat.card (O ⧸ I211N2) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N2)

lemma isPrimeI211N2 : Ideal.IsPrime I211N2 := prime_ideal_of_norm_prime hp211.out _ NI211N2
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![30, 1, 0]] ![![211, 0, 0], ![77, 1, 0]]
  ![![211, 0, 0], ![-11, -104, 1]] where
 M := ![![![44521, 0, 0], ![16247, 211, 0]], ![![6330, 211, 0], ![2310, 107, 1]]]
 hmul := by decide  
 g := ![![![![211, 0, 0], ![0, 0, 0]], ![![77, 1, 0], ![0, 0, 0]]], ![![![30, 1, 0], ![0, 0, 0]], ![![11, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI211N1 : IdealMulLeCertificate' Table 
  ![![211, 0, 0], ![-11, -104, 1]] ![![211, 0, 0], ![104, 1, 0]]
  ![![211, 0, 0]] where
 M := ![![![44521, 0, 0], ![21944, 211, 0]], ![![-2321, -21944, 211], ![-1055, -10761, 0]]]
 hmul := by decide  
 g := ![![![![211, 0, 0]], ![![104, 1, 0]]], ![![![-11, -104, 1]], ![![-5, -51, 0]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1, I211N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
    exact isPrimeI211N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0 ⊙ MulI211N1)


lemma PB216I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 215 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 215 (by omega)

def PB216I4 : PrimesBelowBoundCertificateInterval O 193 215 216 where
  m := 3
  g := ![2, 2, 3]
  P := ![197, 199, 211]
  hP := PB216I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1, I211N2]
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
    · exact ![38809, 197]
    · exact ![39601, 199]
    · exact ![211, 211, 211]
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
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
      exact NI211N2
  β := ![I197N1, I199N1, I211N0, I211N1, I211N2]
  Il := ![[I197N1], [I199N1], [I211N0, I211N1, I211N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
