
import IdealArithmetic.Examples.NF3_1_561295_1.RI3_1_561295_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-141, 5, -6]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-141, 5, -6]] 
 ![![197, 0, 0], ![29, 1, 0], ![179, 0, 1]] where
  M :=![![![-141, 5, -6], ![479, -18, 21], ![-11, -1, -1]]]
  hmulB := by decide  
  f := ![![![-39, -11, 3]], ![![-7, -2, 0]], ![![-32, -9, 2]]]
  g := ![![![4, 5, -6], ![-14, -18, 21], ![1, -1, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![31, 1, 0]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![197, 0, 0], ![31, 1, 0]] 
 ![![197, 0, 0], ![31, 1, 0], ![35, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![31, 1, 0], ![1, 28, 9], ![-79, -23, 35]]]
  hmulB := by decide  
  f := ![![![-3582, -104659, -33642], ![-985, 736386, 0]], ![![-588, -16464, -5292], ![1, 115836, 0]], ![![-660, -18595, -5977], ![-25, 130830, 0]]]
  g := ![![![1, 0, 0], ![-31, 197, 0], ![-35, 0, 197]], ![![0, 1, 0], ![-6, 28, 9], ![-3, -23, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0], ![-61, 1, 0]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![197, 0, 0], ![-61, 1, 0]] 
 ![![197, 0, 0], ![136, 1, 0], ![26, 0, 1]] where
  M :=![![![197, 0, 0], ![0, 197, 0], ![0, 0, 197]], ![![-61, 1, 0], ![1, -64, 9], ![-79, -23, -57]]]
  hmulB := by decide  
  f := ![![![23956, -1864875, 262260], ![-16745, -5740580, 0]], ![![16518, -1287365, 181044], ![-11622, -3962852, 0]], ![![3184, -246126, 34613], ![-2138, -757640, 0]]]
  g := ![![![1, 0, 0], ![-136, 197, 0], ![-26, 0, 197]], ![![-1, 1, 0], ![43, -64, 9], ![23, -23, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-141, 5, -6]] ![![197, 0, 0], ![31, 1, 0]]
  ![![197, 0, 0], ![100, 72, 1]] where
 M := ![![![-27777, 985, -1182], ![-3892, 137, -165]]]
 hmul := by decide  
 g := ![![![![-141, 5, -6], ![0, 0, 0]], ![![-36, -11, -1], ![32, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![197, 0, 0], ![100, 72, 1]] ![![197, 0, 0], ![-61, 1, 0]]
  ![![197, 0, 0]] where
 M := ![![![38809, 0, 0], ![-12017, 197, 0]], ![![19700, 14184, 197], ![-6107, -4531, 591]]]
 hmul := by decide  
 g := ![![![![197, 0, 0]], ![![-61, 1, 0]]], ![![![100, 72, 1]], ![![-31, -23, 3]]]]
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

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![97, -14, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![97, -14, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![97, 185, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![97, -14, 1], ![-93, 116, -122], ![1042, 303, 21]]]
  hmulB := by decide  
  f := ![![![-96, 14, -1], ![199, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-97, -185, 199]], ![![0, -1, 1], ![59, 114, -122], ![-5, -18, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [76, 175, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 198], [0, 1]]
 g := ![![[73, 175], [1, 121], [6, 56], [61], [26], [56], [24, 1]], ![[94, 24], [119, 78], [156, 143], [61], [26], [56], [48, 198]]]
 h' := ![![[24, 198], [123, 162], [141, 188], [11, 102], [104, 114], [17, 184], [166, 102], [0, 1]], ![[0, 1], [31, 37], [76, 11], [71, 97], [54, 85], [55, 15], [27, 97], [24, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [123, 139]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [76, 175, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2434, -377, -3285]
  a := ![-1, 2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1589, 3052, -3285]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-77, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-77, 1, 0]] 
 ![![199, 0, 0], ![122, 1, 0], ![178, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-77, 1, 0], ![1, -80, 9], ![-79, -23, -73]]]
  hmulB := by decide  
  f := ![![![-1149, 128954, -14508], ![1194, 320788, 0]], ![![-679, 79036, -8892], ![797, 196612, 0]], ![![-1044, 115346, -12977], ![1026, 286936, 0]]]
  g := ![![![1, 0, 0], ![-122, 199, 0], ![-178, 0, 199]], ![![-1, 1, 0], ![41, -80, 9], ![79, -23, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![97, -14, 1]] ![![199, 0, 0], ![-77, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![-15323, 199, 0]], ![![19303, -2786, 199], ![-7562, 1194, -199]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![-77, 1, 0]]], ![![![97, -14, 1]], ![![-38, 6, -1]]]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0]] 
 ![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [199, 33, 187, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 179, 83], [155, 31, 128], [0, 1]]
 g := ![![[77, 167, 144], [62, 105, 136], [147, 144], [129, 4], [161, 55, 49], [2, 154], [1]], ![[152, 107, 26, 93], [197, 54, 12, 178], [39, 51], [21, 134], [84, 203, 166, 36], [197, 143], [182, 20, 11, 188]], ![[8, 158, 190, 98], [158, 118, 129, 192], [161, 125], [71, 171], [33, 65, 190, 77], [89, 120], [172, 53, 0, 23]]]
 h' := ![![[80, 179, 83], [111, 30, 12], [129, 48, 66], [105, 205, 12], [33, 150, 209], [168, 146, 7], [12, 178, 24], [0, 1]], ![[155, 31, 128], [121, 76, 119], [108, 153, 122], [189, 173, 85], [123, 21, 150], [150, 82, 97], [188, 174, 115], [80, 179, 83]], ![[0, 1], [189, 105, 80], [147, 10, 23], [89, 44, 114], [202, 40, 63], [86, 194, 107], [101, 70, 72], [155, 31, 128]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 205], []]
 b := ![[], [166, 43, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [199, 33, 187, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3587211, 1001406, 1839709]
  a := ![2, -9, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17001, 4746, 8719]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def PBC211 : ContainsPrimesAboveP 211 ![I211N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![211, 0, 0]]) timesTableT_eq_Table B_one_repr 211 (by decide) 𝕀



lemma PB212I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 211 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 211 (by omega)

def PB212I4 : PrimesBelowBoundCertificateInterval O 193 211 212 where
  m := 3
  g := ![3, 2, 1]
  P := ![197, 199, 211]
  hP := PB212I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
    · exact ![I199N0, I199N1]
    · exact ![I211N0]
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
    · exact ![197, 197, 197]
    · exact ![39601, 199]
    · exact ![9393931]
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
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
  β := ![I197N0, I197N1, I197N2, I199N1]
  Il := ![[I197N0, I197N1, I197N2], [I199N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
