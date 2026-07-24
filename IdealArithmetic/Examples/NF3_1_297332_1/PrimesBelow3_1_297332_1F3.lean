
import IdealArithmetic.Examples.NF3_1_297332_1.RI3_1_297332_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![40, 61, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![40, 61, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![40, 61, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![40, 61, 1], ![154, 75, 122], ![9394, 2212, 75]]]
  hmulB := by decide  
  f := ![![![-39, -61, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-40, -61, 139]], ![![0, 0, 1], ![-34, -53, 122], ![46, -17, 75]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [136, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [127, 138], [0, 1]]
 g := ![![[135, 46], [72, 6], [24], [16, 120], [49], [5], [1]], ![[0, 93], [0, 133], [24], [105, 19], [49], [5], [1]]]
 h' := ![![[127, 138], [77, 18], [13, 59], [48, 118], [28, 26], [24, 7], [3, 127], [0, 1]], ![[0, 1], [0, 121], [0, 80], [22, 21], [133, 113], [79, 132], [8, 12], [127, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [32, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [136, 12, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![444, 135, 25]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4, -10, 25]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![17, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![17, 1, 0]] 
 ![![139, 0, 0], ![17, 1, 0], ![64, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![17, 1, 0], ![0, 17, 2], ![154, 35, 17]]]
  hmulB := by decide  
  f := ![![![1259, 74, 0], ![-10286, 0, 0]], ![![153, 9, 0], ![-1250, 0, 0]], ![![588, 26, -1], ![-4804, 70, 0]]]
  g := ![![![1, 0, 0], ![-17, 139, 0], ![-64, 0, 139]], ![![0, 1, 0], ![-3, 17, 2], ![-11, 35, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![40, 61, 1]] ![![139, 0, 0], ![17, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![2363, 139, 0]], ![![5560, 8479, 139], ![834, 1112, 139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![17, 1, 0]]], ![![![40, 61, 1]], ![![6, 8, 1]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![49, -41, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![49, -41, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![49, 108, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![49, -41, 1], ![154, 84, -82], ![-6314, -1358, 84]]]
  hmulB := by decide  
  f := ![![![-48, 41, -1], ![149, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -108, 149]], ![![0, -1, 1], ![28, 60, -82], ![-70, -70, 84]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [37, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 148], [0, 1]]
 g := ![![[62, 145], [125], [49, 143], [63], [44, 144], [54], [1]], ![[0, 4], [125], [105, 6], [63], [41, 5], [54], [1]]]
 h' := ![![[90, 148], [23, 61], [124, 42], [25, 128], [11, 19], [116, 137], [112, 90], [0, 1]], ![[0, 1], [0, 88], [30, 107], [72, 21], [82, 130], [79, 12], [17, 59], [90, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111]]
 b := ![[], [110, 130]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [37, 59, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1869, 159, 494]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-175, -357, 494]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-67, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-67, 1, 0]] 
 ![![149, 0, 0], ![82, 1, 0], ![65, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-67, 1, 0], ![0, -67, 2], ![154, 35, -67]]]
  hmulB := by decide  
  f := ![![![9582, -143, 0], ![21307, 0, 0]], ![![5294, -79, 0], ![11772, 0, 0]], ![![4270, -30, -1], ![9495, 75, 0]]]
  g := ![![![1, 0, 0], ![-82, 149, 0], ![-65, 0, 149]], ![![-1, 1, 0], ![36, -67, 2], ![11, 35, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![49, -41, 1]] ![![149, 0, 0], ![-67, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-9983, 149, 0]], ![![7301, -6109, 149], ![-3129, 2831, -149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-67, 1, 0]]], ![![![49, -41, 1]], ![![-21, 19, -1]]]]
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
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [60, 64, 111, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 112, 144], [149, 38, 7], [0, 1]]
 g := ![![[105, 47, 103], [128, 4, 22], [57, 103, 105], [138, 91], [67, 124, 72], [40, 1], []], ![[103, 3, 119, 86], [47, 25, 114, 105], [15, 49, 17, 21], [115, 76], [88, 76], [130, 85], [90, 49]], ![[78, 123, 27, 120], [92, 67, 150, 15], [110, 11, 90, 23], [85, 38], [42, 60, 124, 51], [96, 11], [76, 49]]]
 h' := ![![[42, 112, 144], [21, 115, 109], [53, 26, 18], [103, 56, 16], [57, 4, 53], [16, 98, 26], [0, 0, 1], [0, 1]], ![[149, 38, 7], [70, 56, 15], [23, 103, 49], [149, 84, 65], [42, 71, 23], [45, 90], [139, 104, 38], [42, 112, 144]], ![[0, 1], [128, 131, 27], [137, 22, 84], [28, 11, 70], [30, 76, 75], [50, 114, 125], [125, 47, 112], [149, 38, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [149, 78], []]
 b := ![[], [64, 82, 119], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [60, 64, 111, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![218044, -4530, -2114]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1444, -30, -14]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def PBC151 : ContainsPrimesAboveP 151 ![I151N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![151, 0, 0]]) timesTableT_eq_Table B_one_repr 151 (by decide) 𝕀



lemma PB155I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 154 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 154 (by omega)

def PB155I3 : PrimesBelowBoundCertificateInterval O 137 154 155 where
  m := 3
  g := ![2, 2, 1]
  P := ![139, 149, 151]
  hP := PB155I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![3442951]
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
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
  β := ![I139N1, I149N1]
  Il := ![[I139N1], [I149N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
