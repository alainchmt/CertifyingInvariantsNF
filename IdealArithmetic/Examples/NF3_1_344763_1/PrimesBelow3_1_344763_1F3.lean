
import IdealArithmetic.Examples.NF3_1_344763_1.RI3_1_344763_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0]] 
 ![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [94, 78, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 94, 137], [104, 44, 2], [0, 1]]
 g := ![![[78, 19, 30], [85, 5, 120], [69, 4], [120, 62, 47], [69, 107], [0, 1], []], ![[73, 92, 48, 65], [64, 44, 11, 71], [90, 117], [0, 27, 74, 42], [72, 124], [11, 129], [41, 4]], ![[54, 97, 103, 56], [113, 5, 80, 2], [117, 57], [56, 118, 26, 14], [26, 57], [46, 79], [37, 4]]]
 h' := ![![[35, 94, 137], [72, 26, 126], [71, 40, 113], [118, 87, 137], [47, 128, 73], [0, 45, 61], [0, 0, 1], [0, 1]], ![[104, 44, 2], [131, 62, 71], [47, 108, 27], [81, 81, 16], [121, 35, 37], [83, 85, 92], [12, 87, 44], [35, 94, 137]], ![[0, 1], [95, 51, 81], [120, 130, 138], [50, 110, 125], [122, 115, 29], [131, 9, 125], [110, 52, 94], [104, 44, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111, 13], []]
 b := ![[], [107, 45, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [94, 78, 0, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12788, -417, -417]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-92, -3, -3]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-7, 69, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-7, 69, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![142, 69, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-7, 69, 1], ![113, -7, 69], ![7797, 113, -7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-142, -69, 149]], ![![-1, 0, 1], ![-65, -32, 69], ![59, 4, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [39, 141, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 148], [0, 1]]
 g := ![![[38, 107], [112], [138, 1], [47], [41, 28], [64], [1]], ![[0, 42], [112], [146, 148], [47], [116, 121], [64], [1]]]
 h' := ![![[8, 148], [128, 133], [131, 75], [65, 1], [40, 135], [68, 37], [110, 8], [0, 1]], ![[0, 1], [0, 16], [135, 74], [73, 148], [77, 14], [66, 112], [25, 141], [8, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [123, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [39, 141, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1457, 739, 421]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-411, -190, 421]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-69, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-69, 1, 0]] 
 ![![149, 0, 0], ![80, 1, 0], ![7, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-69, 1, 0], ![0, -69, 1], ![113, 0, -69]]]
  hmulB := by decide  
  f := ![![![5659, -82, 0], ![12218, 0, 0]], ![![3106, -45, 0], ![6706, 0, 0]], ![![377, -5, 0], ![814, 1, 0]]]
  g := ![![![1, 0, 0], ![-80, 149, 0], ![-7, 0, 149]], ![![-1, 1, 0], ![37, -69, 1], ![4, 0, -69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-7, 69, 1]] ![![149, 0, 0], ![-69, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-10281, 149, 0]], ![![-1043, 10281, 149], ![596, -4768, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-69, 1, 0]]], ![![![-7, 69, 1]], ![![4, -32, 0]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [83, 94, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [142, 124, 137], [119, 26, 14], [0, 1]]
 g := ![![[122, 112, 121], [81, 59, 90], [105, 115, 69], [62, 18], [56, 9, 40], [110, 1], []], ![[11, 114, 107, 36], [63, 113, 84, 138], [42, 66, 129, 116], [16, 17], [13, 23, 127, 37], [69, 72], [119, 45]], ![[105, 55, 16, 79], [41, 15, 104, 13], [89, 11, 18, 142], [145, 39], [7, 38, 126, 134], [132, 125], [91, 45]]]
 h' := ![![[142, 124, 137], [72, 59, 11], [43, 11, 40], [20, 137, 89], [33, 97, 138], [81, 147, 77], [0, 0, 1], [0, 1]], ![[119, 26, 14], [52, 135, 64], [100, 29, 131], [25, 69, 94], [121, 61, 116], [70, 124, 95], [19, 61, 26], [142, 124, 137]], ![[0, 1], [53, 108, 76], [63, 111, 131], [133, 96, 119], [115, 144, 48], [4, 31, 130], [115, 90, 124], [119, 26, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74, 49], []]
 b := ![[], [28, 131, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [83, 94, 41, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-78671, -10268, -6946]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-521, -68, -46]
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

instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [116, 78, 154, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 58, 83], [75, 98, 74], [0, 1]]
 g := ![![[71, 131, 132], [14, 64], [8, 57, 52], [7, 109, 46], [103, 97, 51], [3, 1], []], ![[15, 154, 124, 91], [35, 4], [92, 1, 39, 135], [21, 95, 56, 116], [69, 22, 105, 53], [88, 27], [151, 138]], ![[151, 62, 39, 2], [141, 36], [156, 100, 130, 85], [46, 149, 87, 2], [72, 25, 90, 65], [152, 67], [3, 138]]]
 h' := ![![[85, 58, 83], [142, 43, 17], [14, 87, 8], [130, 97, 44], [141, 82, 108], [123, 121, 88], [0, 0, 1], [0, 1]], ![[75, 98, 74], [137, 134, 54], [127, 112, 155], [38, 155, 117], [21, 5, 120], [14, 1, 141], [71, 129, 98], [85, 58, 83]], ![[0, 1], [132, 137, 86], [85, 115, 151], [11, 62, 153], [17, 70, 86], [62, 35, 85], [96, 28, 58], [75, 98, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 40], []]
 b := ![[], [36, 59, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [116, 78, 154, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-450747, 159041, 2041]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2871, 1013, 13]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def PBC157 : ContainsPrimesAboveP 157 ![I157N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![157, 0, 0]]) timesTableT_eq_Table B_one_repr 157 (by decide) 𝕀

instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [5, 150, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 142, 84], [76, 20, 79], [0, 1]]
 g := ![![[113, 1, 58], [76, 141, 40], [129, 95], [119, 111], [103, 25], [13, 0, 1], []], ![[24, 119, 122, 55], [38, 143, 57, 146], [85, 118], [50, 22], [41, 53], [140, 142, 25, 22], [58, 47]], ![[83, 9, 133, 147], [73, 143, 147, 48], [138, 16], [56, 62], [114, 113], [138, 6, 96, 120], [63, 47]]]
 h' := ![![[87, 142, 84], [109, 134, 59], [103, 43, 140], [111, 66, 101], [124, 108, 33], [98, 6, 158], [0, 0, 1], [0, 1]], ![[76, 20, 79], [150, 160, 48], [79, 134, 55], [34, 155, 66], [11, 64, 115], [85, 64, 78], [107, 125, 20], [87, 142, 84]], ![[0, 1], [135, 32, 56], [18, 149, 131], [43, 105, 159], [117, 154, 15], [144, 93, 90], [82, 38, 142], [76, 20, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [151, 62], []]
 b := ![[], [100, 93, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [5, 150, 0, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12877, -489, -489]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-79, -3, -3]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀



lemma PB167I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 166 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 166 (by omega)

def PB167I3 : PrimesBelowBoundCertificateInterval O 137 166 167 where
  m := 5
  g := ![1, 2, 1, 1, 1]
  P := ![139, 149, 151, 157, 163]
  hP := PB167I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0]
    · exact ![I163N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
    · exact PBC163
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2685619]
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![3869893]
    · exact ![4330747]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
  β := ![I149N1]
  Il := ![[], [I149N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
