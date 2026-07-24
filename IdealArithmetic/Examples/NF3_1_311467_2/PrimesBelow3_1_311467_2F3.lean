
import IdealArithmetic.Examples.NF3_1_311467_2.RI3_1_311467_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-99, -33, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-99, -33, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![40, 106, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-99, -33, 1], ![-168, -56, -32], ![5376, -1544, -88]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-40, -106, 139]], ![![-1, -1, 1], ![8, 24, -32], ![64, 56, -88]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [41, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 138], [0, 1]]
 g := ![![[100, 78], [99, 80], [57], [99, 125], [31], [35], [1]], ![[0, 61], [0, 59], [57], [92, 14], [31], [35], [1]]]
 h' := ![![[70, 138], [111, 56], [115, 48], [111, 125], [31, 60], [107, 46], [98, 70], [0, 1]], ![[0, 1], [0, 83], [0, 91], [104, 14], [61, 79], [130, 93], [133, 69], [70, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [7, 111]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [41, 69, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-463, -108, -22]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, 16, -22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![32, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![32, 1, 0]] 
 ![![139, 0, 0], ![32, 1, 0], ![88, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![32, 1, 0], ![0, 32, 1], ![-168, 43, 33]]]
  hmulB := by decide  
  f := ![![![2433, 76, 0], ![-10564, 0, 0]], ![![544, 17, 0], ![-2362, 0, 0]], ![![1480, 46, 0], ![-6426, 1, 0]]]
  g := ![![![1, 0, 0], ![-32, 139, 0], ![-88, 0, 139]], ![![0, 1, 0], ![-8, 32, 1], ![-32, 43, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-99, -33, 1]] ![![139, 0, 0], ![32, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![4448, 139, 0]], ![![-13761, -4587, 139], ![-3336, -1112, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![32, 1, 0]]], ![![![-99, -33, 1]], ![![-24, -8, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-10, -14, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-10, -14, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![139, 135, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-10, -14, 1], ![-168, 33, -13], ![2184, -727, 20]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-139, -135, 149]], ![![-1, -1, 1], ![11, 12, -13], ![-4, -23, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [38, 127, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 148], [0, 1]]
 g := ![![[70, 130], [114], [119, 95], [25], [107, 104], [37], [1]], ![[99, 19], [114], [123, 54], [25], [11, 45], [37], [1]]]
 h' := ![![[22, 148], [11, 117], [97, 76], [5, 86], [106, 144], [38, 36], [111, 22], [0, 1]], ![[0, 1], [52, 32], [130, 73], [109, 63], [145, 5], [85, 113], [148, 127], [22, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [62, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [38, 127, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![416, -1891, 763]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-709, -704, 763]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![13, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![13, 1, 0]] 
 ![![149, 0, 0], ![13, 1, 0], ![129, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![13, 1, 0], ![0, 13, 1], ![-168, 43, 14]]]
  hmulB := by decide  
  f := ![![![274, 21, 0], ![-3129, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![236, 18, 0], ![-2695, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 149, 0], ![-129, 0, 149]], ![![0, 1, 0], ![-2, 13, 1], ![-17, 43, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-10, -14, 1]] ![![149, 0, 0], ![13, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![1937, 149, 0]], ![![-1490, -2086, 149], ![-298, -149, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![13, 1, 0]]], ![![![-10, -14, 1]], ![![-2, -1, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71873128337, -27869713536, 3245697745]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![71873128337, -27869713536, 3245697745]] 
 ![![151, 0, 0], ![0, 151, 0], ![139, 13, 1]] where
  M :=![![![71873128337, -27869713536, 3245697745], ![-545277221160, 211438131372, -24624015791], ![4136834652888, -1604109900173, 186814115581]]]
  hmulB := by decide  
  f := ![![![559439, -112619, -24564]], ![![4126752, -496813, -137183]], ![![1022891, -158177, -38621]]]
  g := ![![![-2511780518, -463998571, 3245697745], ![19056032939, 3520200905, -24624015791], ![-144571704721, -26706578826, 186814115581]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [42, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [119, 150], [0, 1]]
 g := ![![[123, 18], [62, 68], [148, 99], [39], [146, 55], [118], [1]], ![[0, 133], [0, 83], [0, 52], [39], [47, 96], [118], [1]]]
 h' := ![![[119, 150], [114, 13], [126, 70], [31, 34], [59, 103], [130, 120], [109, 119], [0, 1]], ![[0, 1], [0, 138], [0, 81], [0, 117], [85, 48], [65, 31], [76, 32], [119, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [139]]
 b := ![[], [55, 145]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [42, 32, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2258, -307, 139]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-113, -14, 139]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![559439, -112619, -24564]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![559439, -112619, -24564]] 
 ![![151, 0, 0], ![137, 1, 0], ![106, 0, 1]] where
  M :=![![![559439, -112619, -24564], ![4126752, -496813, -137183], ![23046744, -1772117, -633996]]]
  hmulB := by decide  
  f := ![![![71873128337, -27869713536, 3245697745]], ![![61598287159, -23885514060, 2781699174]], ![![77850240110, -30187414139, 3515616401]]]
  g := ![![![123126, -112619, -24564], ![574381, -496813, -137183], ![2205499, -1772117, -633996]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![71873128337, -27869713536, 3245697745]] ![![559439, -112619, -24564]]
  ![![151, 0, 0]] where
 M := ![![![151, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16763, -6496, -565]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-16763, -6496, -565]] 
 ![![157, 0, 0], ![0, 157, 0], ![23, 19, 1]] where
  M :=![![![-16763, -6496, -565], ![94920, -41058, -7061], ![1186248, -208703, -48119]]]
  hmulB := by decide  
  f := ![![![-3197567, 1239897, -144398]], ![![24258864, -9406681, 1095499]], ![![1295099, -502191, 58485]]]
  g := ![![![-24, 27, -565], ![1639, 593, -7061], ![14605, 4494, -48119]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [108, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [137, 156], [0, 1]]
 g := ![![[6, 16], [27], [119, 37], [44, 48], [7, 51], [86], [1]], ![[0, 141], [27], [7, 120], [26, 109], [86, 106], [86], [1]]]
 h' := ![![[137, 156], [80, 4], [22, 98], [115, 115], [29, 131], [21, 88], [49, 137], [0, 1]], ![[0, 1], [0, 153], [103, 59], [13, 42], [78, 26], [145, 69], [135, 20], [137, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [138, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [108, 20, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-375, -1361, 325]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-50, -48, 325]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3197567, 1239897, -144398]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-3197567, 1239897, -144398]] 
 ![![157, 0, 0], ![137, 1, 0], ![71, 0, 1]] where
  M :=![![![-3197567, 1239897, -144398], ![24258864, -9406681, 1095499], ![-184043832, 71365321, -8311182]]]
  hmulB := by decide  
  f := ![![![-16763, -6496, -565]], ![![-14023, -5930, -538]], ![![-25, -4267, -562]]]
  g := ![![![-1037014, 1239897, -144398], ![7867476, -9406681, 1095499], ![-59687891, 71365321, -8311182]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-16763, -6496, -565]] ![![-3197567, 1239897, -144398]]
  ![![157, 0, 0]] where
 M := ![![![157, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)


lemma PB158I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 157 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 157 (by omega)

def PB158I3 : PrimesBelowBoundCertificateInterval O 137 157 158 where
  m := 4
  g := ![2, 2, 2, 2]
  P := ![139, 149, 151, 157]
  hP := PB158I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![24649, 157]
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
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
  β := ![I139N1, I149N1, I151N1, I157N1]
  Il := ![[I139N1], [I149N1], [I151N1], [I157N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
