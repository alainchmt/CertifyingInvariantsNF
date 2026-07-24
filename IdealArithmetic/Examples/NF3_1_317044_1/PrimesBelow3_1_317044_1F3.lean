
import IdealArithmetic.Examples.NF3_1_317044_1.RI3_1_317044_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![17, -9, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![17, -9, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![17, 130, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![17, -9, 1], ![-70, -12, -45], ![644, 166, -3]]]
  hmulB := by decide  
  f := ![![![-16, 9, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -130, 139]], ![![0, -1, 1], ![5, 42, -45], ![5, 4, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [78, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 138], [0, 1]]
 g := ![![[127, 41], [30, 106], [64], [76, 28], [117], [118], [1]], ![[0, 98], [0, 33], [64], [13, 111], [117], [118], [1]]]
 h' := ![![[102, 138], [23, 72], [50, 84], [49, 8], [0, 81], [77, 16], [61, 102], [0, 1]], ![[0, 1], [0, 67], [0, 55], [31, 131], [61, 58], [41, 123], [40, 37], [102, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [31, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [78, 37, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1308, -1924, -1933]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![227, 1794, -1933]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![45, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![45, 1, 0]] 
 ![![139, 0, 0], ![45, 1, 0], ![3, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![45, 1, 0], ![0, 46, 5], ![-70, -20, 45]]]
  hmulB := by decide  
  f := ![![![631, 14, 0], ![-1946, 0, 0]], ![![135, 3, 0], ![-416, 0, 0]], ![![-33, -10, -1], ![102, 28, 0]]]
  g := ![![![1, 0, 0], ![-45, 139, 0], ![-3, 0, 139]], ![![0, 1, 0], ![-15, 46, 5], ![5, -20, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![17, -9, 1]] ![![139, 0, 0], ![45, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![6255, 139, 0]], ![![2363, -1251, 139], ![695, -417, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![45, 1, 0]]], ![![![17, -9, 1]], ![![5, -3, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [98, 45, 133, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 33, 143], [103, 115, 6], [0, 1]]
 g := ![![[121, 23, 6], [119, 132], [135, 112, 118], [10, 73], [51, 4, 119], [16, 1], []], ![[85, 29, 8, 73], [76, 35], [51, 55, 52, 145], [104, 54], [120, 47, 22, 45], [57, 113], [31, 36]], ![[128, 4, 48, 143], [88, 20], [23, 88, 72, 114], [124, 25], [57, 78, 15, 104], [5, 46], [19, 36]]]
 h' := ![![[62, 33, 143], [27, 41, 30], [31, 89, 70], [68, 87, 72], [68, 119, 64], [71, 76, 62], [0, 0, 1], [0, 1]], ![[103, 115, 6], [78, 114, 75], [134, 46, 66], [20, 106, 10], [26, 62, 90], [72, 7, 118], [61, 63, 115], [62, 33, 143]], ![[0, 1], [99, 143, 44], [9, 14, 13], [50, 105, 67], [122, 117, 144], [105, 66, 118], [105, 86, 33], [103, 115, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 77], []]
 b := ![[], [97, 116, 137], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [98, 45, 133, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![407515, 123223, 1341]
  a := ![-1, 1, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2735, 827, 9]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀

instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79461, -2188, 3524]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![79461, -2188, 3524]] 
 ![![151, 0, 0], ![0, 151, 0], ![128, 40, 1]] where
  M :=![![![79461, -2188, 3524], ![-246680, 6793, -10940], ![202496, -5576, 8981]]]
  hmulB := by decide  
  f := ![![![43, 4, -12]], ![![840, 287, 20]], ![![256, 80, -3]]]
  g := ![![![-2461, -948, 3524], ![7640, 2943, -10940], ![-6272, -2416, 8981]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [122, 131, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 150], [0, 1]]
 g := ![![[84, 74], [22, 19], [83, 110], [128], [98, 34], [98], [1]], ![[54, 77], [100, 132], [18, 41], [128], [23, 117], [98], [1]]]
 h' := ![![[20, 150], [34, 15], [142, 87], [62, 84], [124, 85], [59, 100], [29, 20], [0, 1]], ![[0, 1], [32, 136], [70, 64], [81, 67], [12, 66], [96, 51], [127, 131], [20, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103]]
 b := ![[], [89, 127]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [122, 131, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4152, -14, -23]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8, 6, -23]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 4, -12]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![43, 4, -12]] 
 ![![151, 0, 0], ![102, 1, 0], ![43, 0, 1]] where
  M :=![![![43, 4, -12], ![840, 287, 20], ![-448, 88, 283]]]
  hmulB := by decide  
  f := ![![![79461, -2188, 3524]], ![![52042, -1433, 2308]], ![![23969, -660, 1063]]]
  g := ![![![1, 4, -12], ![-194, 287, 20], ![-143, 88, 283]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![79461, -2188, 3524]] ![![43, 4, -12]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15591789147379021, 944034667882962, -4968272857889096]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![15591789147379021, 944034667882962, -4968272857889096]] 
 ![![157, 0, 0], ![0, 157, 0], ![88, 139, 1]] where
  M :=![![![15591789147379021, 944034667882962, -4968272857889096], ![347779100052236720, 115901280973043903, 4720173339414810], ![-135638246762254684, 50675126652788104, 114957246305160941]]]
  hmulB := by decide  
  f := ![![![-83340743452891159382207699263519, 2294850204812560014730061031218, -3696084049196028083296719506044]], ![![258725883443721965830770365423080, -7124212264158037701543248111421, 11474251024062800073650305156090]], ![![180996991616543360704748693715596, -4983888624853304244246581301147, 8027047347429988160452278923707]]]
  g := ![![![2884075163322417, 4404674916652658, -4968272857889096], ![-430548750422080, -3440782249717291, 4720173339414810], ![-65298572749149156, -101454663119519635, 114957246305160941]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [97, 91, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 156], [0, 1]]
 g := ![![[111, 56], [46], [66, 90], [122, 46], [85, 67], [117], [1]], ![[39, 101], [46], [40, 67], [18, 111], [111, 90], [117], [1]]]
 h' := ![![[66, 156], [60, 29], [35, 49], [98, 103], [76, 49], [101, 99], [60, 66], [0, 1]], ![[0, 1], [90, 128], [129, 108], [145, 54], [13, 108], [41, 58], [20, 91], [66, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135]]
 b := ![[], [49, 146]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [97, 91, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1197, -2756, -3423]
  a := ![1, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1911, 3013, -3423]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37742967, 46822, -14753478]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![37742967, 46822, -14753478]] 
 ![![157, 0, 0], ![90, 1, 0], ![89, 0, 1]] where
  M :=![![![37742967, 46822, -14753478], ![1032743460, 332859349, 234110], ![-209826232, 205612252, 332812527]]]
  hmulB := by decide  
  f := ![![![110731625191949203, -3049078784551650, 4910844044064242]], ![![61287179517139690, -1687588694799591, 2718029108554290]], ![![64568802379738815, -1777950654464734, 2863566014218993]]]
  g := ![![![8576997, 46822, -14753478], ![-184365820, 332859349, 234110], ![-307867795, 205612252, 332812527]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![15591789147379021, 944034667882962, -4968272857889096]] ![![37742967, 46822, -14753478]]
  ![![157, 0, 0]] where
 M := ![![![2605899985848626064590099, -706576967124640474771192, -1883315554869978989256810]]]
 hmul := by decide  
 g := ![![![![16598089081838382577007, -4500490236462678183256, -11995640476878847065330]]]]
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


lemma PB160I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 159 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 159 (by omega)

def PB160I3 : PrimesBelowBoundCertificateInterval O 137 159 160 where
  m := 4
  g := ![2, 1, 2, 2]
  P := ![139, 149, 151, 157]
  hP := PB160I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
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
    · exact ![3307949]
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
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
  β := ![I139N1, I151N1, I157N1]
  Il := ![[I139N1], [], [I151N1], [I157N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
