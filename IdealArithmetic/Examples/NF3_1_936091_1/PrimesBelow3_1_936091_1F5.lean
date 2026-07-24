
import IdealArithmetic.Examples.NF3_1_936091_1.RI3_1_936091_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![-9, 79, 1]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0], ![-9, 79, 1]] 
 ![![263, 0, 0], ![0, 263, 0], ![254, 79, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![-9, 79, 1], ![-194, 8, 80], ![-15520, 1166, 88]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-254, -79, 263]], ![![-1, 0, 1], ![-78, -24, 80], ![-144, -22, 88]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 2 2 8 [257, 131, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [132, 262], [0, 1]]
 g := ![![[22, 108], [169, 104], [184, 179], [62], [78], [206], [66], [1]], ![[76, 155], [221, 159], [142, 84], [62], [78], [206], [66], [1]]]
 h' := ![![[132, 262], [225, 125], [52, 34], [112, 210], [240, 59], [78, 135], [169, 39], [6, 132], [0, 1]], ![[0, 1], [156, 138], [69, 229], [217, 53], [138, 204], [14, 128], [57, 224], [72, 131], [132, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111]]
 b := ![[], [19, 187]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 2
  hpos := by decide
  P := [257, 131, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-325, -274, -110]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![105, 32, -110]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![-80, 1, 0]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![263, 0, 0], ![-80, 1, 0]] 
 ![![263, 0, 0], ![183, 1, 0], ![175, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![-80, 1, 0], ![0, -80, 1], ![-194, 17, -79]]]
  hmulB := by decide  
  f := ![![![20161, -252, 0], ![66276, 0, 0]], ![![14161, -177, 0], ![46552, 0, 0]], ![![13465, -168, 0], ![44264, 1, 0]]]
  g := ![![![1, 0, 0], ![-183, 263, 0], ![-175, 0, 263]], ![![-1, 1, 0], ![55, -80, 1], ![40, 17, -79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![-9, 79, 1]] ![![263, 0, 0], ![-80, 1, 0]]
  ![![263, 0, 0]] where
 M := ![![![69169, 0, 0], ![-21040, 263, 0]], ![![-2367, 20777, 263], ![526, -6312, 0]]]
 hmul := by decide  
 g := ![![![![263, 0, 0]], ![![-80, 1, 0]]], ![![![-9, 79, 1]], ![![2, -24, 0]]]]
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

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![-8, -44, 1]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![269, 0, 0], ![-8, -44, 1]] 
 ![![269, 0, 0], ![0, 269, 0], ![261, 225, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![-8, -44, 1], ![-194, 9, -43], ![8342, -925, -34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-261, -225, 269]], ![![-1, -1, 1], ![41, 36, -43], ![64, 25, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 2 2 8 [117, 152, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [117, 268], [0, 1]]
 g := ![![[268, 23], [58], [72, 89], [138, 164], [255], [57], [239], [1]], ![[0, 246], [58], [263, 180], [227, 105], [255], [57], [239], [1]]]
 h' := ![![[117, 268], [170, 125], [184, 199], [263, 122], [151, 83], [76, 229], [252, 47], [152, 117], [0, 1]], ![[0, 1], [0, 144], [64, 70], [11, 147], [178, 186], [238, 40], [102, 222], [122, 152], [117, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [242]]
 b := ![[], [50, 121]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 2
  hpos := by decide
  P := [117, 152, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![548, -2097, 604]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-584, -513, 604]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![43, 1, 0]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![269, 0, 0], ![43, 1, 0]] 
 ![![269, 0, 0], ![43, 1, 0], ![34, 0, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![43, 1, 0], ![0, 43, 1], ![-194, 17, 44]]]
  hmulB := by decide  
  f := ![![![7483, 174, 0], ![-46806, 0, 0]], ![![1161, 27, 0], ![-7262, 0, 0]], ![![910, 21, 0], ![-5692, 1, 0]]]
  g := ![![![1, 0, 0], ![-43, 269, 0], ![-34, 0, 269]], ![![0, 1, 0], ![-7, 43, 1], ![-9, 17, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![269, 0, 0], ![-8, -44, 1]] ![![269, 0, 0], ![43, 1, 0]]
  ![![269, 0, 0]] where
 M := ![![![72361, 0, 0], ![11567, 269, 0]], ![![-2152, -11836, 269], ![-538, -1883, 0]]]
 hmul := by decide  
 g := ![![![![269, 0, 0]], ![![43, 1, 0]]], ![![![-8, -44, 1]], ![![-2, -7, 0]]]]
 hle2 := by decide  


def PBC269 : ContainsPrimesAboveP 269 ![I269N0, I269N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
    exact isPrimeI269N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 269 (by decide) (𝕀 ⊙ MulI269N0)
instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0], ![66, -45, 1]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![271, 0, 0], ![66, -45, 1]] 
 ![![271, 0, 0], ![0, 271, 0], ![66, 226, 1]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]], ![![66, -45, 1], ![-194, 83, -44], ![8536, -942, 39]]]
  hmulB := by decide  
  f := ![![![-65, 45, -1], ![271, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -226, 271]], ![![0, -1, 1], ![10, 37, -44], ![22, -36, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 2 2 8 [244, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [192, 270], [0, 1]]
 g := ![![[248, 10], [35, 244], [139, 187], [79, 1], [34], [129], [8], [1]], ![[0, 261], [0, 27], [0, 84], [0, 270], [34], [129], [8], [1]]]
 h' := ![![[192, 270], [132, 84], [230, 171], [236, 27], [79, 1], [40, 247], [132, 251], [27, 192], [0, 1]], ![[0, 1], [0, 187], [0, 100], [0, 244], [0, 270], [39, 24], [86, 20], [35, 79], [192, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [11, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 2
  hpos := by decide
  P := [244, 79, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-522, -260, 66]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, -56, 66]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0], ![44, 1, 0]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![271, 0, 0], ![44, 1, 0]] 
 ![![271, 0, 0], ![44, 1, 0], ![232, 0, 1]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]], ![![44, 1, 0], ![0, 44, 1], ![-194, 17, 45]]]
  hmulB := by decide  
  f := ![![![5545, 126, 0], ![-34146, 0, 0]], ![![836, 19, 0], ![-5148, 0, 0]], ![![4672, 106, 0], ![-28770, 1, 0]]]
  g := ![![![1, 0, 0], ![-44, 271, 0], ![-232, 0, 271]], ![![0, 1, 0], ![-8, 44, 1], ![-42, 17, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![271, 0, 0], ![66, -45, 1]] ![![271, 0, 0], ![44, 1, 0]]
  ![![271, 0, 0]] where
 M := ![![![73441, 0, 0], ![11924, 271, 0]], ![![17886, -12195, 271], ![2710, -1897, 0]]]
 hmul := by decide  
 g := ![![![![271, 0, 0]], ![![44, 1, 0]]], ![![![66, -45, 1]], ![![10, -7, 0]]]]
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


lemma PB274I5_primes (p : ℕ) :
  p ∈ Set.range ![263, 269, 271] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 273 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 273 (by omega)

def PB274I5 : PrimesBelowBoundCertificateInterval O 257 273 274 where
  m := 3
  g := ![2, 2, 2]
  P := ![263, 269, 271]
  hP := PB274I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0, I263N1]
    · exact ![I269N0, I269N1]
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
    · exact ![72361, 269]
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
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
  β := ![I263N1, I269N1, I271N1]
  Il := ![[I263N1], [I269N1], [I271N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
