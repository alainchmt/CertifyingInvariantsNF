
import IdealArithmetic.Examples.NF3_1_977075_1.RI3_1_977075_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![61, 1, 0]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0], ![61, 1, 0]] 
 ![![263, 0, 0], ![61, 1, 0], ![224, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![61, 1, 0], ![0, 61, 1], ![-332, 73, 62]]]
  hmulB := by decide  
  f := ![![![3722, 61, 0], ![-16043, 0, 0]], ![![854, 14, 0], ![-3681, 0, 0]], ![![3126, 51, 0], ![-13474, 1, 0]]]
  g := ![![![1, 0, 0], ![-61, 263, 0], ![-224, 0, 263]], ![![0, 1, 0], ![-15, 61, 1], ![-71, 73, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N0 : Nat.card (O ⧸ I263N0) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N0)

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := prime_ideal_of_norm_prime hp263.out _ NI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0], ![82, 1, 0]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![263, 0, 0], ![82, 1, 0]] 
 ![![263, 0, 0], ![82, 1, 0], ![114, 0, 1]] where
  M :=![![![263, 0, 0], ![0, 263, 0], ![0, 0, 263]], ![![82, 1, 0], ![0, 82, 1], ![-332, 73, 83]]]
  hmulB := by decide  
  f := ![![![8693, 106, 0], ![-27878, 0, 0]], ![![2706, 33, 0], ![-8678, 0, 0]], ![![3798, 46, 0], ![-12180, 1, 0]]]
  g := ![![![1, 0, 0], ![-82, 263, 0], ![-114, 0, 263]], ![![0, 1, 0], ![-26, 82, 1], ![-60, 73, 83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1

def I263N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-557, 32, 9]] i)))

def SI263N2: IdealEqSpanCertificate' Table ![![-557, 32, 9]] 
 ![![263, 0, 0], ![119, 1, 0], ![41, 0, 1]] where
  M :=![![![-557, 32, 9], ![-2988, 100, 41], ![-13612, 5, 141]]]
  hmulB := by decide  
  f := ![![![-13895, 4467, -412]], ![![-5767, 1854, -171]], ![![-7285, 2342, -216]]]
  g := ![![![-18, 32, 9], ![-63, 100, 41], ![-76, 5, 141]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N2 : Nat.card (O ⧸ I263N2) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N2)

lemma isPrimeI263N2 : Ideal.IsPrime I263N2 := prime_ideal_of_norm_prime hp263.out _ NI263N2
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![263, 0, 0], ![61, 1, 0]] ![![263, 0, 0], ![82, 1, 0]]
  ![![13895, -4467, 412]] where
 M := ![![![69169, 0, 0], ![21566, 263, 0]], ![![16043, 263, 0], ![5002, 143, 1]]]
 hmul := by decide  
 g := ![![![![146491, -8416, -2367]], ![![48662, -2724, -779]]], ![![![36965, -2052, -590]], ![![12270, -663, -194]]]]
 hle2 := by decide  

def MulI263N1 : IdealMulLeCertificate' Table 
  ![![13895, -4467, 412]] ![![-557, 32, 9]]
  ![![263, 0, 0]] where
 M := ![![![-263, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC263 : ContainsPrimesAboveP 263 ![I263N0, I263N1, I263N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
    exact isPrimeI263N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 263 (by decide) (𝕀 ⊙ MulI263N0 ⊙ MulI263N1)
instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![269, 0, 0]] 
 ![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [103, 118, 148, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [180, 13, 241], [210, 255, 28], [0, 1]]
 g := ![![[121, 0, 208], [79, 172], [52, 179, 52], [120, 139, 131], [33, 54], [219, 9], [121, 1], []], ![[9, 60, 200, 46], [66, 166], [5, 112, 213, 31], [195, 217, 214, 158], [53, 25], [265, 20], [130, 196], [255, 246]], ![[158, 30, 85, 95], [66, 117], [131, 189, 57, 19], [191, 7, 35, 227], [140, 96], [114, 196], [8, 169], [199, 246]]]
 h' := ![![[180, 13, 241], [240, 185, 137], [24, 102, 21], [14, 78, 66], [93, 70, 249], [159, 145, 190], [180, 145, 266], [0, 0, 1], [0, 1]], ![[210, 255, 28], [54, 82, 165], [76, 51, 78], [131, 158, 120], [14, 126, 203], [239, 187, 5], [74, 261, 17], [217, 93, 255], [180, 13, 241]], ![[0, 1], [47, 2, 236], [89, 116, 170], [4, 33, 83], [33, 73, 86], [14, 206, 74], [171, 132, 255], [200, 176, 13], [210, 255, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [218, 63], []]
 b := ![[], [80, 140, 204], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [103, 118, 148, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-133693, 6725, 6725]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-497, 25, 25]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 19465109 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def PBC269 : ContainsPrimesAboveP 269 ![I269N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![269, 0, 0]]) timesTableT_eq_Table B_one_repr 269 (by decide) 𝕀

instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0], ![-125, 1, 0]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![271, 0, 0], ![-125, 1, 0]] 
 ![![271, 0, 0], ![146, 1, 0], ![93, 0, 1]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]], ![![-125, 1, 0], ![0, -125, 1], ![-332, 73, -124]]]
  hmulB := by decide  
  f := ![![![33501, -268, 0], ![72628, 0, 0]], ![![18126, -145, 0], ![39296, 0, 0]], ![![11683, -93, 0], ![25328, 1, 0]]]
  g := ![![![1, 0, 0], ![-146, 271, 0], ![-93, 0, 271]], ![![-1, 1, 0], ![67, -125, 1], ![2, 73, -124]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N0 : Nat.card (O ⧸ I271N0) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N0)

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := prime_ideal_of_norm_prime hp271.out _ NI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0], ![-75, 1, 0]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![271, 0, 0], ![-75, 1, 0]] 
 ![![271, 0, 0], ![196, 1, 0], ![66, 0, 1]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]], ![![-75, 1, 0], ![0, -75, 1], ![-332, 73, -74]]]
  hmulB := by decide  
  f := ![![![14476, -193, 0], ![52303, 0, 0]], ![![10576, -141, 0], ![38212, 0, 0]], ![![3546, -47, 0], ![12812, 1, 0]]]
  g := ![![![1, 0, 0], ![-196, 271, 0], ![-66, 0, 271]], ![![-1, 1, 0], ![54, -75, 1], ![-36, 73, -74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1

def I271N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0], ![-72, 1, 0]] i)))

def SI271N2: IdealEqSpanCertificate' Table ![![271, 0, 0], ![-72, 1, 0]] 
 ![![271, 0, 0], ![199, 1, 0], ![236, 0, 1]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]], ![![-72, 1, 0], ![0, -72, 1], ![-332, 73, -71]]]
  hmulB := by decide  
  f := ![![![6481, -90, 0], ![24390, 0, 0]], ![![4681, -65, 0], ![17616, 0, 0]], ![![5636, -78, 0], ![21210, 1, 0]]]
  g := ![![![1, 0, 0], ![-199, 271, 0], ![-236, 0, 271]], ![![-1, 1, 0], ![52, -72, 1], ![7, 73, -71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N2 : Nat.card (O ⧸ I271N2) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N2)

lemma isPrimeI271N2 : Ideal.IsPrime I271N2 := prime_ideal_of_norm_prime hp271.out _ NI271N2
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![271, 0, 0], ![-125, 1, 0]] ![![271, 0, 0], ![-75, 1, 0]]
  ![![271, 0, 0], ![-110, 71, 1]] where
 M := ![![![73441, 0, 0], ![-20325, 271, 0]], ![![-33875, 271, 0], ![9375, -200, 1]]]
 hmul := by decide  
 g := ![![![![271, 0, 0], ![0, 0, 0]], ![![35, -70, -1], ![271, 0, 0]]], ![![![-15, -70, -1], ![271, 0, 0]], ![![35, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI271N1 : IdealMulLeCertificate' Table 
  ![![271, 0, 0], ![-110, 71, 1]] ![![271, 0, 0], ![-72, 1, 0]]
  ![![271, 0, 0]] where
 M := ![![![73441, 0, 0], ![-19512, 271, 0]], ![![-29810, 19241, 271], ![7588, -5149, 0]]]
 hmul := by decide  
 g := ![![![![271, 0, 0]], ![![-72, 1, 0]]], ![![![-110, 71, 1]], ![![28, -19, 0]]]]
 hle2 := by decide  


def PBC271 : ContainsPrimesAboveP 271 ![I271N0, I271N1, I271N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI271N0
    exact isPrimeI271N1
    exact isPrimeI271N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 271 (by decide) (𝕀 ⊙ MulI271N0 ⊙ MulI271N1)
instance hp277 : Fact (Nat.Prime 277) := {out := by norm_num}

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 0, 0], ![-32, 44, 1]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![277, 0, 0], ![-32, 44, 1]] 
 ![![277, 0, 0], ![0, 277, 0], ![245, 44, 1]] where
  M :=![![![277, 0, 0], ![0, 277, 0], ![0, 0, 277]], ![![-32, 44, 1], ![-332, 41, 45], ![-14940, 2953, 86]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-245, -44, 277]], ![![-1, 0, 1], ![-41, -7, 45], ![-130, -3, 86]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 2 2 8 [93, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [269, 276], [0, 1]]
 g := ![![[12, 122], [52], [62, 146], [210], [18, 186], [250], [64], [1]], ![[144, 155], [52], [2, 131], [210], [192, 91], [250], [64], [1]]]
 h' := ![![[269, 276], [258, 251], [51, 69], [4, 223], [265, 140], [84, 98], [204, 145], [184, 269], [0, 1]], ![[0, 1], [189, 26], [53, 208], [159, 54], [253, 137], [131, 179], [152, 132], [248, 8], [269, 276]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [36, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 2
  hpos := by decide
  P := [93, 8, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1082, -3219, 676]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-594, -119, 676]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 76729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 0, 0], ![-45, 1, 0]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![277, 0, 0], ![-45, 1, 0]] 
 ![![277, 0, 0], ![232, 1, 0], ![191, 0, 1]] where
  M :=![![![277, 0, 0], ![0, 277, 0], ![0, 0, 277]], ![![-45, 1, 0], ![0, -45, 1], ![-332, 73, -44]]]
  hmulB := by decide  
  f := ![![![9766, -217, 0], ![60109, 0, 0]], ![![8146, -181, 0], ![50138, 0, 0]], ![![6758, -150, 0], ![41595, 1, 0]]]
  g := ![![![1, 0, 0], ![-232, 277, 0], ![-191, 0, 277]], ![![-1, 1, 0], ![37, -45, 1], ![-32, 73, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N1 : Nat.card (O ⧸ I277N1) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N1)

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := prime_ideal_of_norm_prime hp277.out _ NI277N1
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![277, 0, 0], ![-32, 44, 1]] ![![277, 0, 0], ![-45, 1, 0]]
  ![![277, 0, 0]] where
 M := ![![![76729, 0, 0], ![-12465, 277, 0]], ![![-8864, 12188, 277], ![1108, -1939, 0]]]
 hmul := by decide  
 g := ![![![![277, 0, 0]], ![![-45, 1, 0]]], ![![![-32, 44, 1]], ![![4, -7, 0]]]]
 hle2 := by decide  


def PBC277 : ContainsPrimesAboveP 277 ![I277N0, I277N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI277N0
    exact isPrimeI277N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 277 (by decide) (𝕀 ⊙ MulI277N0)


lemma PB280I5_primes (p : ℕ) :
  p ∈ Set.range ![263, 269, 271, 277] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 279 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 279 (by omega)

def PB280I5 : PrimesBelowBoundCertificateInterval O 257 279 280 where
  m := 4
  g := ![3, 1, 3, 2]
  P := ![263, 269, 271, 277]
  hP := PB280I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0, I263N1, I263N2]
    · exact ![I269N0]
    · exact ![I271N0, I271N1, I271N2]
    · exact ![I277N0, I277N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC263
    · exact PBC269
    · exact PBC271
    · exact PBC277
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![263, 263, 263]
    · exact ![19465109]
    · exact ![271, 271, 271]
    · exact ![76729, 277]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
      exact NI263N2
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
      exact NI271N2
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
      exact NI277N1
  β := ![I263N0, I263N1, I263N2, I271N0, I271N1, I271N2, I277N1]
  Il := ![[I263N0, I263N1, I263N2], [], [I271N0, I271N1, I271N2], [I277N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
