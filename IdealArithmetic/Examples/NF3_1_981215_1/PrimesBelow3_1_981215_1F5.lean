
import IdealArithmetic.Examples.NF3_1_981215_1.RI3_1_981215_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![87565275944057, 5656962882846, 4915926156395]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![87565275944057, 5656962882846, 4915926156395]] 
 ![![263, 0, 0], ![0, 263, 0], ![32, 222, 1]] where
  M :=![![![87565275944057, 5656962882846, 4915926156395], ![933284932988599, 60292829185040, 52394739398516], ![657710261173616, 42489931025891, 36923940927205]]]
  hmulB := by decide  
  f := ![![![7422188, -642595, -76328]], ![![-13936053, 6181355, -6915889]], ![![-11302149, 5156011, -5811604]]]
  g := ![![![-265187684641, -4128055679988, 4915926156395], ![-2826413413551, -43997487898424, 52394739398516], ![-1991847332688, -31006178535413, 36923940927205]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 2 2 8 [132, 198, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 262], [0, 1]]
 g := ![![[133, 2], [98, 43], [174, 35], [198], [210], [144], [17], [1]], ![[0, 261], [0, 220], [82, 228], [198], [210], [144], [17], [1]]]
 h' := ![![[65, 262], [214, 110], [176, 147], [177, 185], [117, 120], [144, 90], [189, 251], [131, 65], [0, 1]], ![[0, 1], [0, 153], [0, 116], [104, 78], [27, 143], [208, 173], [198, 12], [148, 198], [65, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [140]]
 b := ![[], [92, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 2
  hpos := by decide
  P := [132, 198, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6717, 755, -3168]
  a := ![1, -4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![411, 2677, -3168]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7422188, -642595, -76328]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![7422188, -642595, -76328]] 
 ![![263, 0, 0], ![190, 1, 0], ![157, 0, 1]] where
  M :=![![![7422188, -642595, -76328], ![-13936053, 6181355, -6915889], ![-116171437, 4333123, 9318002]]]
  hmulB := by decide  
  f := ![![![87565275944057, 5656962882846, 4915926156395]], ![![66808697195283, 4316029570060, 3750649084082]], ![![54773606784755, 3538528911151, 3074997518940]]]
  g := ![![![538018, -642595, -76328], ![-390110, 6181355, -6915889], ![-9134567, 4333123, 9318002]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![87565275944057, 5656962882846, 4915926156395]] ![![7422188, -642595, -76328]]
  ![![263, 0, 0]] where
 M := ![![![263, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13790, 661, 898]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![-13790, 661, 898]] 
 ![![269, 0, 0], ![129, 1, 0], ![17, 0, 1]] where
  M :=![![![-13790, 661, 898], ![170857, -19889, 5475], ![49023, 11113, -22296]]]
  hmulB := by decide  
  f := ![![![-382601469, -24717130, -21479297]], ![![-198637242, -12832524, -11151521]], ![![-34862369, -2252207, -1957178]]]
  g := ![![![-425, 661, 898], ![9827, -19889, 5475], ![-3738, 11113, -22296]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N0 : Nat.card (O ⧸ I269N0) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N0)

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := prime_ideal_of_norm_prime hp269.out _ NI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-143976201493, -9301267187, -8082842967]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![-143976201493, -9301267187, -8082842967]] 
 ![![269, 0, 0], ![202, 1, 0], ![197, 0, 1]] where
  M :=![![![-143976201493, -9301267187, -8082842967], ![-1534521739510, -99134416351, -86148253123], ![-1081417537555, -69862611690, -60710923383]]]
  hmulB := by decide  
  f := ![![![-4627563, 449391, -21584]], ![![-3491969, 325992, 2329]], ![![-3062974, 312548, -35709]]]
  g := ![![![12368772620, -9301267187, -8082842967], ![131828387467, -99134416351, -86148253123], ![92902906804, -69862611690, -60710923383]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1

def I269N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![148, -16, 3]] i)))

def SI269N2: IdealEqSpanCertificate' Table ![![148, -16, 3]] 
 ![![269, 0, 0], ![206, 1, 0], ![72, 0, 1]] where
  M :=![![![148, -16, 3], ![589, 73, -182], ![-3314, 201, 156]]]
  hmulB := by decide  
  f := ![![![47970, 3099, 2693]], ![![38636, 2496, 2169]], ![![14179, 916, 796]]]
  g := ![![![12, -16, 3], ![-5, 73, -182], ![-208, 201, 156]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N2 : Nat.card (O ⧸ I269N2) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N2)

lemma isPrimeI269N2 : Ideal.IsPrime I269N2 := prime_ideal_of_norm_prime hp269.out _ NI269N2
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![-13790, 661, 898]] ![![-143976201493, -9301267187, -8082842967]]
  ![![47970, 3099, 2693]] where
 M := ![![![47970, 3099, 2693]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI269N1 : IdealMulLeCertificate' Table 
  ![![47970, 3099, 2693]] ![![148, -16, 3]]
  ![![269, 0, 0]] where
 M := ![![![269, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC269 : ContainsPrimesAboveP 269 ![I269N0, I269N1, I269N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
    exact isPrimeI269N1
    exact isPrimeI269N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 269 (by decide) (𝕀 ⊙ MulI269N0 ⊙ MulI269N1)
instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![351449849384, 22704647838, 19730440961]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![351449849384, 22704647838, 19730440961]] 
 ![![271, 0, 0], ![0, 271, 0], ![159, 50, 1]] where
  M :=![![![351449849384, 22704647838, 19730440961], ![3745809575713, 241989824249, 210290244296], ![2639769814412, 170536547717, 148197026020]]]
  hmulB := by decide  
  f := ![![![-410012, 18787, 27929]], ![![5315652, -605012, 150799]], ![![744565, -99269, 41733]]]
  g := ![![![-10279299865, -3556521772, 19730440961], ![-109558447481, -37905986681, 210290244296], ![-77208698608, -26713338573, 148197026020]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 2 2 8 [194, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [227, 270], [0, 1]]
 g := ![![[193, 126], [28, 87], [162, 53], [257, 139], [141], [151], [39], [1]], ![[69, 145], [265, 184], [269, 218], [103, 132], [141], [151], [39], [1]]]
 h' := ![![[227, 270], [259, 111], [8, 241], [6, 253], [99, 154], [95, 236], [260, 180], [77, 227], [0, 1]], ![[0, 1], [253, 160], [244, 30], [256, 18], [98, 117], [9, 35], [199, 91], [116, 44], [227, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [85, 164]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 2
  hpos := by decide
  P := [194, 44, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14685, 16336, -7348]
  a := ![-3, 6, 32]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4257, 1416, -7348]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-410012, 18787, 27929]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![-410012, 18787, 27929]] 
 ![![271, 0, 0], ![265, 1, 0], ![220, 0, 1]] where
  M :=![![![-410012, 18787, 27929], ![5315652, -605012, 150799], ![1186423, 361568, -671018]]]
  hmulB := by decide  
  f := ![![![351449849384, 22704647838, 19730440961]], ![![357490847463, 23094913289, 20069583391]], ![![295050688852, 19061103587, 16564184640]]]
  g := ![![![-42557, 18787, 27929], ![488812, -605012, 150799], ![195553, 361568, -671018]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![351449849384, 22704647838, 19730440961]] ![![-410012, 18787, 27929]]
  ![![271, 0, 0]] where
 M := ![![![271, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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
instance hp277 : Fact (Nat.Prime 277) := {out := by norm_num}

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 0, 0]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![277, 0, 0]] 
 ![![277, 0, 0], ![0, 277, 0], ![0, 0, 277]] where
  M :=![![![277, 0, 0], ![0, 277, 0], ![0, 0, 277]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 3 2 8 [20, 6, 173, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 133, 189], [34, 143, 88], [0, 1]]
 g := ![![[135, 201, 222], [184, 175], [220, 198, 164], [], [165, 172, 147], [235, 49], [104, 1], []], ![[82, 218, 240, 146], [86, 241], [28, 15, 193, 120], [214, 25], [269, 67, 54, 258], [154, 202], [268, 228], [274, 265]], ![[159, 19, 6, 69], [186, 189], [134, 266, 127, 74], [119, 25], [234, 29, 47, 63], [236, 218], [7, 238], [98, 265]]]
 h' := ![![[70, 133, 189], [114, 77, 105], [32, 190, 250], [22, 179, 21], [24, 148], [223, 276, 79], [136, 187, 7], [0, 0, 1], [0, 1]], ![[34, 143, 88], [4, 247, 206], [184, 37, 194], [95, 36, 270], [135, 17, 272], [38, 138, 28], [25, 235, 57], [251, 42, 143], [70, 133, 189]], ![[0, 1], [27, 230, 243], [223, 50, 110], [27, 62, 263], [70, 112, 5], [106, 140, 170], [35, 132, 213], [27, 235, 133], [34, 143, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 240], []]
 b := ![[], [225, 243, 179], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 3
  hpos := by decide
  P := [20, 6, 173, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-88960489, -58436751, -138332415]
  a := ![1, -66, -75]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-321157, -210963, -499395]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 21253933 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def PBC277 : ContainsPrimesAboveP 277 ![I277N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI277N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![277, 0, 0]]) timesTableT_eq_Table B_one_repr 277 (by decide) 𝕀



lemma PB281I5_primes (p : ℕ) :
  p ∈ Set.range ![263, 269, 271, 277] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 280 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 280 (by omega)

def PB281I5 : PrimesBelowBoundCertificateInterval O 257 280 281 where
  m := 4
  g := ![2, 3, 2, 1]
  P := ![263, 269, 271, 277]
  hP := PB281I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0, I263N1]
    · exact ![I269N0, I269N1, I269N2]
    · exact ![I271N0, I271N1]
    · exact ![I277N0]
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
    · exact ![69169, 263]
    · exact ![269, 269, 269]
    · exact ![73441, 271]
    · exact ![21253933]
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
      exact NI269N2
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
  β := ![I263N1, I269N0, I269N1, I269N2, I271N1]
  Il := ![[I263N1], [I269N0, I269N1, I269N2], [I271N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
