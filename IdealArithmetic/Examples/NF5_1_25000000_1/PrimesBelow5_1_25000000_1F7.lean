
import IdealArithmetic.Examples.NF5_1_25000000_1.RI5_1_25000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp311 : Fact (Nat.Prime 311) := {out := by norm_num}

def I311N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, -70, -272, -174, 416]] i)))

def SI311N0: IdealEqSpanCertificate' Table ![![67, -70, -272, -174, 416]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![262, 44, 1, 0, 0], ![97, 104, 0, 1, 0], ![147, 259, 0, 0, 1]] where
  M :=![![![67, -70, -272, -174, 416], ![-1316, 143, 82, -1050, 30], ![1980, 866, 4507, 5518, -7260], ![3840, -1606, -5322, -1257, 7834], ![-600, -484, -2312, -2476, 3675]]]
  hmulB := by decide  
  f := ![![![2085, 1934, -448, 510, -2224]], ![![7876, 617, -1002, 106, -3102]], ![![2910, 1738, -525, 450, -2340]], ![![3283, 804, -474, 193, -1726]], ![![7573, 1439, -1050, 332, -3651]]]
  g := ![![![87, -250, -272, -174, 416], ![240, 315, 82, -1050, 30], ![-2080, 3566, 4507, 5518, -7260], ![1185, -5356, -5322, -1257, 7834], ![981, -1907, -2312, -2476, 3675]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P0 : CertificateIrreducibleZModOfList' 311 2 2 8 [200, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [222, 310], [0, 1]]
 g := ![![[2, 14], [180, 16], [8, 56], [277], [167, 90], [129, 79], [146], [1]], ![[0, 297], [0, 295], [0, 255], [277], [243, 221], [251, 232], [146], [1]]]
 h' := ![![[222, 310], [76, 221], [266, 307], [159, 180], [188, 272], [13, 159], [226, 214], [111, 222], [0, 1]], ![[0, 1], [0, 90], [0, 4], [0, 131], [238, 39], [168, 152], [151, 97], [257, 89], [222, 310]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [168, 175]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N0 : CertifiedPrimeIdeal' SI311N0 311 where
  n := 2
  hpos := by decide
  P := [200, 89, 1]
  hirr := P311P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-35910, -3457, -22841, -47968, 40453]
  a := ![26, 17, 31, 30, -91]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14967, -14428, -22841, -47968, 40453]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N0 : Ideal.IsPrime I311N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N0 B_one_repr
lemma NI311N0 : Nat.card (O ⧸ I311N0) = 96721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N0

def I311N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1043, 393, -109, 90, -528]] i)))

def SI311N1: IdealEqSpanCertificate' Table ![![1043, 393, -109, 90, -528]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![122, 97, 1, 0, 0], ![246, 118, 0, 1, 0], ![99, 50, 0, 0, 1]] where
  M :=![![![1043, 393, -109, 90, -528], ![1932, 754, -185, 170, -954], ![3476, 1407, -296, 318, -1672], ![-708, -256, 80, -59, 377], ![2132, 876, -176, 194, -1007]]]
  hmulB := by decide  
  f := ![![![-4603, 5311, 155, 1462, -2328]], ![![6388, -7372, -227, -2034, 3250]], ![![158, -183, -9, -52, 86]], ![![-1198, 1382, 36, 379, -599]], ![![-443, 511, 13, 140, -221]]]
  g := ![![![143, 86, -109, 90, -528], ![248, 149, -185, 170, -954], ![408, 245, -296, 318, -1672], ![-107, -64, 80, -59, 377], ![243, 146, -176, 194, -1007]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P1 : CertificateIrreducibleZModOfList' 311 2 2 8 [186, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [280, 310], [0, 1]]
 g := ![![[52, 274], [214, 235], [130, 226], [14], [65, 13], [229, 14], [28], [1]], ![[266, 37], [82, 76], [277, 85], [14], [284, 298], [106, 297], [28], [1]]]
 h' := ![![[280, 310], [4, 213], [78, 70], [161, 55], [39, 90], [13, 18], [154, 90], [125, 280], [0, 1]], ![[0, 1], [243, 98], [85, 241], [11, 256], [48, 221], [77, 293], [163, 221], [153, 31], [280, 310]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [139]]
 b := ![[], [222, 225]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N1 : CertifiedPrimeIdeal' SI311N1 311 where
  n := 2
  hpos := by decide
  P := [186, 31, 1]
  hirr := P311P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2305776, -824713, -2908909, -3897410, 5391487]
  a := ![239, 117, 236, 172, -835]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2500279, 1516590, -2908909, -3897410, 5391487]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N1 : Ideal.IsPrime I311N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N1 B_one_repr
lemma NI311N1 : Nat.card (O ⧸ I311N1) = 96721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N1

def I311N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-42087, 48523, 1405, 13320, -21250]] i)))

def SI311N2: IdealEqSpanCertificate' Table ![![-42087, 48523, 1405, 13320, -21250]] 
 ![![311, 0, 0, 0, 0], ![170, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![184, 0, 0, 0, 1]] where
  M :=![![![-42087, 48523, 1405, 13320, -21250], ![58360, -67322, -1947, -18480, 29490], ![-81000, 93373, 2704, 25632, -40890], ![53984, -62246, -1802, -17087, 27261], ![-13772, 15860, 460, 4354, -6943]]]
  hmulB := by decide  
  f := ![![![727, 193, 977, 1396, -1678]], ![![410, 102, 523, 764, -902]], ![![-9, 14, 43, 24, -72]], ![![149, 53, 261, 339, -437]], ![![460, 116, 596, 866, -1025]]]
  g := ![![![-16632, 48523, 1405, 13320, -21250], ![23071, -67322, -1947, -18480, 29490], ![-32006, 93373, 2704, 25632, -40890], ![21335, -62246, -1802, -17087, 27261], ![-5438, 15860, 460, 4354, -6943]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N2 : Nat.card (O ⧸ I311N2) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N2)

lemma isPrimeI311N2 : Ideal.IsPrime I311N2 := prime_ideal_of_norm_prime hp311.out _ NI311N2
def MulI311N0 : IdealMulLeCertificate' Table 
  ![![67, -70, -272, -174, 416]] ![![1043, 393, -109, 90, -528]]
  ![![-727, -193, -977, -1396, 1678]] where
 M := ![![![-727, -193, -977, -1396, 1678]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI311N1 : IdealMulLeCertificate' Table 
  ![![-727, -193, -977, -1396, 1678]] ![![-42087, 48523, 1405, 13320, -21250]]
  ![![311, 0, 0, 0, 0]] where
 M := ![![![-311, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC311 : ContainsPrimesAboveP 311 ![I311N0, I311N1, I311N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI311N0
    exact isPrimeI311N1
    exact isPrimeI311N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 311 (by decide) (𝕀 ⊙ MulI311N0 ⊙ MulI311N1)


lemma PB312I7_primes (p : ℕ) :
  p ∈ Set.range ![311] ↔ Nat.Prime p ∧ 307 < p ∧ p ≤ 311 := by
  rw [← List.mem_ofFn']
  convert primes_range 307 311 (by omega)

def PB312I7 : PrimesBelowBoundCertificateInterval O 307 311 312 where
  m := 1
  g := ![3]
  P := ![311]
  hP := PB312I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I311N0, I311N1, I311N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC311
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![96721, 96721, 311]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI311N0
      exact NI311N1
      exact NI311N2
  β := ![I311N2]
  Il := ![[I311N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
