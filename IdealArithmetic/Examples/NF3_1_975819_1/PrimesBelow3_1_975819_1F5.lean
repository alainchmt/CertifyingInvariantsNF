
import IdealArithmetic.Examples.NF3_1_975819_1.RI3_1_975819_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![78258124758421787580557, -13638729388402610928347, 4428116074940117884784]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![78258124758421787580557, -13638729388402610928347, 4428116074940117884784]] 
 ![![263, 0, 0], ![0, 263, 0], ![227, 256, 1]] where
  M :=![![![78258124758421787580557, -13638729388402610928347, 4428116074940117884784], ![-1283444899405469672039370, 223677192904281163230439, -72621763016953172526519], ![4754418703107471932125720, -828594223168689724486061, 269021497144429113900264]]]
  hmulB := by decide  
  f := ![![![561684131499, 24685157368, -2581663141]], ![![714801975000, 510369583736, 126007449981]], ![![1151203678481, 522410025577, 122074532740]]]
  g := ![![![-3524426708186254647397, -4362115758832976385677, 4428116074940117884784], ![57801122834383652058861, 71539348004731153346081, -72621763016953172526519], ![-214119624139459836210016, -265011777536663661151915, 269021497144429113900264]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 2 2 8 [198, 184, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 262], [0, 1]]
 g := ![![[70, 89], [109, 225], [2, 243], [1], [181], [69], [192], [1]], ![[0, 174], [0, 38], [0, 20], [1], [181], [69], [192], [1]]]
 h' := ![![[79, 262], [247, 160], [130, 15], [216, 207], [199, 262], [100, 60], [136, 190], [65, 79], [0, 1]], ![[0, 1], [0, 103], [0, 248], [0, 56], [120, 1], [106, 203], [155, 73], [257, 184], [79, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128]]
 b := ![[], [102, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 2
  hpos := by decide
  P := [198, 184, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4278, -1051, 75]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-81, -77, 75]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-561684131499, -24685157368, 2581663141]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![-561684131499, -24685157368, 2581663141]] 
 ![![263, 0, 0], ![36, 1, 0], ![252, 0, 1]] where
  M :=![![![-561684131499, -24685157368, 2581663141], ![-714801975000, -510369583736, -126007449981], ![7725036009770, -1135692567799, -433732448491]]]
  hmulB := by decide  
  f := ![![![-78258124758421787580557, 13638729388402610928347, -4428116074940117884784]], ![![-5832120121284086239014, 1016414696114877681331, -330001580535707495535]], ![![-93062608905816587081468, 16218836612342766838135, -5265805125586839623064]]]
  g := ![![![-1230409041, -24685157368, 2581663141], ![187879773516, -510369583736, -126007449981], ![600420324982, -1135692567799, -433732448491]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![78258124758421787580557, -13638729388402610928347, 4428116074940117884784]] ![![-561684131499, -24685157368, 2581663141]]
  ![![263, 0, 0]] where
 M := ![![![-263, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![-99, 51, 1]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![269, 0, 0], ![-99, 51, 1]] 
 ![![269, 0, 0], ![0, 269, 0], ![170, 51, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![-99, 51, 1], ![-398, 42, 254], ![-14934, 1922, -110]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-170, -51, 269]], ![![-1, 0, 1], ![-162, -48, 254], ![14, 28, -110]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 2 2 8 [146, 131, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [138, 268], [0, 1]]
 g := ![![[257, 202], [44], [120, 20], [4, 228], [23], [16], [214], [1]], ![[157, 67], [44], [190, 249], [264, 41], [23], [16], [214], [1]]]
 h' := ![![[138, 268], [181, 134], [234, 154], [223, 17], [133, 175], [172, 125], [25, 265], [123, 138], [0, 1]], ![[0, 1], [112, 135], [235, 115], [148, 252], [73, 94], [206, 144], [11, 4], [68, 131], [138, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [241, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 2
  hpos := by decide
  P := [146, 131, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8628, -7526, 7184]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4508, -1390, 7184]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0], ![15, 1, 0]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![269, 0, 0], ![15, 1, 0]] 
 ![![269, 0, 0], ![15, 1, 0], ![110, 0, 1]] where
  M :=![![![269, 0, 0], ![0, 269, 0], ![0, 0, 269]], ![![15, 1, 0], ![-2, 17, 5], ![-296, 39, 14]]]
  hmulB := by decide  
  f := ![![![-2375, 20196, 5940], ![0, -319572, 0]], ![![-132, 1122, 330], ![1, -17754, 0]], ![![-980, 8258, 2429], ![158, -130680, 0]]]
  g := ![![![1, 0, 0], ![-15, 269, 0], ![-110, 0, 269]], ![![0, 1, 0], ![-3, 17, 5], ![-9, 39, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![269, 0, 0], ![-99, 51, 1]] ![![269, 0, 0], ![15, 1, 0]]
  ![![269, 0, 0]] where
 M := ![![![72361, 0, 0], ![4035, 269, 0]], ![![-26631, 13719, 269], ![-1883, 807, 269]]]
 hmul := by decide  
 g := ![![![![269, 0, 0]], ![![15, 1, 0]]], ![![![-99, 51, 1]], ![![-7, 3, 1]]]]
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

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0], ![-79, -88, 1]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![271, 0, 0], ![-79, -88, 1]] 
 ![![271, 0, 0], ![0, 271, 0], ![192, 183, 1]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]], ![![-79, -88, 1], ![-120, -216, -441], ![26210, -3499, 49]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-192, -183, 271]], ![![-1, -1, 1], ![312, 297, -441], ![62, -46, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 2 2 8 [163, 195, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 270], [0, 1]]
 g := ![![[81, 138], [121, 166], [93, 196], [78, 99], [14], [78], [85], [1]], ![[0, 133], [0, 105], [84, 75], [14, 172], [14], [78], [85], [1]]]
 h' := ![![[76, 270], [60, 42], [17, 39], [23, 14], [257, 53], [10, 234], [248, 112], [108, 76], [0, 1]], ![[0, 1], [0, 229], [0, 232], [3, 257], [220, 218], [179, 37], [88, 159], [193, 195], [76, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [62, 141]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 2
  hpos := by decide
  P := [163, 195, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8773331, -626890, 1520320]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1109501, -1028950, 1520320]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0], ![-101, 1, 0]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![271, 0, 0], ![-101, 1, 0]] 
 ![![271, 0, 0], ![170, 1, 0], ![222, 0, 1]] where
  M :=![![![271, 0, 0], ![0, 271, 0], ![0, 0, 271]], ![![-101, 1, 0], ![-2, -99, 5], ![-296, 39, -102]]]
  hmulB := by decide  
  f := ![![![-11511, -609848, 30800], ![2168, -1669360, 0]], ![![-7222, -382541, 19320], ![1356, -1047144, 0]], ![![-9458, -499580, 25231], ![1700, -1367520, 0]]]
  g := ![![![1, 0, 0], ![-170, 271, 0], ![-222, 0, 271]], ![![-1, 1, 0], ![58, -99, 5], ![58, 39, -102]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![271, 0, 0], ![-79, -88, 1]] ![![271, 0, 0], ![-101, 1, 0]]
  ![![271, 0, 0]] where
 M := ![![![73441, 0, 0], ![-27371, 271, 0]], ![![-21409, -23848, 271], ![7859, 8672, -542]]]
 hmul := by decide  
 g := ![![![![271, 0, 0]], ![![-101, 1, 0]]], ![![![-79, -88, 1]], ![![29, 32, -2]]]]
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


def P277P0 : CertificateIrreducibleZModOfList' 277 3 2 8 [69, 112, 105, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [229, 226, 165], [220, 50, 112], [0, 1]]
 g := ![![[85, 220, 113], [113, 71], [103, 78, 252], [106, 147], [170, 52, 210], [174, 189], [172, 1], []], ![[119, 176, 168, 136], [86, 264], [81, 151, 94, 88], [199, 241], [125, 131, 6, 102], [214, 39], [128, 7], [82, 79]], ![[48, 104, 221, 146], [257, 237], [231, 274, 143, 40], [62, 206], [242, 23, 259, 16], [164, 202], [238, 108], [135, 79]]]
 h' := ![![[229, 226, 165], [120, 68, 152], [95, 240, 25], [240, 47, 23], [181, 240, 198], [92, 73, 140], [43, 57, 110], [0, 0, 1], [0, 1]], ![[220, 50, 112], [52, 93, 261], [13, 233, 131], [64, 192, 41], [172, 100, 194], [144, 89, 209], [101, 9, 224], [247, 233, 50], [229, 226, 165]], ![[0, 1], [223, 116, 141], [134, 81, 121], [144, 38, 213], [78, 214, 162], [128, 115, 205], [151, 211, 220], [28, 44, 226], [220, 50, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [165, 274], []]
 b := ![[], [191, 168, 136], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 3
  hpos := by decide
  P := [69, 112, 105, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30083585, 6343854, -2065035]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-108605, 22902, -7455]
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



lemma PB280I5_primes (p : ℕ) :
  p ∈ Set.range ![263, 269, 271, 277] ↔ Nat.Prime p ∧ 257 < p ∧ p ≤ 279 := by
  rw [← List.mem_ofFn']
  convert primes_range 257 279 (by omega)

def PB280I5 : PrimesBelowBoundCertificateInterval O 257 279 280 where
  m := 4
  g := ![2, 2, 2, 1]
  P := ![263, 269, 271, 277]
  hP := PB280I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I263N0, I263N1]
    · exact ![I269N0, I269N1]
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
    · exact ![72361, 269]
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
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
  β := ![I263N1, I269N1, I271N1]
  Il := ![[I263N1], [I269N1], [I271N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
