
import IdealArithmetic.Examples.NF4_4_54381317_1.RI4_4_54381317_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic

set_option linter.all false

open Classical Polynomial

noncomputable section 
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}
def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0, 0], ![-108, -6, -4, 1]] i)))

def SI127N0: IdealEqSpanCertificate timesTableO I127N0
 ![![127, 0, 0, 0], ![-108, -6, -4, 1]] 
 ![![127, 0, 0, 0], ![0, 127, 0, 0], ![3, 32, 1, 0], ![31, 122, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![127, 0, 0, 0], ![0, 127, 0, 0], ![0, 0, 127, 0], ![0, 0, 0, 127]], ![![-108, -6, -4, 1], ![383, 224, 74, -3], ![-1149, -613, -16, 71], ![27193, 22423, 5067, 55]]]
  hmulB := by decide
  f := ![![![3087409, 3066396, 968504, -20786], ![-2800858, -1813560, 0, 0]], ![![-25705, -25551, -8070, 173], ![23368, 15113, 0, 0]], ![![66517, 66000, 20847, -448], ![-60200, -39032, 0, 0]], ![![728975, 723948, 228656, -4908], ![-661169, -428162, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-3, -32, 127, 0], ![-31, -122, 0, 127]], ![![-1, 0, -4, 1], ![2, -14, 74, -3], ![-26, -69, -16, 71], ![81, -1153, 5067, 55]]]
  hle1 := by decide
  hle2 := by decide

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI127N0)

def MemCI127N0 : IdealMemCertificate B I127N0
  ![![127, 0, 0, 0], ![0, 127, 0, 0], ![3, 32, 1, 0], ![31, 122, 0, 1]] ![32980, 29699, 8258, 658] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI127N0
 g := ![-96, -2479, 8258, 658]
 hmem := by decide

def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [42, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [125, 126], [0, 1]]
 g := ![![[121, 124], [20, 71], [80, 68], [50, 16], [126, 47], [125, 1]],![[0, 3], [5, 56], [71, 59], [18, 111], [32, 80], [123, 126]]]
 h' := ![![[125, 126], [49, 88], [69, 84], [59, 103], [42, 4], [84, 89], [0, 1]],![[0, 1], [0, 39], [28, 43], [107, 24], [34, 123], [33, 38], [125, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [79, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal O 127 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I127N0
  hcard := NI127N0
  P := [42, 2, 1]
  f := ofList [42, 2, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P127P0
  hneq := by decide
  hlen := by decide
  c := ![32980, 29699, 8258, 658]
  a := ![0, -1, -1, -1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI127N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI127N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal.isPrime PI127N0
def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0, 0], ![-104, -111, -4, 1]] i)))

def SI127N1: IdealEqSpanCertificate timesTableO I127N1
 ![![127, 0, 0, 0], ![-104, -111, -4, 1]] 
 ![![127, 0, 0, 0], ![0, 127, 0, 0], ![84, 94, 1, 0], ![105, 11, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![127, 0, 0, 0], ![0, 127, 0, 0], ![0, 0, 127, 0], ![0, 0, 0, 127]], ![![-104, -111, -4, 1], ![383, 228, -31, -3], ![-1149, -613, -12, -34], ![-13022, -12437, -3333, -46]]]
  hmulB := by decide
  f := ![![![493429, 103617, -88032, -3147], ![-491871, -297180, 0, 0]], ![![-6290, -1289, 1130, 40], ![6350, 3810, 0, 0]], ![![321720, 67594, -57389, -2052], ![-320616, -193740, 0, 0]], ![![407473, 85625, -72682, -2599], ![-406036, -245370, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-84, -94, 127, 0], ![-105, -11, 0, 127]], ![![1, 2, -4, 1], ![26, 25, -31, -3], ![27, 7, -12, -34], ![2140, 2373, -3333, -46]]]
  hle1 := by decide
  hle2 := by decide

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 16129 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI127N1)

def MemCI127N1 : IdealMemCertificate B I127N1
  ![![127, 0, 0, 0], ![0, 127, 0, 0], ![84, 94, 1, 0], ![105, 11, 0, 1]] ![1552917, 1297946, 275652, -6048] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI127N1
 g := ![-165093, -193282, 275652, -6048]
 hmem := by decide

def P127P1 : CertificateIrreducibleZModOfList' 127 2 2 6 [74, 113, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 126], [0, 1]]
 g := ![![[41, 115], [23, 21], [106, 38], [108, 94], [42, 25], [14, 1]],![[0, 12], [63, 106], [3, 89], [27, 33], [11, 102], [28, 126]]]
 h' := ![![[14, 126], [76, 49], [30, 23], [9, 61], [67, 27], [107, 122], [0, 1]],![[0, 1], [0, 78], [98, 104], [101, 66], [64, 100], [37, 5], [14, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [104, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N1 : CertifiedPrimeIdeal O 127 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I127N1
  hcard := NI127N1
  P := [74, 113, 1]
  f := ofList [74, 113, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P127P1
  hneq := by decide
  hlen := by decide
  c := ![1552917, 1297946, 275652, -6048]
  a := ![-2, 3, -64, 1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI127N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI127N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := CertifiedPrimeIdeal.isPrime PI127N1
def MulI127N0 : IdealMulEqCertificate timesTableO (I127N0) I127N1
  ![![127, 0, 0, 0], ![-108, -6, -4, 1]] ![![127, 0, 0, 0], ![-104, -111, -4, 1]]
  ![![127, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![16129, 0, 0, 0], ![-13208, -14097, -508, 127]], ![![-13716, -762, -508, 127], ![508, 635, -2667, 0]]]
 hmul := by decide
 f :=  ![![![![285769830560219613707, 60007920199437368998, -50984289700608147724, -1822585622861640670], ![-284872653127722966906, -172113448567232212260, 0, 0]], ![![681529452909448, -595256, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![127, 0, 0, 0]], ![![-104, -111, -4, 1]]], ![![![-108, -6, -4, 1]], ![![4, 5, -21, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC127 : IsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI127N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}
def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate timesTableO I131N0
 ![![131, 0, 0, 0]] 
 ![![131, 0, 0, 0], ![0, 131, 0, 0], ![0, 0, 131, 0], ![0, 0, 0, 131]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![131, 0, 0, 0], ![0, 131, 0, 0], ![0, 0, 131, 0], ![0, 0, 0, 131]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 294499921 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI131N0)

def MemCI131N0 : IdealMemCertificate B I131N0
  ![![131, 0, 0, 0], ![0, 131, 0, 0], ![0, 0, 131, 0], ![0, 0, 0, 131]] ![2929201621975, 2797566331580, 860008316642, 84541031697] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI131N0
 g := ![22360317725, 21355468180, 6564948982, 645351387]
 hmem := by decide

def P131P0 : CertificateIrreducibleZModOfList' 131 4 2 7 [82, 31, 109, 16, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 71, 9, 82], [108, 49, 93, 37], [103, 10, 29, 12], [0, 1]]
 g := ![![[113, 126, 20, 7], [106, 90, 79, 5], [87, 74, 125], [97, 93, 43], [68, 47, 125], [1], []],![[40, 130, 6, 64, 75, 86], [100, 21, 59, 40, 17, 67], [113, 40, 43], [73, 49, 99], [65, 72, 100], [25, 99, 25], [63, 2, 43]],![[84, 21, 82, 89, 104, 29], [104, 77, 80, 66, 19, 104], [74, 69, 16], [115, 75, 5], [127, 122, 62], [31, 35, 38], [47, 43, 59]],![[112, 120, 33, 52, 121, 63], [72, 34, 46, 115, 90, 64], [83, 106, 59], [46, 19, 49], [83, 90, 102], [126, 66, 62], [109, 95, 13]]]
 h' := ![![[35, 71, 9, 82], [85, 119, 95, 20], [82, 90, 119, 108], [81, 49, 58, 115], [100, 39, 111, 82], [49, 100, 22, 115], [0, 0, 1], [0, 1]],![[108, 49, 93, 37], [56, 19, 62, 66], [62, 66, 93, 76], [114, 49, 101, 49], [27, 59, 74, 19], [36, 129, 126, 121], [120, 102, 63, 5], [35, 71, 9, 82]],![[103, 10, 29, 12], [88, 15, 18, 32], [20, 74, 76, 71], [18, 41, 57, 4], [127, 25, 29, 23], [89, 24, 20, 113], [81, 99, 60, 13], [108, 49, 93, 37]],![[0, 1], [14, 109, 87, 13], [86, 32, 105, 7], [39, 123, 46, 94], [55, 8, 48, 7], [124, 9, 94, 44], [99, 61, 7, 113], [103, 10, 29, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [112, 111, 116], []]
 b := ![[], [], [86, 37, 95, 96], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal O 131 where 
  r := 4
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I131N0
  hcard := NI131N0
  P := [82, 31, 109, 16, 1]
  f := ofList [82, 31, 109, 16, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P131P0
  hneq := by decide
  hlen := by decide
  c := ![2929201621975, 2797566331580, 860008316642, 84541031697]
  a := ![-1, 1, 1, -3]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI131N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI131N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal.isPrime PI131N0
def PBC131 : IsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I131N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}
def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0, 0], ![-199, -84, -4, 1]] i)))

def SI137N0: IdealEqSpanCertificate timesTableO I137N0
 ![![137, 0, 0, 0], ![-199, -84, -4, 1]] 
 ![![137, 0, 0, 0], ![0, 137, 0, 0], ![99, 16, 1, 0], ![60, 117, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![137, 0, 0, 0], ![0, 137, 0, 0], ![0, 0, 137, 0], ![0, 0, 0, 137]], ![![-199, -84, -4, 1], ![383, 133, -4, -3], ![-1149, -613, -107, -7], ![-2681, -3473, -1173, -114]]]
  hmulB := by decide
  f := ![![![555980, 98854, -44252, -7889], ![-866525, -649106, 0, 0]], ![![-5280, -909, 432, 76], ![8494, 6302, 0, 0]], ![![401163, 71334, -31927, -5692], ![-625174, -468326, 0, 0]], ![![238961, 42507, -19012, -3390], ![-372263, -278898, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-99, -16, 137, 0], ![-60, -117, 0, 137]], ![![1, -1, -4, 1], ![7, 4, -4, -3], ![72, 14, -107, -7], ![878, 209, -1173, -114]]]
  hle1 := by decide
  hle2 := by decide

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI137N0)

def MemCI137N0 : IdealMemCertificate B I137N0
  ![![137, 0, 0, 0], ![0, 137, 0, 0], ![99, 16, 1, 0], ![60, 117, 0, 1]] ![29998, 25442, 6221, 403] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI137N0
 g := ![-4453, -885, 6221, 403]
 hmem := by decide

def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [124, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 136], [0, 1]]
 g := ![![[121, 44], [39], [2], [63, 128], [25], [109], [1]],![[11, 93], [39], [2], [17, 9], [25], [109], [1]]]
 h' := ![![[66, 136], [88, 27], [35, 83], [134, 31], [127, 111], [79, 5], [13, 66], [0, 1]],![[0, 1], [89, 110], [33, 54], [125, 106], [55, 26], [135, 132], [122, 71], [66, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [114]]
 b := ![[], [37, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal O 137 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I137N0
  hcard := NI137N0
  P := [124, 71, 1]
  f := ofList [124, 71, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P137P0
  hneq := by decide
  hlen := by decide
  c := ![29998, 25442, 6221, 403]
  a := ![0, -1, -1, 1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI137N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI137N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal.isPrime PI137N0
def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0, 0], ![-161, -128, -4, 1]] i)))

def SI137N1: IdealEqSpanCertificate timesTableO I137N1
 ![![137, 0, 0, 0], ![-161, -128, -4, 1]] 
 ![![137, 0, 0, 0], ![0, 137, 0, 0], ![93, 120, 1, 0], ![74, 78, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![137, 0, 0, 0], ![0, 137, 0, 0], ![0, 0, 137, 0], ![0, 0, 0, 137]], ![![-161, -128, -4, 1], ![383, 171, -48, -3], ![-1149, -613, -69, -51], ![-19533, -18081, -4693, -120]]]
  hmulB := by decide
  f := ![![![583080, -13018, -190844, -5839], ![-667327, -489090, 0, 0]], ![![-11354, 319, 3744, 114], ![13152, 9590, 0, 0]], ![![385893, -8538, -126271, -3864], ![-441462, -323610, 0, 0]], ![![308484, -6850, -100952, -3089], ![-352966, -258720, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-93, -120, 137, 0], ![-74, -78, 0, 137]], ![![1, 2, -4, 1], ![37, 45, -48, -3], ![66, 85, -69, -51], ![3108, 4047, -4693, -120]]]
  hle1 := by decide
  hle2 := by decide

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 18769 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI137N1)

def MemCI137N1 : IdealMemCertificate B I137N1
  ![![137, 0, 0, 0], ![0, 137, 0, 0], ![93, 120, 1, 0], ![74, 78, 0, 1]] ![281686, 243633, 62720, 4328] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI137N1
 g := ![-42858, -55623, 62720, 4328]
 hmem := by decide

def P137P1 : CertificateIrreducibleZModOfList' 137 2 2 7 [101, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 136], [0, 1]]
 g := ![![[127, 19], [77], [88], [55, 2], [64], [135], [1]],![[0, 118], [77], [88], [20, 135], [64], [135], [1]]]
 h' := ![![[51, 136], [109, 108], [25, 25], [62, 122], [56, 106], [128, 8], [36, 51], [0, 1]],![[0, 1], [0, 29], [67, 112], [119, 15], [119, 31], [125, 129], [34, 86], [51, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [65, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N1 : CertifiedPrimeIdeal O 137 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I137N1
  hcard := NI137N1
  P := [101, 86, 1]
  f := ofList [101, 86, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P137P1
  hneq := by decide
  hlen := by decide
  c := ![281686, 243633, 62720, 4328]
  a := ![19, 1, -1, 3]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI137N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI137N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := CertifiedPrimeIdeal.isPrime PI137N1
def MulI137N0 : IdealMulEqCertificate timesTableO (I137N0) I137N1
  ![![137, 0, 0, 0], ![-199, -84, -4, 1]] ![![137, 0, 0, 0], ![-161, -128, -4, 1]]
  ![![137, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![18769, 0, 0, 0], ![-22057, -17536, -548, 137]], ![![-27263, -11508, -548, 137], ![-15070, -4521, 411, 137]]]
 hmul := by decide
 f :=  ![![![![653839605465618531, -14665656016569968, -214033442825464272, -6547917987255758], ![-748477274865175264, -548514012068412102, 0, 0]], ![![2913971330, -2158, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![137, 0, 0, 0]], ![![-161, -128, -4, 1]]], ![![![-199, -84, -4, 1]], ![![-110, -33, 3, 1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC137 : IsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI137N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}
def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-397, -179, -3, 2]] i)))

def SI139N0: IdealEqSpanCertificate timesTableO I139N0
 ![![-397, -179, -3, 2]] 
 ![![139, 0, 0, 0], ![0, 139, 0, 0], ![13, 110, 1, 0], ![99, 6, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-397, -179, -3, 2], ![766, 267, -19, -1], ![-383, 434, 187, -20], ![-7660, -7023, -1166, 167]]]
  hmulB := by decide
  f := ![![![-92, -37, 1, 1]], ![![383, 240, 43, 2]], ![![300, 194, 37, 2]], ![![75, 97, 36, 4]]]
  g := ![![![-4, 1, -3, 2], ![8, 17, -19, -1], ![-6, -144, 187, -20], ![-65, 865, -1166, 167]]]
  hle1 := by decide
  hle2 := by decide

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI139N0)

def MemCI139N0 : IdealMemCertificate B I139N0
  ![![139, 0, 0, 0], ![0, 139, 0, 0], ![13, 110, 1, 0], ![99, 6, 0, 1]] ![126001, 112292, 30576, 2433] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI139N0
 g := ![-3686, -23494, 30576, 2433]
 hmem := by decide

def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [63, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 138], [0, 1]]
 g := ![![[32, 64], [22, 44], [136], [45, 127], [20], [35], [1]],![[0, 75], [0, 95], [136], [51, 12], [20], [35], [1]]]
 h' := ![![[69, 138], [4, 8], [17, 34], [84, 85], [33, 108], [96, 115], [76, 69], [0, 1]],![[0, 1], [0, 131], [0, 105], [111, 54], [118, 31], [108, 24], [111, 70], [69, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [90, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal O 139 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I139N0
  hcard := NI139N0
  P := [63, 70, 1]
  f := ofList [63, 70, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P139P0
  hneq := by decide
  hlen := by decide
  c := ![126001, 112292, 30576, 2433]
  a := ![-1, 0, 1, 2]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI139N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI139N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal.isPrime PI139N0
def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-92, -37, 1, 1]] i)))

def SI139N1: IdealEqSpanCertificate timesTableO I139N1
 ![![-92, -37, 1, 1]] 
 ![![139, 0, 0, 0], ![0, 139, 0, 0], ![24, 28, 1, 0], ![23, 74, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-92, -37, 1, 1], ![383, 240, 43, 2], ![766, 1047, 400, 45], ![17235, 15706, 4647, 445]]]
  hmulB := by decide
  f := ![![![-397, -179, -3, 2]], ![![766, 267, -19, -1]], ![![83, 26, -3, 0]], ![![287, 62, -19, 1]]]
  g := ![![![-1, -1, 1, 1], ![-5, -8, 43, 2], ![-71, -97, 400, 45], ![-752, -1060, 4647, 445]]]
  hle1 := by decide
  hle2 := by decide

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 19321 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI139N1)

def MemCI139N1 : IdealMemCertificate B I139N1
  ![![139, 0, 0, 0], ![0, 139, 0, 0], ![24, 28, 1, 0], ![23, 74, 0, 1]] ![123510, 109100, 28780, 2208] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI139N1
 g := ![-4446, -6188, 28780, 2208]
 hmem := by decide

def P139P1 : CertificateIrreducibleZModOfList' 139 2 2 7 [33, 128, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 138], [0, 1]]
 g := ![![[46, 46], [28, 16], [137], [132, 28], [38], [121], [1]],![[135, 93], [65, 123], [137], [23, 111], [38], [121], [1]]]
 h' := ![![[11, 138], [49, 18], [51, 4], [92, 50], [83, 81], [15, 49], [106, 11], [0, 1]],![[0, 1], [108, 121], [95, 135], [86, 89], [1, 58], [137, 90], [88, 128], [11, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [138, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N1 : CertifiedPrimeIdeal O 139 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I139N1
  hcard := NI139N1
  P := [33, 128, 1]
  f := ofList [33, 128, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P139P1
  hneq := by decide
  hlen := by decide
  c := ![123510, 109100, 28780, 2208]
  a := ![-5, 0, 0, 2]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI139N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI139N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := CertifiedPrimeIdeal.isPrime PI139N1
def MulI139N0 : IdealMulEqCertificate timesTableO (I139N0) I139N1
  ![![-397, -179, -3, 2]] ![![-92, -37, 1, 1]]
  ![![139, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![139, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC139 : IsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI139N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}
def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0, 0], ![27, 1, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate timesTableO I149N0
 ![![149, 0, 0, 0], ![27, 1, 0, 0]] 
 ![![149, 0, 0, 0], ![27, 1, 0, 0], ![16, 0, 1, 0], ![15, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![149, 0, 0, 0], ![0, 149, 0, 0], ![0, 0, 149, 0], ![0, 0, 0, 149]], ![![27, 1, 0, 0], ![0, 27, 1, 0], ![0, 0, 27, 1], ![383, 332, 80, 28]]]
  hmulB := by decide
  f := ![![![2485, -43, 104323, 3864], ![-13708, 745, -575736, 0]], ![![405, -12, 22355, 828], ![-2234, 149, -123372, 0]], ![![248, -18, 11177, 414], ![-1368, 150, -61686, 0]], ![![219, -14, 10502, 389], ![-1208, 122, -57960, 0]]]
  g := ![![![1, 0, 0, 0], ![-27, 149, 0, 0], ![-16, 0, 149, 0], ![-15, 0, 0, 149]], ![![0, 1, 0, 0], ![-5, 27, 1, 0], ![-3, 0, 27, 1], ![-69, 332, 80, 28]]]
  hle1 := by decide
  hle2 := by decide

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0
def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0, 0], ![34, 1, 0, 0]] i)))

def SI149N1: IdealEqSpanCertificate timesTableO I149N1
 ![![149, 0, 0, 0], ![34, 1, 0, 0]] 
 ![![149, 0, 0, 0], ![34, 1, 0, 0], ![36, 0, 1, 0], ![117, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![149, 0, 0, 0], ![0, 149, 0, 0], ![0, 0, 149, 0], ![0, 0, 0, 149]], ![![34, 1, 0, 0], ![0, 34, 1, 0], ![0, 0, 34, 1], ![383, 332, 80, 35]]]
  hmulB := by decide
  f := ![![![1599, -55, 56199, 1653], ![-7003, 447, -246297, 0]], ![![306, -25, 13565, 399], ![-1340, 149, -59451, 0]], ![![348, -24, 13565, 399], ![-1524, 150, -59451, 0]], ![![1267, -57, 44129, 1298], ![-5549, 413, -193401, 0]]]
  g := ![![![1, 0, 0, 0], ![-34, 149, 0, 0], ![-36, 0, 149, 0], ![-117, 0, 0, 149]], ![![0, 1, 0, 0], ![-8, 34, 1, 0], ![-9, 0, 34, 1], ![-120, 332, 80, 35]]]
  hle1 := by decide
  hle2 := by decide

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0, 0], ![42, 1, 0, 0]] i)))

def SI149N2: IdealEqSpanCertificate timesTableO I149N2
 ![![149, 0, 0, 0], ![42, 1, 0, 0]] 
 ![![149, 0, 0, 0], ![42, 1, 0, 0], ![24, 0, 1, 0], ![35, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![149, 0, 0, 0], ![0, 149, 0, 0], ![0, 0, 149, 0], ![0, 0, 0, 149]], ![![42, 1, 0, 0], ![0, 42, 1, 0], ![0, 0, 42, 1], ![383, 332, 80, 43]]]
  hmulB := by decide
  f := ![![![6469, -509978, -13070, -22], ![-22946, 1809754, 3278, 0]], ![![1848, -143764, -3676, -6], ![-6555, 510176, 894, 0]], ![![1020, -82170, -2125, -4], ![-3618, 291594, 596, 0]], ![![1435, -119822, -3064, -5], ![-5090, 425204, 746, 0]]]
  g := ![![![1, 0, 0, 0], ![-42, 149, 0, 0], ![-24, 0, 149, 0], ![-35, 0, 0, 149]], ![![0, 1, 0, 0], ![-12, 42, 1, 0], ![-7, 0, 42, 1], ![-114, 332, 80, 43]]]
  hle1 := by decide
  hle2 := by decide

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def I149N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0, 0], ![45, 1, 0, 0]] i)))

def SI149N3: IdealEqSpanCertificate timesTableO I149N3
 ![![149, 0, 0, 0], ![45, 1, 0, 0]] 
 ![![149, 0, 0, 0], ![45, 1, 0, 0], ![61, 0, 1, 0], ![86, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![149, 0, 0, 0], ![0, 149, 0, 0], ![0, 0, 149, 0], ![0, 0, 0, 149]], ![![45, 1, 0, 0], ![0, 45, 1, 0], ![0, 0, 45, 1], ![383, 332, 80, 46]]]
  hmulB := by decide
  f := ![![![1846, -94, 52467, 1166], ![-6109, 447, -173734, 0]], ![![540, -33, 16694, 371], ![-1787, 149, -55279, 0]], ![![734, -29, 21464, 477], ![-2429, 150, -71073, 0]], ![![1054, -53, 30283, 673], ![-3488, 253, -100276, 0]]]
  g := ![![![1, 0, 0, 0], ![-45, 149, 0, 0], ![-61, 0, 149, 0], ![-86, 0, 0, 149]], ![![0, 1, 0, 0], ![-14, 45, 1, 0], ![-19, 0, 45, 1], ![-157, 332, 80, 46]]]
  hle1 := by decide
  hle2 := by decide

lemma NI149N3 : Nat.card (O ⧸ I149N3) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI149N3)

lemma isPrimeI149N3 : Ideal.IsPrime I149N3 := prime_ideal_of_norm_prime hp149.out _ NI149N3
def MulI149N0 : IdealMulEqCertificate timesTableO (I149N0) I149N1
  ![![149, 0, 0, 0], ![27, 1, 0, 0]] ![![149, 0, 0, 0], ![34, 1, 0, 0]]
  ![![149, 0, 0, 0], ![-70, -67, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![22201, 0, 0, 0], ![5066, 149, 0, 0]], ![![4023, 149, 0, 0], ![918, 61, 1, 0]]]
 hmul := by decide
 f :=  ![![![![-434621245153, 10040510608, -16200872957590, -476516008733], ![1903486171431, -100029598939, 71000885299791, 0]], ![![1482804726, 0, 0, 0], ![-4619, 212474, 0, 0]]], ![![![199511283194, -4609060845, 7436952051145, 218742947854], ![-873788322222, 45918225456, -32592699229590, 0]], ![![-680676064, 0, 0, 0], ![2170, -97743, 0, 0]]]]
 g :=  ![![![![304116306, 179334968, 7883867, -1703847], ![-223736910, -159203371, 0, 0]], ![![69375453, 40910152, 1798479, -388684], ![-51039205, -36317707, 0, 0]]], ![![![55088145, 32485053, 1428098, -308638], ![-40528000, -28838354, 0, 0]], ![![12566791, 7410541, 325780, -70407], ![-9245298, -6578647, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI149N1 : IdealMulEqCertificate timesTableO (I149N0*I149N1) I149N2
  ![![149, 0, 0, 0], ![-70, -67, -4, 1]] ![![149, 0, 0, 0], ![42, 1, 0, 0]]
  ![![149, 0, 0, 0], ![-5090, -2701, -155, 39]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI149N0
 hI2 := rfl
 M :=  ![![![22201, 0, 0, 0], ![6258, 149, 0, 0]], ![![-10430, -9983, -596, 149], ![-2557, -2552, -155, 39]]]
 hmul := by decide
 f :=  ![![![![281186373343829632, -21637719714373457358, -553005634708414715, -896727707528782], ![-997541382839038915, 76786138310032751328, 133611977721917288, 0]], ![![450699870021, 0, 0, 0], ![4619, 0, 0, 0]]], ![![![-9605659632744042252, 739170139481966924429, 18891327623132064301, 30633280835553463], ![34077195417332251149, -2623105452614094934080, -4564343448055924123, 0]], ![![-15396441500563, 0, 0, 0], ![-157790, 0, 0, 0]]]]
 g :=  ![![![![149, 0, 0, 0], ![0, 0, 0, 0]], ![![42, 1, 0, 0], ![0, 0, 0, 0]]], ![![![5020, 2634, 151, -38], ![149, 0, 0, 0]], ![![17, 1, 0, 0], ![1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI149N2 : IdealMulEqCertificate timesTableO (I149N0*I149N1*I149N2) I149N3
  ![![149, 0, 0, 0], ![-5090, -2701, -155, 39]] ![![149, 0, 0, 0], ![45, 1, 0, 0]]
  ![![149, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI149N1
 hI2 := rfl
 M :=  ![![![22201, 0, 0, 0], ![6705, 149, 0, 0]], ![![-758410, -402449, -23095, 5811], ![-214113, -113687, -6556, 1639]]]
 hmul := by decide
 f :=  ![![![![37847948314, -3434823635, 2353861963054, 52309995824], ![-125253524457, 14191112654, -7794211871338, 0]], ![![576758, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![149, 0, 0, 0]], ![![45, 1, 0, 0]]], ![![![-5090, -2701, -155, 39]], ![![-1437, -763, -44, 11]]]]
 hle1 := by decide
 hle2 := by decide

def PBC149 : IsPrimesAboveP 149 ![I149N0, I149N1, I149N2, I149N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
    exact isPrimeI149N3
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI149N2, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}
def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0, 0], ![-103, -67, -4, 1]] i)))

def SI151N0: IdealEqSpanCertificate timesTableO I151N0
 ![![151, 0, 0, 0], ![-103, -67, -4, 1]] 
 ![![151, 0, 0, 0], ![0, 151, 0, 0], ![74, 28, 1, 0], ![42, 45, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![151, 0, 0, 0], ![0, 151, 0, 0], ![0, 0, 151, 0], ![0, 0, 0, 151]], ![![-103, -67, -4, 1], ![383, 229, 13, -3], ![-1149, -613, -11, 10], ![3830, 2171, 187, -1]]]
  hmulB := by decide
  f := ![![![780434, 440507, 24059, -5181], ![-728424, -503585, 0, 0]], ![![-6781, -3826, -209, 45], ![6342, 4379, 0, 0]], ![![381239, 215189, 11753, -2531], ![-355753, -245978, 0, 0]], ![![215089, 121408, 6631, -1428], ![-200666, -138765, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-74, -28, 151, 0], ![-42, -45, 0, 151]], ![![1, 0, -4, 1], ![-3, 0, 13, -3], ![-5, -5, -11, 10], ![-66, -20, 187, -1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI151N0)

def MemCI151N0 : IdealMemCertificate B I151N0
  ![![151, 0, 0, 0], ![0, 151, 0, 0], ![74, 28, 1, 0], ![42, 45, 0, 1]] ![83599, 63587, 10480, -1457] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI151N0
 g := ![-4177, -1088, 10480, -1457]
 hmem := by decide

def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [49, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 150], [0, 1]]
 g := ![![[128, 37], [83, 10], [69, 88], [62], [34, 45], [68], [1]],![[0, 114], [28, 141], [38, 63], [62], [13, 106], [68], [1]]]
 h' := ![![[70, 150], [10, 43], [92, 114], [7, 115], [146, 45], [126, 14], [102, 70], [0, 1]],![[0, 1], [0, 108], [69, 37], [54, 36], [125, 106], [49, 137], [19, 81], [70, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118]]
 b := ![[], [49, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal O 151 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I151N0
  hcard := NI151N0
  P := [49, 81, 1]
  f := ofList [49, 81, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P151P0
  hneq := by decide
  hlen := by decide
  c := ![83599, 63587, 10480, -1457]
  a := ![-10, 2, 13, -1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI151N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI151N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal.isPrime PI151N0
def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0, 0], ![-27, 1, 0, 0]] i)))

def SI151N1: IdealEqSpanCertificate timesTableO I151N1
 ![![151, 0, 0, 0], ![-27, 1, 0, 0]] 
 ![![151, 0, 0, 0], ![124, 1, 0, 0], ![26, 0, 1, 0], ![98, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![151, 0, 0, 0], ![0, 151, 0, 0], ![0, 0, 151, 0], ![0, 0, 0, 151]], ![![-27, 1, 0, 0], ![0, -27, 1, 0], ![0, 0, -27, 1], ![383, 332, 80, -26]]]
  hmulB := by decide
  f := ![![![973, 72, 92228, -3416], ![5436, 604, 515816, 0]], ![![1567, -76198, 2928, -4], ![8759, -425820, 604, 0]], ![![194, 20, 15875, -588], ![1084, 152, 88788, 0]], ![![644, 62, 59856, -2217], ![3598, 480, 334768, 0]]]
  g := ![![![1, 0, 0, 0], ![-124, 151, 0, 0], ![-26, 0, 151, 0], ![-98, 0, 0, 151]], ![![-1, 1, 0, 0], ![22, -27, 1, 0], ![4, 0, -27, 1], ![-267, 332, 80, -26]]]
  hle1 := by decide
  hle2 := by decide

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0, 0], ![-2, 1, 0, 0]] i)))

def SI151N2: IdealEqSpanCertificate timesTableO I151N2
 ![![151, 0, 0, 0], ![-2, 1, 0, 0]] 
 ![![151, 0, 0, 0], ![149, 1, 0, 0], ![147, 0, 1, 0], ![143, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![151, 0, 0, 0], ![0, 151, 0, 0], ![0, 0, 151, 0], ![0, 0, 0, 151]], ![![-2, 1, 0, 0], ![0, -2, 1, 0], ![0, 0, -2, 1], ![383, 332, 80, -1]]]
  hmulB := by decide
  f := ![![![311, -11551, 5700, -1], ![23405, -860398, 151, 0]], ![![307, -11397, 5624, -1], ![23104, -848922, 151, 0]], ![![303, -11245, 5549, -1], ![22803, -837596, 151, 0]], ![![295, -10939, 5398, -1], ![22201, -814794, 152, 0]]]
  g := ![![![1, 0, 0, 0], ![-149, 151, 0, 0], ![-147, 0, 151, 0], ![-143, 0, 0, 151]], ![![-1, 1, 0, 0], ![1, -2, 1, 0], ![1, 0, -2, 1], ![-402, 332, 80, -1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulEqCertificate timesTableO (I151N0) I151N1
  ![![151, 0, 0, 0], ![-103, -67, -4, 1]] ![![151, 0, 0, 0], ![-27, 1, 0, 0]]
  ![![151, 0, 0, 0], ![3919, 2038, 121, -30]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![22801, 0, 0, 0], ![-4077, 151, 0, 0]], ![![-15553, -10117, -604, 151], ![3164, 2038, 121, -30]]]
 hmul := by decide
 f :=  ![![![![4540807155223, -228650680111502, 8725631110857, -9770620953], ![25381017371720, -1277819082541758, 1471728701823, 0]], ![![3635058840, 0, 0, 0], ![-16308, 0, 0, 0]]], ![![![117850615855687, -5934324569629240, 226462160800999, -253583483562], ![658730579399420, -33164096312203542, 38196762811872, 0]], ![![94343121900, 0, 0, 0], ![-423252, 0, 0, 0]]]]
 g :=  ![![![![-3768, -2038, -121, 30], ![151, 0, 0, 0]], ![![-27, 1, 0, 0], ![0, 0, 0, 0]]], ![![![-103, -67, -4, 1], ![0, 0, 0, 0]], ![![-5, 0, 0, 0], ![1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI151N1 : IdealMulEqCertificate timesTableO (I151N0*I151N1) I151N2
  ![![151, 0, 0, 0], ![3919, 2038, 121, -30]] ![![151, 0, 0, 0], ![-2, 1, 0, 0]]
  ![![151, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI151N0
 hI2 := rfl
 M :=  ![![![22801, 0, 0, 0], ![-302, 151, 0, 0]], ![![591769, 307738, 18271, -4530], ![-19328, -10117, -604, 151]]]
 hmul := by decide
 f :=  ![![![![7163245155821, -267655695636583, 132060245278372, -11583867756], ![540819117643673, -19937598525563404, 1749073830276, 0]], ![![-3006696, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![151, 0, 0, 0]], ![![-2, 1, 0, 0]]], ![![![3919, 2038, 121, -30]], ![![-128, -67, -4, 1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC151 : IsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI151N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}
def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate timesTableO I157N0
 ![![157, 0, 0, 0]] 
 ![![157, 0, 0, 0], ![0, 157, 0, 0], ![0, 0, 157, 0], ![0, 0, 0, 157]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![157, 0, 0, 0], ![0, 157, 0, 0], ![0, 0, 157, 0], ![0, 0, 0, 157]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 607573201 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI157N0)

def MemCI157N0 : IdealMemCertificate B I157N0
  ![![157, 0, 0, 0], ![0, 157, 0, 0], ![0, 0, 157, 0], ![0, 0, 0, 157]] ![126054359884, 120587422221, 37157336010, 3665465655] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI157N0
 g := ![802894012, 768072753, 236670930, 23346915]
 hmem := by decide

def P157P0 : CertificateIrreducibleZModOfList' 157 4 2 7 [154, 62, 36, 149, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 46, 156, 151], [129, 84, 152, 126], [150, 26, 6, 37], [0, 1]]
 g := ![![[119, 28, 81, 145], [85, 75, 3], [80, 148, 155, 89], [31, 141, 156, 122], [22, 0, 93, 64], [1], []],![[115, 91, 9, 12, 43, 45], [4, 115, 81], [112, 33, 68, 66, 15, 80], [28, 94, 141, 130, 39, 65], [120, 114, 121, 106, 111, 116], [106, 140, 11], [82, 143, 36]],![[100, 154, 95, 8, 74, 14], [99, 113, 68], [45, 81, 38, 109, 27, 130], [114, 77, 114, 61, 12, 1], [50, 152, 144, 99, 1, 145], [58, 23, 153], [27, 148, 19]],![[119, 48, 53, 70, 50, 130], [124, 83, 118], [24, 137, 85, 86, 133, 89], [6, 139, 156, 125, 51, 120], [20, 60, 2, 69, 79, 124], [74, 107, 81], [41, 92, 113]]]
 h' := ![![[43, 46, 156, 151], [79, 124, 94, 107], [83, 51, 141, 72], [93, 31, 150, 51], [66, 58, 57, 114], [3, 95, 121, 8], [0, 0, 1], [0, 1]],![[129, 84, 152, 126], [142, 31, 144, 89], [75, 144, 143, 148], [29, 95, 118, 143], [54, 113, 116, 80], [94, 153, 137, 70], [54, 86, 54, 47], [43, 46, 156, 151]],![[150, 26, 6, 37], [143, 24, 82, 105], [85, 146, 106, 15], [22, 34, 114, 110], [97, 39, 122, 148], [137, 23, 66, 21], [80, 32, 71, 101], [129, 84, 152, 126]],![[0, 1], [88, 135, 151, 13], [40, 130, 81, 79], [98, 154, 89, 10], [110, 104, 19, 129], [133, 43, 147, 58], [15, 39, 31, 9], [150, 26, 6, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [11, 48, 53], []]
 b := ![[], [], [10, 4, 108, 103], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal O 157 where 
  r := 4
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I157N0
  hcard := NI157N0
  P := [154, 62, 36, 149, 1]
  f := ofList [154, 62, 36, 149, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P157P0
  hneq := by decide
  hlen := by decide
  c := ![126054359884, 120587422221, 37157336010, 3665465655]
  a := ![1, 1, -4, -1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI157N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI157N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal.isPrime PI157N0
def PBC157 : IsPrimesAboveP 157 ![I157N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I157N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}
def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate timesTableO I163N0
 ![![163, 0, 0, 0]] 
 ![![163, 0, 0, 0], ![0, 163, 0, 0], ![0, 0, 163, 0], ![0, 0, 0, 163]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![163, 0, 0, 0], ![0, 163, 0, 0], ![0, 0, 163, 0], ![0, 0, 0, 163]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 705911761 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI163N0)

def MemCI163N0 : IdealMemCertificate B I163N0
  ![![163, 0, 0, 0], ![0, 163, 0, 0], ![0, 0, 163, 0], ![0, 0, 0, 163]] ![30955052900, 29552093155, 9080252247, 892157354] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI163N0
 g := ![189908300, 181301185, 55707069, 5473358]
 hmem := by decide

def P163P0 : CertificateIrreducibleZModOfList' 163 4 2 7 [62, 96, 7, 76, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 66, 95, 137], [2, 92, 118, 149], [3, 4, 113, 40], [0, 1]]
 g := ![![[46, 41, 149, 97], [132, 150, 13, 51], [119, 132, 133], [8, 18, 132], [42, 96, 21], [87, 1], []],![[113, 161, 115, 93, 60, 120], [29, 127, 115, 3, 44, 127], [128, 153, 49], [103, 108, 54], [16, 20, 140], [68, 9, 77, 153, 94, 148], [8, 82, 24]],![[112, 80, 139, 42, 32, 110], [0, 103, 72, 3, 64, 80], [110, 131, 22], [72, 7, 156], [116, 68, 14], [51, 126, 71, 65, 143, 102], [15, 56, 33]],![[102, 125, 81, 6, 35, 152], [135, 80, 2, 126, 80, 54], [145, 10, 41], [123, 74, 95], [53, 6, 15], [2, 32, 159, 18, 27, 97], [90, 73, 133]]]
 h' := ![![[82, 66, 95, 137], [129, 71, 118, 74], [53, 101, 46, 122], [111, 160, 35, 123], [66, 55, 1, 135], [148, 62, 110, 64], [0, 0, 1], [0, 1]],![[2, 92, 118, 149], [18, 83, 116, 149], [32, 144, 150, 107], [12, 139, 79, 7], [82, 97, 54, 39], [111, 115, 160, 125], [34, 82, 88, 63], [82, 66, 95, 137]],![[3, 4, 113, 40], [28, 61, 60, 148], [60, 67, 62, 42], [69, 52, 78, 115], [135, 60, 38, 51], [127, 121, 159, 103], [52, 20, 105, 4], [2, 92, 118, 149]],![[0, 1], [57, 111, 32, 118], [110, 14, 68, 55], [61, 138, 134, 81], [134, 114, 70, 101], [117, 28, 60, 34], [134, 61, 132, 96], [3, 4, 113, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [131, 23, 120], []]
 b := ![[], [], [96, 41, 65, 125], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal O 163 where 
  r := 4
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I163N0
  hcard := NI163N0
  P := [62, 96, 7, 76, 1]
  f := ofList [62, 96, 7, 76, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P163P0
  hneq := by decide
  hlen := by decide
  c := ![30955052900, 29552093155, 9080252247, 892157354]
  a := ![-3, 1, -1, 1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI163N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI163N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal.isPrime PI163N0
def PBC163 : IsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I163N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}
def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0, 0], ![-92, -67, -4, 1]] i)))

def SI167N0: IdealEqSpanCertificate timesTableO I167N0
 ![![167, 0, 0, 0], ![-92, -67, -4, 1]] 
 ![![167, 0, 0, 0], ![0, 167, 0, 0], ![107, 39, 1, 0], ![2, 89, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![167, 0, 0, 0], ![0, 167, 0, 0], ![0, 0, 167, 0], ![0, 0, 0, 167]], ![![-92, -67, -4, 1], ![383, 240, 13, -3], ![-1149, -613, 0, 10], ![3830, 2171, 187, 10]]]
  hmulB := by decide
  f := ![![![1219045, 710289, 36348, -7947], ![-957411, -761520, 0, 0]], ![![-21348, -12432, -636, 139], ![16867, 13360, 0, 0]], ![![776141, 452237, 23143, -5060], ![-609380, -484800, 0, 0]], ![![3214, 1875, 96, -21], ![-2492, -2000, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-107, -39, 167, 0], ![-2, -89, 0, 167]], ![![2, 0, -4, 1], ![-6, 0, 13, -3], ![-7, -9, 0, 10], ![-97, -36, 187, 10]]]
  hle1 := by decide
  hle2 := by decide

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI167N0)

def MemCI167N0 : IdealMemCertificate B I167N0
  ![![167, 0, 0, 0], ![0, 167, 0, 0], ![107, 39, 1, 0], ![2, 89, 0, 1]] ![493820, 412628, 96269, 3229] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI167N0
 g := ![-58763, -21732, 96269, 3229]
 hmem := by decide

def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [13, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [130, 166], [0, 1]]
 g := ![![[157, 81], [72, 66], [62, 121], [63], [6], [75, 33], [1]],![[166, 86], [135, 101], [94, 46], [63], [6], [23, 134], [1]]]
 h' := ![![[130, 166], [66, 158], [29, 147], [138, 11], [150, 49], [27, 138], [154, 130], [0, 1]],![[0, 1], [65, 9], [101, 20], [65, 156], [7, 118], [98, 29], [20, 37], [130, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [125, 88]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal O 167 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I167N0
  hcard := NI167N0
  P := [13, 37, 1]
  f := ofList [13, 37, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P167P0
  hneq := by decide
  hlen := by decide
  c := ![493820, 412628, 96269, 3229]
  a := ![3, 0, 7, -4]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI167N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI167N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal.isPrime PI167N0
def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0, 0], ![-34, 1, 0, 0]] i)))

def SI167N1: IdealEqSpanCertificate timesTableO I167N1
 ![![167, 0, 0, 0], ![-34, 1, 0, 0]] 
 ![![167, 0, 0, 0], ![133, 1, 0, 0], ![13, 0, 1, 0], ![108, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![167, 0, 0, 0], ![0, 167, 0, 0], ![0, 0, 167, 0], ![0, 0, 0, 167]], ![![-34, 1, 0, 0], ![0, -34, 1, 0], ![0, 0, -34, 1], ![383, 332, 80, -33]]]
  hmulB := by decide
  f := ![![![8501, -206902, 6350, -8], ![41750, -1015026, 1336, 0]], ![![6733, -164724, 5043, -6], ![33067, -808113, 1002, 0]], ![![721, -16103, 507, -1], ![3541, -78990, 167, 0]], ![![5472, -133774, 4100, -5], ![26874, -656276, 836, 0]]]
  g := ![![![1, 0, 0, 0], ![-133, 167, 0, 0], ![-13, 0, 167, 0], ![-108, 0, 0, 167]], ![![-1, 1, 0, 0], ![27, -34, 1, 0], ![2, 0, -34, 1], ![-247, 332, 80, -33]]]
  hle1 := by decide
  hle2 := by decide

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0, 0], ![-6, 1, 0, 0]] i)))

def SI167N2: IdealEqSpanCertificate timesTableO I167N2
 ![![167, 0, 0, 0], ![-6, 1, 0, 0]] 
 ![![167, 0, 0, 0], ![161, 1, 0, 0], ![131, 0, 1, 0], ![118, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![167, 0, 0, 0], ![0, 167, 0, 0], ![0, 0, 167, 0], ![0, 0, 0, 167]], ![![-6, 1, 0, 0], ![0, -6, 1, 0], ![0, 0, -6, 1], ![383, 332, 80, -5]]]
  hmulB := by decide
  f := ![![![181, -24, 8567, -1428], ![5010, 167, 238476, 0]], ![![175, -23, 8399, -1400], ![4844, 167, 233800, 0]], ![![145, -18, 6719, -1120], ![4014, 168, 187040, 0]], ![![134, -16, 6053, -1009], ![3710, 173, 168504, 0]]]
  g := ![![![1, 0, 0, 0], ![-161, 167, 0, 0], ![-131, 0, 167, 0], ![-118, 0, 0, 167]], ![![-1, 1, 0, 0], ![5, -6, 1, 0], ![4, 0, -6, 1], ![-377, 332, 80, -5]]]
  hle1 := by decide
  hle2 := by decide

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulEqCertificate timesTableO (I167N0) I167N1
  ![![167, 0, 0, 0], ![-92, -67, -4, 1]] ![![167, 0, 0, 0], ![-34, 1, 0, 0]]
  ![![167, 0, 0, 0], ![4847, 2518, 149, -37]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![27889, 0, 0, 0], ![-5678, 167, 0, 0]], ![![-15364, -11189, -668, 167], ![3511, 2518, 149, -37]]]
 hmul := by decide
 f :=  ![![![![3023853443052836028, -73327341479049113391, 2240286598526272648, -2535774071885036], ![14852449441640387450, -359729816330479872683, 423471618112948512, 0]], ![![2651891847875, 0, 0, 0], ![-20875, 0, 0, 0]]], ![![![87764222130504891882, -2128250329258501385059, 65022003999820673260, -73598222635092329], ![431077000432340040637, -10440786268900635743610, 12290826211639167047, 0]], ![![76968421117660, 0, 0, 0], ![-605875, 0, 0, 0]]]]
 g :=  ![![![![-4680, -2518, -149, 37], ![167, 0, 0, 0]], ![![-34, 1, 0, 0], ![0, 0, 0, 0]]], ![![![-92, -67, -4, 1], ![0, 0, 0, 0]], ![![-8, 0, 0, 0], ![1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI167N1 : IdealMulEqCertificate timesTableO (I167N0*I167N1) I167N2
  ![![167, 0, 0, 0], ![4847, 2518, 149, -37]] ![![167, 0, 0, 0], ![-6, 1, 0, 0]]
  ![![167, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI167N0
 hI2 := rfl
 M :=  ![![![27889, 0, 0, 0], ![-1002, 167, 0, 0]], ![![809449, 420506, 24883, -6179], ![-43253, -22545, -1336, 334]]]
 hmul := by decide
 f :=  ![![![![13307622815, -1839096490, 1538482603674, -256423060200], ![368326191362, 9124513254, 42822556275828, 0]], ![![-2561556, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![167, 0, 0, 0]], ![![-6, 1, 0, 0]]], ![![![4847, 2518, 149, -37]], ![![-259, -135, -8, 2]]]]
 hle1 := by decide
 hle2 := by decide

def PBC167 : IsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI167N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}
def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0, 0], ![56, 1, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate timesTableO I173N0
 ![![173, 0, 0, 0], ![56, 1, 0, 0]] 
 ![![173, 0, 0, 0], ![56, 1, 0, 0], ![151, 0, 1, 0], ![21, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![173, 0, 0, 0], ![0, 173, 0, 0], ![0, 0, 173, 0], ![0, 0, 0, 173]], ![![56, 1, 0, 0], ![0, 56, 1, 0], ![0, 0, 56, 1], ![383, 332, 80, 57]]]
  hmulB := by decide
  f := ![![![3473, -65122, -1276, -2], ![-10726, 201372, 346, 0]], ![![1064, -21149, -434, -1], ![-3286, 65394, 173, 0]], ![![2875, -56789, -1127, -2], ![-8879, 175596, 346, 0]], ![![273, -7929, -198, -1], ![-843, 24510, 174, 0]]]
  g := ![![![1, 0, 0, 0], ![-56, 173, 0, 0], ![-151, 0, 173, 0], ![-21, 0, 0, 173]], ![![0, 1, 0, 0], ![-19, 56, 1, 0], ![-49, 0, 56, 1], ![-182, 332, 80, 57]]]
  hle1 := by decide
  hle2 := by decide

lemma NI173N0 : Nat.card (O ⧸ I173N0) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI173N0)

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := prime_ideal_of_norm_prime hp173.out _ NI173N0
def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0, 0], ![65, 1, 0, 0]] i)))

def SI173N1: IdealEqSpanCertificate timesTableO I173N1
 ![![173, 0, 0, 0], ![65, 1, 0, 0]] 
 ![![173, 0, 0, 0], ![65, 1, 0, 0], ![100, 0, 1, 0], ![74, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![173, 0, 0, 0], ![0, 173, 0, 0], ![0, 0, 173, 0], ![0, 0, 0, 173]], ![![65, 1, 0, 0], ![0, 65, 1, 0], ![0, 0, 65, 1], ![383, 332, 80, 66]]]
  hmulB := by decide
  f := ![![![846, -4407, -133, -1], ![-2249, 11764, 173, 0]], ![![195, -1687, -91, -1], ![-518, 4498, 173, 0]], ![![480, -2528, -104, -1], ![-1276, 6748, 173, 0]], ![![363, -1985, -96, -1], ![-965, 5298, 174, 0]]]
  g := ![![![1, 0, 0, 0], ![-65, 173, 0, 0], ![-100, 0, 173, 0], ![-74, 0, 0, 173]], ![![0, 1, 0, 0], ![-25, 65, 1, 0], ![-38, 0, 65, 1], ![-197, 332, 80, 66]]]
  hle1 := by decide
  hle2 := by decide

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0, 0], ![78, 1, 0, 0]] i)))

def SI173N2: IdealEqSpanCertificate timesTableO I173N2
 ![![173, 0, 0, 0], ![78, 1, 0, 0]] 
 ![![173, 0, 0, 0], ![78, 1, 0, 0], ![144, 0, 1, 0], ![13, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![173, 0, 0, 0], ![0, 173, 0, 0], ![0, 0, 173, 0], ![0, 0, 0, 173]], ![![78, 1, 0, 0], ![0, 78, 1, 0], ![0, 0, 78, 1], ![383, 332, 80, 79]]]
  hmulB := by decide
  f := ![![![11311, -1167671, -17546, -33], ![-25085, 2590156, 5709, 0]], ![![5070, -526435, -7920, -15], ![-11244, 1167750, 2595, 0]], ![![9396, -971994, -14569, -27], ![-20838, 2156100, 4671, 0]], ![![689, -87784, -1360, -3], ![-1528, 194720, 520, 0]]]
  g := ![![![1, 0, 0, 0], ![-78, 173, 0, 0], ![-144, 0, 173, 0], ![-13, 0, 0, 173]], ![![0, 1, 0, 0], ![-36, 78, 1, 0], ![-65, 0, 78, 1], ![-220, 332, 80, 79]]]
  hle1 := by decide
  hle2 := by decide

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def I173N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0, 0], ![-27, 1, 0, 0]] i)))

def SI173N3: IdealEqSpanCertificate timesTableO I173N3
 ![![173, 0, 0, 0], ![-27, 1, 0, 0]] 
 ![![173, 0, 0, 0], ![146, 1, 0, 0], ![136, 0, 1, 0], ![39, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![173, 0, 0, 0], ![0, 173, 0, 0], ![0, 0, 173, 0], ![0, 0, 0, 173]], ![![-27, 1, 0, 0], ![0, -27, 1, 0], ![0, 0, -27, 1], ![383, 332, 80, -26]]]
  hmulB := by decide
  f := ![![![4024, -95, 53296, -1974], ![25777, 346, 341502, 0]], ![![3430, -73, 45682, -1692], ![21972, 346, 292716, 0]], ![![3164, -63, 41875, -1551], ![20268, 347, 268323, 0]], ![![924, -3, 12014, -445], ![5919, 200, 76986, 0]]]
  g := ![![![1, 0, 0, 0], ![-146, 173, 0, 0], ![-136, 0, 173, 0], ![-39, 0, 0, 173]], ![![-1, 1, 0, 0], ![22, -27, 1, 0], ![21, 0, -27, 1], ![-335, 332, 80, -26]]]
  hle1 := by decide
  hle2 := by decide

lemma NI173N3 : Nat.card (O ⧸ I173N3) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI173N3)

lemma isPrimeI173N3 : Ideal.IsPrime I173N3 := prime_ideal_of_norm_prime hp173.out _ NI173N3
def MulI173N0 : IdealMulEqCertificate timesTableO (I173N0) I173N1
  ![![173, 0, 0, 0], ![56, 1, 0, 0]] ![![173, 0, 0, 0], ![65, 1, 0, 0]]
  ![![-376, -201, -12, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![29929, 0, 0, 0], ![11245, 173, 0, 0]], ![![9688, 173, 0, 0], ![3640, 121, 1, 0]]]
 hmul := by decide
 f :=  ![![![![25144269871599873, -107534471554983630, -1855640917010354, -3004802839001], ![-66856633125475749, 287236870718598298, 519830891153842, 0]], ![![-76384546989996, 0, 0, 0], ![27824, -1153734, 0, 0]]]]
 g :=  ![![![![-71449, -34773, -2076, 519]], ![![-25696, -12482, -741, 186]]], ![![![-21979, -10673, -633, 159]], ![![-7906, -3832, -226, 57]]]]
 hle1 := by decide
 hle2 := by decide

def MulI173N1 : IdealMulEqCertificate timesTableO (I173N0*I173N1) I173N2
  ![![-376, -201, -12, 3]] ![![173, 0, 0, 0], ![78, 1, 0, 0]]
  ![![173, 0, 0, 0], ![-9912, -5077, -299, 75]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI173N0
 hI2 := rfl
 M :=  ![![![-65048, -34773, -2076, 519], ![-28179, -15058, -897, 225]]]
 hmul := by decide
 f :=  ![![![![-126634868729911, 58467968302154306, 749609994812254, -2010315], ![280869644747105, -129682556229710798, 347784498, 0]]], ![![![7258659351828696, -3351360246633433390, -42967341093675691, 115230442], ![-16099334203414917, 7433351564125479382, -19934866472, 0]]]]
 g :=  ![![![![9536, 4876, 287, -72], ![173, 0, 0, 0]], ![![9, 1, 0, 0], ![3, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI173N2 : IdealMulEqCertificate timesTableO (I173N0*I173N1*I173N2) I173N3
  ![![173, 0, 0, 0], ![-9912, -5077, -299, 75]] ![![173, 0, 0, 0], ![-27, 1, 0, 0]]
  ![![173, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI173N1
 hI2 := rfl
 M :=  ![![![29929, 0, 0, 0], ![-4671, 173, 0, 0]], ![![-1714776, -878321, -51727, 12975], ![296349, 152067, 8996, -2249]]]
 hmul := by decide
 f :=  ![![![![65850748298, -825678309, 1894145573165, -70155753134], ![421932077195, 10336402995, 12136945191007, 0]], ![![1349, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![173, 0, 0, 0]], ![![-27, 1, 0, 0]]], ![![![-9912, -5077, -299, 75]], ![![1713, 879, 52, -13]]]]
 hle1 := by decide
 hle2 := by decide

def PBC173 : IsPrimesAboveP 173 ![I173N0, I173N1, I173N2, I173N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N2
    exact isPrimeI173N3
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI173N2, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl

