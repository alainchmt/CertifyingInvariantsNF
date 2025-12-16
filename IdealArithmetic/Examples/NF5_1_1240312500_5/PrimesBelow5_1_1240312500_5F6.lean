
import IdealArithmetic.Examples.NF5_1_1240312500_5.PrimesBelow5_1_1240312500_5F5

open Classical Polynomial

noncomputable section 
instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}
def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45887, -28512, -18062, -24726, 65580]] i)))

def SI257N0: IdealEqSpanCertificate O ℤ timesTableO I257N0
 ![![-45887, -28512, -18062, -24726, 65580]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![0, 0, 257, 0, 0], ![0, 0, 0, 257, 0], ![14, 86, 204, 153, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-45887, -28512, -18062, -24726, 65580], ![-174150, -103789, -64026, -86698, 229104], ![-613158, -355124, -214835, -288534, 760356], ![-936396, -528218, -313450, -417429, 1096884], ![-693402, -396686, -237848, -318194, 837415]]]
  hmulB := by decide
  f := ![![![-4795, 5844, 1442, 2638, -5988]], ![![21606, -26337, -6506, -11894, 27000]], ![![-97410, 118680, 29317, 53582, -121644]], ![![208596, -254054, -62686, -114637, 260244]], ![![54056, -65810, -16214, -29675, 67363]]]
  g := ![![![-3751, -22056, -52126, -39138, 65580], ![-13158, -77069, -182106, -136730, 229104], ![-43806, -255820, -604387, -453786, 760356], ![-63396, -369106, -871898, -654633, 1096884], ![-48316, -281768, -665644, -499777, 837415]]]
  hle1 := by decide
  hle2 := by decide

lemma NI257N0 : Nat.card (O ⧸ I257N0) = 4362470401 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI257N0)

def MemCI257N0 : IdealMemCertificate O ℤ B I257N0
  ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![0, 0, 257, 0, 0], ![0, 0, 0, 257, 0], ![14, 86, 204, 153, 1]] ![-98608395433, -52272242137, -37386448967, -80239887170, 160715764734] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI257N0
 g := ![-9138634637, -53983766573, -127717519279, -95991252496, 160715764734]
 hmem := by decide

def P257P0 : CertificateIrreducibleZModOfList' 257 4 2 8 [77, 125, 222, 212, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 192, 30, 253], [90, 28, 118, 18], [148, 36, 109, 243], [0, 1]]
 g := ![![[126, 136, 199, 16], [37, 119, 100], [214, 67, 8], [151, 62, 242], [25, 36, 169], [17, 213, 226], [1], []],![[235, 47, 166, 242, 144, 228], [37, 224, 121], [217, 147, 92], [46, 82, 89], [213, 86, 246], [237, 58, 244], [240, 157, 198], [193, 223, 16]],![[164, 224, 170, 171, 247, 62], [37, 92, 187], [103, 40, 255], [199, 17, 165], [40, 104, 34], [135, 199, 118], [83, 103, 67], [246, 67, 67]],![[26, 185, 127, 137, 217, 217], [32, 192, 158], [58, 140, 211], [95, 85, 99], [46, 67, 98], [66, 74, 16], [219, 248, 84], [247, 114, 196]]]
 h' := ![![[64, 192, 30, 253], [171, 105, 224, 4], [128, 242, 52, 247], [71, 40, 244, 120], [167, 64, 234, 146], [251, 210, 213, 13], [180, 132, 35, 45], [0, 0, 1], [0, 1]],![[90, 28, 118, 18], [48, 244, 253, 171], [228, 208, 249, 246], [177, 9, 170, 116], [11, 210, 191, 203], [96, 23, 185, 62], [94, 217, 147, 66], [29, 242, 105, 55], [64, 192, 30, 253]],![[148, 36, 109, 243], [233, 143, 85, 17], [68, 4, 240, 207], [240, 158, 154, 189], [20, 106, 183, 57], [253, 224, 135, 88], [25, 155, 220, 142], [209, 228, 138, 239], [90, 28, 118, 18]],![[0, 1], [70, 22, 209, 65], [161, 60, 230, 71], [1, 50, 203, 89], [67, 134, 163, 108], [36, 57, 238, 94], [122, 10, 112, 4], [58, 44, 13, 220], [148, 36, 109, 243]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [114, 63, 67], []]
 b := ![[], [], [248, 116, 25, 239], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : PrimeIdeal O 257 where 
  r := 5
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I257N0
  hcard := NI257N0
  P := [77, 125, 222, 212, 1]
  f := ofList [77, 125, 222, 212, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P257P0
  hneq := by decide
  hlen := by decide
  c := ![-98608395433, -52272242137, -37386448967, -80239887170, 160715764734]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI257N0
  hpmem := by 
    show  _ ∈ I257N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI257N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := PrimeIdeal_isPrime PI257N0
def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4795, -5844, -1442, -2638, 5988]] i)))

def SI257N1: IdealEqSpanCertificate O ℤ timesTableO I257N1
 ![![4795, -5844, -1442, -2638, 5988]] 
 ![![257, 0, 0, 0, 0], ![203, 1, 0, 0, 0], ![168, 0, 1, 0, 0], ![194, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![4795, -5844, -1442, -2638, 5988], ![-21606, 26337, 6506, 11894, -27000], ![97410, -118680, -29317, -53582, 121644], ![-208596, 254054, 62686, 114637, -260244], ![-57858, 70462, 17380, 31790, -72167]]]
  hmulB := by decide
  f := ![![![45887, 28512, 18062, 24726, -65580]], ![![36923, 22925, 14516, 19868, -52692]], ![![32382, 20020, 12643, 17286, -45828]], ![![38282, 23578, 14854, 20289, -53772]], ![![4305, 2542, 1558, 2104, -5555]]]
  g := ![![![7359, -5844, -1442, -2638, 5988], ![-33173, 26337, 6506, 11894, -27000], ![149474, -118680, -29317, -53582, 121644], ![-319884, 254054, 62686, 114637, -260244], ![-88713, 70462, 17380, 31790, -72167]]]
  hle1 := by decide
  hle2 := by decide

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1
def MulI257N0 : IdealMulEqCertificate O ℤ timesTableO (I257N0) I257N1
  ![![-45887, -28512, -18062, -24726, 65580]] ![![4795, -5844, -1442, -2638, 5988]]
  ![![257, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![-257, 0, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![-1, 0, 0, 0, 0]]]]
 g :=  ![![![![-1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC257 : PrimesBelowPCertificate 257 ![I257N0, I257N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI257N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}
def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0, 0, 0], ![-551, -297, -206, -258, 671]] i)))

def SI263N0: IdealEqSpanCertificate O ℤ timesTableO I263N0
 ![![263, 0, 0, 0, 0], ![-551, -297, -206, -258, 671]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![214, 106, 227, 1, 0], ![65, 192, 76, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![0, 0, 0, 263, 0], ![0, 0, 0, 0, 263]], ![![-551, -297, -206, -258, 671], ![-1857, -814, -455, -674, 1713], ![-4971, -1383, -588, -796, 2439], ![-1383, -7439, -3658, -4343, 11190], ![-3394, -3903, -1967, -2437, 6381]]]
  hmulB := by decide
  f := ![![![1899627, 154572, -402394, -19692, 236854], ![-3214912, 1222950, 0, 0, 0]], ![![-25321, -2056, 5368, 266, -3167], ![42869, -16306, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![1535616, 125008, -325215, -15861, 191306], ![-2598602, 988528, 0, 0, 0]], ![![451373, 36900, -95394, -4500, 55777], ![-763088, 290346, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-214, -106, -227, 263, 0], ![-65, -192, -76, 0, 263]], ![![42, -387, 28, -258, 671], ![118, -982, 85, -674, 1713], ![26, -1465, -20, -796, 2439], ![763, -6447, 501, -4343, 11190], ![393, -3691, 252, -2437, 6381]]]
  hle1 := by decide
  hle2 := by decide

lemma NI263N0 : Nat.card (O ⧸ I263N0) = 18191447 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI263N0)

def MemCI263N0 : IdealMemCertificate O ℤ B I263N0
  ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![214, 106, 227, 1, 0], ![65, 192, 76, 0, 1]] ![39254999, 153777231, 107296503, 152055532, -341411154] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI263N0
 g := ![-39197353, 188543089, -32175139, 152055532, -341411154]
 hmem := by decide

def P263P0 : CertificateIrreducibleZModOfList' 263 3 2 8 [24, 76, 142, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 75, 27], [78, 187, 236], [0, 1]]
 g := ![![[53, 88, 190], [19, 44, 225], [206, 124, 186], [84, 75], [65, 198], [93, 6], [121, 1], []],![[216, 174, 168, 242], [75, 101, 103, 92], [132, 90, 23, 184], [3, 9], [155, 186], [106, 75], [133, 253], [209, 203]],![[109, 247, 169, 171], [246, 200, 19, 155], [181, 118, 63, 130], [115, 248], [8, 35], [228, 225], [64, 102], [0, 203]]]
 h' := ![![[43, 75, 27], [70, 46, 157], [53, 231, 248], [106, 160, 221], [67, 129, 115], [256, 219, 143], [252, 248, 100], [0, 0, 1], [0, 1]],![[78, 187, 236], [58, 9, 93], [157, 212, 13], [84, 62, 148], [141, 82, 3], [210, 238, 42], [85, 47, 148], [252, 159, 187], [43, 75, 27]],![[0, 1], [211, 208, 13], [188, 83, 2], [70, 41, 157], [215, 52, 145], [251, 69, 78], [215, 231, 15], [35, 104, 75], [78, 187, 236]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [144, 10], []]
 b := ![[], [201, 183, 136], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : PrimeIdeal O 263 where 
  r := 5
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I263N0
  hcard := NI263N0
  P := [24, 76, 142, 1]
  f := ofList [24, 76, 142, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P263P0
  hneq := by decide
  hlen := by decide
  c := ![39254999, 153777231, 107296503, 152055532, -341411154]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI263N0
  hpmem := by 
    show  _ ∈ I263N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI263N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := PrimeIdeal_isPrime PI263N0
def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0, 0, 0], ![-69, 110, -4, -5, 13]] i)))

def SI263N1: IdealEqSpanCertificate O ℤ timesTableO I263N1
 ![![263, 0, 0, 0, 0], ![-69, 110, -4, -5, 13]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![239, 72, 1, 0, 0], ![75, 158, 0, 1, 0], ![178, 233, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![0, 0, 0, 263, 0], ![0, 0, 0, 0, 263]], ![![-69, 110, -4, -5, 13], ![-36, -74, 107, -13, 33], ![-96, 90, -69, 217, 45], ![1713, -8248, -4817, -6046, 14802], ![283, -3201, -1890, -2362, 5968]]]
  hmulB := by decide
  f := ![![![-137545743107, -227256574768, 362757235028, -45281200696, 115014071008], ![-57935387372, -893803236096, -752180, 0, 0]], ![![-1012840502076, -1673440834223, 2671222035612, -333435502968, 846924861168], ![-426616671060, -6581665833888, -5538780, 0, 0]], ![![-402249797198, -664607344226, 1060876337301, -132423973145, 336356368997], ![-169430891677, -2613909832320, -2199730, 0, 0]], ![![-647698593426, -1070144087068, 1708212449632, -213227754836, 541597655483], ![-272815924405, -4208891423808, -3541980, 0, 0]], ![![-990399160729, -1636362679311, 2612036205824, -326047627059, 828159685530], ![-417164195309, -6435836940384, -5416060, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-239, -72, 263, 0, 0], ![-75, -158, 0, 263, 0], ![-178, -233, 0, 0, 263]], ![![-4, -7, -4, -5, 13], ![-116, -51, 107, -13, 33], ![-30, -151, -69, 217, 45], ![-3910, -8194, -4817, -6046, 14802], ![-1647, -3363, -1890, -2362, 5968]]]
  hle1 := by decide
  hle2 := by decide

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 69169 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI263N1)

def MemCI263N1 : IdealMemCertificate O ℤ B I263N1
  ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![239, 72, 1, 0, 0], ![75, 158, 0, 1, 0], ![178, 233, 0, 0, 1]] ![254811, -13200623, -8332619, -9606024, 24194412] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI263N1
 g := ![-6062368, -13432693, -8332619, -9606024, 24194412]
 hmem := by decide

def P263P1 : CertificateIrreducibleZModOfList' 263 2 2 8 [21, 217, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 262], [0, 1]]
 g := ![![[98, 48], [185, 145], [139, 52], [150], [248], [17], [12], [1]],![[202, 215], [17, 118], [164, 211], [150], [248], [17], [12], [1]]]
 h' := ![![[46, 262], [60, 92], [237, 150], [138, 29], [208, 237], [122, 145], [189, 198], [242, 46], [0, 1]],![[0, 1], [84, 171], [36, 113], [157, 234], [64, 26], [217, 118], [92, 65], [254, 217], [46, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [190]]
 b := ![[], [182, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N1 : PrimeIdeal O 263 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I263N1
  hcard := NI263N1
  P := [21, 217, 1]
  f := ofList [21, 217, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P263P1
  hneq := by decide
  hlen := by decide
  c := ![254811, -13200623, -8332619, -9606024, 24194412]
  a := ![-526, 2412, 1421, 1723, -4419]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI263N1
  hpmem := by 
    show  _ ∈ I263N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI263N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := PrimeIdeal_isPrime PI263N1
def MulI263N0 : IdealMulEqCertificate O ℤ timesTableO (I263N0) I263N1
  ![![263, 0, 0, 0, 0], ![-551, -297, -206, -258, 671]] ![![263, 0, 0, 0, 0], ![-69, 110, -4, -5, 13]]
  ![![263, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![69169, 0, 0, 0, 0], ![-18147, 28930, -1052, -1315, 3419]], ![![-144913, -78111, -54178, -67854, 176473], ![-183574, -77059, -40765, -63120, 159378]]]
 hmul := by decide
 f :=  ![![![![-963663552230661886907103, -1592189426949636887898733, 2541524860255170786154098, -317246042742797790511599, 805803696119295785254374], ![-405902939309126374357379, -6262102931068410658111008, -5269856704737283360, 0, 0]], ![![675284973379, 13440, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![263, 0, 0, 0, 0]], ![![-69, 110, -4, -5, 13]]], ![![![-551, -297, -206, -258, 671]], ![![-698, -293, -155, -240, 606]]]]
 hle1 := by decide
 hle2 := by decide

def PBC263 : PrimesBelowPCertificate 263 ![I263N0, I263N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI263N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}
def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0, 0, 0], ![13, 0, -4, -5, 13]] i)))

def SI269N0: IdealEqSpanCertificate O ℤ timesTableO I269N0
 ![![269, 0, 0, 0, 0], ![13, 0, -4, -5, 13]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![177, 261, 1, 0, 0], ![170, 57, 0, 1, 0], ![245, 185, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![0, 0, 0, 269, 0], ![0, 0, 0, 0, 269]], ![![13, 0, -4, -5, 13], ![-36, 8, -3, -13, 33], ![-96, -20, 13, -3, 45], ![63, -548, -307, -354, 942], ![-47, -231, -130, -162, 440]]]
  hmulB := by decide
  f := ![![![665880969, -147568020, 55249481, 240074809, -609759535], ![-2571640, 4968123340, 2459467, 0, 0]], ![![1331765572, -295136847, 110499265, 480150931, -1219522403], ![-5143280, 9936273849, 4918934, 0, 0]], ![![1730303895, -383458203, 143566787, 623838786, -1584471312], ![-6682590, 12909759501, 6390957, 0, 0]], ![![702952272, -155783511, 58325362, 253440391, -643706416], ![-2714794, 5244711537, 2596389, 0, 0]], ![![1522369769, -337377255, 126314078, 548870820, -1394062197], ![-5879372, 11358367585, 5622945, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-177, -261, 269, 0, 0], ![-170, -57, 0, 269, 0], ![-245, -185, 0, 0, 269]], ![![-6, -4, -4, -5, 13], ![-20, -17, -3, -13, 33], ![-48, -43, 13, -3, 45], ![-432, -277, -307, -354, 942], ![-213, -143, -130, -162, 440]]]
  hle1 := by decide
  hle2 := by decide

lemma NI269N0 : Nat.card (O ⧸ I269N0) = 72361 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI269N0)

def MemCI269N0 : IdealMemCertificate O ℤ B I269N0
  ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![177, 261, 1, 0, 0], ![170, 57, 0, 1, 0], ![245, 185, 0, 0, 1]] ![3915, -301007, -187639, -238440, 570318] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI269N0
 g := ![-245268, -160762, -187639, -238440, 570318]
 hmem := by decide

def P269P0 : CertificateIrreducibleZModOfList' 269 2 2 8 [47, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [230, 268], [0, 1]]
 g := ![![[18, 166], [164], [138, 268], [51, 228], [57], [93], [176], [1]],![[0, 103], [164], [177, 1], [36, 41], [57], [93], [176], [1]]]
 h' := ![![[230, 268], [186, 191], [239, 83], [24, 187], [49, 94], [245, 47], [124, 30], [222, 230], [0, 1]],![[0, 1], [0, 78], [230, 186], [263, 82], [149, 175], [26, 222], [30, 239], [129, 39], [230, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [205, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : PrimeIdeal O 269 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I269N0
  hcard := NI269N0
  P := [47, 39, 1]
  f := ofList [47, 39, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P269P0
  hneq := by decide
  hlen := by decide
  c := ![3915, -301007, -187639, -238440, 570318]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI269N0
  hpmem := by 
    show  _ ∈ I269N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI269N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := PrimeIdeal_isPrime PI269N0
def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 0, 0, 0, 0], ![-22, -62, -4, -5, 13]] i)))

def SI269N1: IdealEqSpanCertificate O ℤ timesTableO I269N1
 ![![269, 0, 0, 0, 0], ![-22, -62, -4, -5, 13]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![4, 187, 1, 0, 0], ![164, 3, 0, 1, 0], ![104, 116, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![0, 0, 0, 269, 0], ![0, 0, 0, 0, 269]], ![![-22, -62, -4, -5, 13], ![-36, -27, -65, -13, 33], ![-96, -82, -22, -127, 45], ![-867, 3792, 2235, 2773, -6870], ![-233, 1443, 862, 1078, -2757]]]
  hmulB := by decide
  f := ![![![2359880757461, 1641739168556, 4361519940496, 860475938774, -2183411122102], ![-757762115722, 18096611675688, 6978936, 0, 0]], ![![3230190082598, 2247202348539, 5970021329400, 1177814105633, -2988639544841], ![-1037220064499, 24770529349332, 9552728, 0, 0]], ![![2280551419116, 1586550752131, 4214903849841, 831550330280, -2110013956120], ![-732289317076, 17488279146156, 6744336, 0, 0]], ![![1474762135594, 1025973348321, 2725648082640, 537737904374, -1364480827737], ![-473548874091, 11309129750412, 4361352, 0, 0]], ![![2305314677920, 1603778237804, 4260671182240, 840579679876, -2132925442015], ![-740240845644, 17678174791056, 6817568, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-4, -187, 269, 0, 0], ![-164, -3, 0, 269, 0], ![-104, -116, 0, 0, 269]], ![![-2, -3, -4, -5, 13], ![-4, 31, -65, -13, 33], ![60, -3, -22, -127, 45], ![929, 1392, 2235, 2773, -6870], ![395, 583, 862, 1078, -2757]]]
  hle1 := by decide
  hle2 := by decide

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 72361 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI269N1)

def MemCI269N1 : IdealMemCertificate O ℤ B I269N1
  ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![4, 187, 1, 0, 0], ![164, 3, 0, 1, 0], ![104, 116, 0, 0, 1]] ![313372, -13468355, -8490350, -9797277, 24684921] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI269N1
 g := ![-3443136, -4683390, -8490350, -9797277, 24684921]
 hmem := by decide

def P269P1 : CertificateIrreducibleZModOfList' 269 2 2 8 [196, 106, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [163, 268], [0, 1]]
 g := ![![[157, 70], [84], [59, 13], [41, 177], [43], [191], [207], [1]],![[0, 199], [84], [26, 256], [109, 92], [43], [191], [207], [1]]]
 h' := ![![[163, 268], [223, 96], [3, 155], [34, 33], [214, 213], [240, 145], [265, 242], [73, 163], [0, 1]],![[0, 1], [0, 173], [251, 114], [33, 236], [232, 56], [203, 124], [168, 27], [11, 106], [163, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [51, 138]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N1 : PrimeIdeal O 269 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I269N1
  hcard := NI269N1
  P := [196, 106, 1]
  f := ofList [196, 106, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P269P1
  hneq := by decide
  hlen := by decide
  c := ![313372, -13468355, -8490350, -9797277, 24684921]
  a := ![-526, 2412, 1421, 1723, -4419]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI269N1
  hpmem := by 
    show  _ ∈ I269N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI269N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := PrimeIdeal_isPrime PI269N1
def I269N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14, -7, -2, -1, 4]] i)))

def SI269N2: IdealEqSpanCertificate O ℤ timesTableO I269N2
 ![![14, -7, -2, -1, 4]] 
 ![![269, 0, 0, 0, 0], ![90, 1, 0, 0, 0], ![239, 0, 1, 0, 0], ![229, 0, 0, 1, 0], ![136, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![14, -7, -2, -1, 4], ![-3, -26, -30, -33, 78], ![-261, 171, 79, 63, -180], ![204, 147, 249, 289, -660], ![13, 86, 101, 111, -261]]]
  hmulB := by decide
  f := ![![![546, -10, 41, 21, -76]], ![![183, 1, 15, 9, -30]], ![![501, -22, 33, 12, -52]], ![![438, 19, 40, 28, -86]], ![![271, 3, 22, 13, -43]]]
  g := ![![![3, -7, -2, -1, 4], ![24, -26, -30, -33, 78], ![-91, 171, 79, 63, -180], ![-182, 147, 249, 289, -660], ![-81, 86, 101, 111, -261]]]
  hle1 := by decide
  hle2 := by decide

lemma NI269N2 : Nat.card (O ⧸ I269N2) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI269N2)

lemma isPrimeI269N2 : Ideal.IsPrime I269N2 := prime_ideal_of_norm_prime hp269.out _ NI269N2
def MulI269N0 : IdealMulEqCertificate O ℤ timesTableO (I269N0) I269N1
  ![![269, 0, 0, 0, 0], ![13, 0, -4, -5, 13]] ![![269, 0, 0, 0, 0], ![-22, -62, -4, -5, 13]]
  ![![-546, 10, -41, -21, 76]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![72361, 0, 0, 0, 0], ![-5918, -16678, -1076, -1345, 3497]], ![![3497, 0, -1076, -1345, 3497], ![1404, -679, 67, 592, -1502]]]
 hmul := by decide
 f :=  ![![![![-37484962002831197240325440543227832, -26077809399428060792375918940956762, -69279583564291725232880466322539908, -13667986473188090428570963257298309, 34681889932459358518195083572980924], ![12036491385025669599350852915672119, -287451599062593965013511567764800832, -239362229426147413910820312, 0, 0]], ![![1802813901560515268, -3149305954259, 0, 0, 0], ![84630, 0, 0, 0, 0]]]]
 g :=  ![![![![-3766, 1883, 538, 269, -1076]], ![![-71, -1465, -1656, -1814, 4297]]], ![![![-375, 392, 274, 267, -679]], ![![-392, 85, -69, -110, 216]]]]
 hle1 := by decide
 hle2 := by decide

def MulI269N1 : IdealMulEqCertificate O ℤ timesTableO (I269N0*I269N1) I269N2
  ![![-546, 10, -41, -21, 76]] ![![14, -7, -2, -1, 4]]
  ![![269, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI269N0
 hI2 := rfl
 M :=  ![![![-269, 0, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![-1, 0, 0, 0, 0]]]]
 g :=  ![![![![-1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC269 : PrimesBelowPCertificate 269 ![I269N0, I269N1, I269N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
    exact isPrimeI269N1
    exact isPrimeI269N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI269N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}
def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-90315, -47475, -26683, -34654, 90262]] i)))

def SI271N0: IdealEqSpanCertificate O ℤ timesTableO I271N0
 ![![-90315, -47475, -26683, -34654, 90262]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![76, 94, 1, 0, 0], ![222, 92, 0, 1, 0], ![156, 9, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-90315, -47475, -26683, -34654, 90262], ![-249024, -128292, -70853, -91252, 236958], ![-657906, -330103, -178288, -227014, 587106], ![-697434, -334392, -172686, -214865, 550842], ![-636434, -313959, -166783, -210616, 542995]]]
  hmulB := by decide
  f := ![![![77465, -46173, -18147, -13032, 40114]], ![![-75138, -111520, -153685, -173942, 403782]], ![![-9496, -47775, -56332, -62188, 146422]], ![![44268, -74108, -62666, -64413, 158082]], ![![43138, -28925, -13626, -11092, 31437]]]
  g := ![![![-16421, 17847, -26683, -34654, 90262], ![-42700, 47212, -70853, -91252, 236958], ![-104426, 118193, -178288, -227014, 587106], ![-95220, 113314, -172686, -214865, 550842], ![-95614, 110160, -166783, -210616, 542995]]]
  hle1 := by decide
  hle2 := by decide

lemma NI271N0 : Nat.card (O ⧸ I271N0) = 73441 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI271N0)

def MemCI271N0 : IdealMemCertificate O ℤ B I271N0
  ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![76, 94, 1, 0, 0], ![222, 92, 0, 1, 0], ![156, 9, 0, 0, 1]] ![-188, -281652, -176418, -224426, 535332] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI271N0
 g := ![-74840, 118564, -176418, -224426, 535332]
 hmem := by decide

def P271P0 : CertificateIrreducibleZModOfList' 271 2 2 8 [109, 88, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [183, 270], [0, 1]]
 g := ![![[237, 212], [264, 162], [55, 224], [254, 28], [53], [212], [156], [1]],![[9, 59], [100, 109], [126, 47], [229, 243], [53], [212], [156], [1]]]
 h' := ![![[183, 270], [221, 36], [238, 51], [227, 148], [112, 242], [61, 18], [26, 36], [162, 183], [0, 1]],![[0, 1], [34, 235], [86, 220], [211, 123], [225, 29], [103, 253], [110, 235], [47, 88], [183, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [151]]
 b := ![[], [70, 211]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : PrimeIdeal O 271 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I271N0
  hcard := NI271N0
  P := [109, 88, 1]
  f := ofList [109, 88, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P271P0
  hneq := by decide
  hlen := by decide
  c := ![-188, -281652, -176418, -224426, 535332]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI271N0
  hpmem := by 
    show  _ ∈ I271N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI271N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := PrimeIdeal_isPrime PI271N0
def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0, 0, 0], ![-36, -141, -4, -5, 13]] i)))

def SI271N1: IdealEqSpanCertificate O ℤ timesTableO I271N1
 ![![271, 0, 0, 0, 0], ![-36, -141, -4, -5, 13]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![260, 246, 1, 0, 0], ![269, 89, 0, 1, 0], ![139, 245, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![0, 0, 271, 0, 0], ![0, 0, 0, 271, 0], ![0, 0, 0, 0, 271]], ![![-36, -141, -4, -5, 13], ![-36, -41, -144, -13, 33], ![-96, -161, -36, -285, 45], ![-2052, 9322, 5474, 6788, -16824], ![-470, 3576, 2126, 2658, -6800]]]
  hmulB := by decide
  f := ![![![1858060674289, 1631026671318, 8111367837400, 709785307022, -1800240455182], ![-1314621655820, 15301657947744, 11835654, 0, 0]], ![![792081448380, 695298052486, 3457833252596, 302577726229, -767432994461], ![-560416265971, 6523015936668, 5045478, 0, 0]], ![![2501625125420, 2195954824176, 10920849821639, 955629050366, -2423778091198], ![-1769958650876, 20601594184752, 15935094, 0, 0]], ![![2104478119151, 1847334690986, 9187103718604, 803917583850, -2038989737827], ![-1488967797359, 17330975669028, 13405308, 0, 0]], ![![1669115825005, 1465168745981, 7286528694776, 637607751298, -1617175302259], ![-1180938728206, 13745643391956, 10632096, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-260, -246, 271, 0, 0], ![-269, -89, 0, 271, 0], ![-139, -245, 0, 0, 271]], ![![2, -7, -4, -5, 13], ![134, 105, -144, -13, 33], ![294, 85, -36, -285, 45], ![-3368, 8046, 5474, 6788, -16824], ![-1192, 3358, 2126, 2658, -6800]]]
  hle1 := by decide
  hle2 := by decide

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 73441 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI271N1)

def MemCI271N1 : IdealMemCertificate O ℤ B I271N1
  ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![260, 246, 1, 0, 0], ![269, 89, 0, 1, 0], ![139, 245, 0, 0, 1]] ![268736, -13263335, -8369565, -9650822, 24309306] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI271N1
 g := ![5141820, -11259067, -8369565, -9650822, 24309306]
 hmem := by decide

def P271P1 : CertificateIrreducibleZModOfList' 271 2 2 8 [270, 191, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [80, 270], [0, 1]]
 g := ![![[80, 64], [227, 176], [261, 212], [88, 151], [80], [87], [167], [1]],![[51, 207], [215, 95], [148, 59], [244, 120], [80], [87], [167], [1]]]
 h' := ![![[80, 270], [227, 8], [261, 110], [88, 36], [220, 91], [127, 132], [168, 241], [1, 80], [0, 1]],![[0, 1], [54, 263], [118, 161], [258, 235], [183, 180], [118, 139], [207, 30], [168, 191], [80, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [206]]
 b := ![[], [216, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N1 : PrimeIdeal O 271 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I271N1
  hcard := NI271N1
  P := [270, 191, 1]
  f := ofList [270, 191, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P271P1
  hneq := by decide
  hlen := by decide
  c := ![268736, -13263335, -8369565, -9650822, 24309306]
  a := ![-526, 2412, 1421, 1723, -4419]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI271N1
  hpmem := by 
    show  _ ∈ I271N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI271N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := PrimeIdeal_isPrime PI271N1
def I271N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0, 0, 0], ![-69, 1, 0, 0, 0]] i)))

def SI271N2: IdealEqSpanCertificate O ℤ timesTableO I271N2
 ![![271, 0, 0, 0, 0], ![-69, 1, 0, 0, 0]] 
 ![![271, 0, 0, 0, 0], ![202, 1, 0, 0, 0], ![117, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![83, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![0, 0, 271, 0, 0], ![0, 0, 0, 271, 0], ![0, 0, 0, 0, 271]], ![![-69, 1, 0, 0, 0], ![0, -69, 1, 0, 0], ![0, 1, -69, 2, 0], ![15, -70, -41, -120, 126], ![3, -27, -16, -20, -18]]]
  hmulB := by decide
  f := ![![![-236618278400, 33941897949, -2396733533568, 69478530140, -6464052], ![-929323839189, -16602164600, -9413506663450, 13902842, 0]], ![![-176940217052, 25381330801, -1792247643368, 51955184072, -4833738], ![-694936853271, -12414892923, -7039303659376, 10396373, 0]], ![![-102604385922, 14718168124, -1039291530520, 30127858152, -2802996], ![-402981132681, -7199168657, -4081963059636, 6028666, 0]], ![![-5234917596, 750927006, -53025078192, 1537135623, -143010], ![-20560261663, -367304287, -208263421816, 307585, 0]], ![![-72469804762, 10395489103, -734054919876, 21279402220, -1979765], ![-284626858255, -5084795548, -2883103516850, 4258066, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-202, 271, 0, 0, 0], ![-117, 0, 271, 0, 0], ![-6, 0, 0, 271, 0], ![-83, 0, 0, 0, 271]], ![![-1, 1, 0, 0, 0], ![51, -69, 1, 0, 0], ![29, 1, -69, 2, 0], ![34, -70, -41, -120, 126], ![33, -27, -16, -20, -18]]]
  hle1 := by decide
  hle2 := by decide

lemma NI271N2 : Nat.card (O ⧸ I271N2) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI271N2)

lemma isPrimeI271N2 : Ideal.IsPrime I271N2 := prime_ideal_of_norm_prime hp271.out _ NI271N2
def MulI271N0 : IdealMulEqCertificate O ℤ timesTableO (I271N0) I271N1
  ![![-90315, -47475, -26683, -34654, 90262]] ![![271, 0, 0, 0, 0], ![-36, -141, -4, -5, 13]]
  ![![271, 0, 0, 0, 0], ![289, 248, 149, 170, -436]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![-24475365, -12865725, -7231093, -9391234, 24461002], ![36208876, 18709177, 10359264, 13358449, -34704209]]]
 hmul := by decide
 f :=  ![![![![-157140696615288665273641, -137939717701568679772219, -685999292393334119116785, -60027337608789596172804, 152250853697183135932366], ![111180665054436313735185, -1294100909019522534035889, -1295400092, 0, 0]]], ![![![-169121029326449734917059, -148456176822239551660757, -738299555402945893177865, -64603793560738858428629, 163858387086933284906899], ![119657026602337925497521, -1392762552920886378912885, -1394160785, 0, 0]]]]
 g :=  ![![![![-35694, -603, 1478, -2524, 7858], ![-51219, 0, 0, 0, 0]], ![![54521, 1167, -2551, 2769, -8739], ![74165, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI271N1 : IdealMulEqCertificate O ℤ timesTableO (I271N0*I271N1) I271N2
  ![![271, 0, 0, 0, 0], ![289, 248, 149, 170, -436]] ![![271, 0, 0, 0, 0], ![-69, 1, 0, 0, 0]]
  ![![271, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI271N0
 hI2 := rfl
 M :=  ![![![73441, 0, 0, 0, 0], ![-18699, 271, 0, 0, 0]], ![![78319, 67208, 40379, 46070, -118156], ![-18699, -16802, -10027, -11382, 29268]]]
 hmul := by decide
 f :=  ![![![![-1744990257995375298120, 250311514916503254043, -17675204872907086419744, 512383724487872684580, -47670500298046292], ![-6853490173559567298279, -122436081063610939924, -69421842903545917875670, 102529409330535242, 0]], ![![-11750240, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![271, 0, 0, 0, 0]], ![![-69, 1, 0, 0, 0]]], ![![![289, 248, 149, 170, -436]], ![![-69, -62, -37, -42, 108]]]]
 hle1 := by decide
 hle2 := by decide

def PBC271 : PrimesBelowPCertificate 271 ![I271N0, I271N1, I271N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI271N0
    exact isPrimeI271N1
    exact isPrimeI271N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI271N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp277 : Fact (Nat.Prime 277) := {out := by norm_num}
def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 0, 0, 0, 0], ![-1309, -764, -442, -553, 1438]] i)))

def SI277N0: IdealEqSpanCertificate O ℤ timesTableO I277N0
 ![![277, 0, 0, 0, 0], ![-1309, -764, -442, -553, 1438]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![43, 7, 12, 1, 0], ![194, 252, 143, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![0, 0, 0, 277, 0], ![0, 0, 0, 0, 277]], ![![-1309, -764, -442, -553, 1438], ![-3981, -1867, -1099, -1441, 3660], ![-10635, -3030, -1346, -1907, 5094], ![-4671, -7081, -2624, -2937, 7926], ![-7568, -4923, -2165, -2655, 6999]]]
  hmulB := by decide
  f := ![![![2208242, -769136, -359874, -152691, 789794], ![-3330371, 1248716, 0, 0, 0]], ![![-23590, 8602, 4051, 1834, -9038], ![36287, -13573, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![342743, -118862, -55579, -23427, 121778], ![-515957, 193501, 0, 0, 0]], ![![1524652, -531112, -248509, -105462, 545417], ![-2299546, 862204, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-43, -7, -12, 277, 0], ![-194, -252, -143, 0, 277]], ![![-926, -1297, -720, -553, 1438], ![-2354, -3300, -1831, -1441, 3660], ![-3310, -4597, -2552, -1907, 5094], ![-5112, -7162, -3974, -2937, 7926], ![-4517, -6318, -3506, -2655, 6999]]]
  hle1 := by decide
  hle2 := by decide

lemma NI277N0 : Nat.card (O ⧸ I277N0) = 21253933 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI277N0)

def MemCI277N0 : IdealMemCertificate O ℤ B I277N0
  ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![43, 7, 12, 1, 0], ![194, 252, 143, 0, 1]] ![38781779, 174374031, 120090957, 168300878, -380346078] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI277N0
 g := ![240393441, 342395233, 189494475, 168300878, -380346078]
 hmem := by decide

def P277P0 : CertificateIrreducibleZModOfList' 277 3 2 8 [159, 152, 77, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 28, 50], [185, 248, 227], [0, 1]]
 g := ![![[256, 90, 39], [196, 117], [159, 173, 52], [214, 206], [35, 79, 63], [260, 215], [200, 1], []],![[48, 113, 118, 129], [90, 123], [269, 53, 134, 263], [247, 202], [107, 146, 67, 72], [268, 48], [162, 10], [45, 7]],![[0, 54, 133, 176], [140, 255], [269, 107, 232, 142], [79, 40], [71, 253, 183, 97], [8, 36], [20, 230], [145, 7]]]
 h' := ![![[15, 28, 50], [73, 152, 53], [203, 7, 242], [116, 44, 208], [252, 12, 162], [188, 159, 127], [55, 188, 237], [0, 0, 1], [0, 1]],![[185, 248, 227], [149, 109, 246], [206, 128, 257], [13, 77, 46], [176, 73, 57], [276, 243, 112], [28, 42, 34], [272, 89, 248], [15, 28, 50]],![[0, 1], [0, 16, 255], [10, 142, 55], [107, 156, 23], [155, 192, 58], [37, 152, 38], [211, 47, 6], [90, 188, 28], [185, 248, 227]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [189, 97], []]
 b := ![[], [28, 164, 59], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : PrimeIdeal O 277 where 
  r := 5
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I277N0
  hcard := NI277N0
  P := [159, 152, 77, 1]
  f := ofList [159, 152, 77, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P277P0
  hneq := by decide
  hlen := by decide
  c := ![38781779, 174374031, 120090957, 168300878, -380346078]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI277N0
  hpmem := by 
    show  _ ∈ I277N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI277N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := PrimeIdeal_isPrime PI277N0
def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![277, 0, 0, 0, 0], ![-134, -62, -4, -5, 13]] i)))

def SI277N1: IdealEqSpanCertificate O ℤ timesTableO I277N1
 ![![277, 0, 0, 0, 0], ![-134, -62, -4, -5, 13]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![9, 253, 1, 0, 0], ![108, 271, 0, 1, 0], ![34, 156, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![0, 0, 0, 277, 0], ![0, 0, 0, 0, 277]], ![![-134, -62, -4, -5, 13], ![-36, -139, -65, -13, 33], ![-96, -82, -134, -127, 45], ![-867, 3792, 2235, 2661, -6870], ![-233, 1443, 862, 1078, -2869]]]
  hmulB := by decide
  f := ![![![100065550371, 777855279287, 385233734143, 73438269596, -186149442112], ![-238136751251, 1656330061239, 6249120, 0, 0]], ![![152599887282, 1186228701982, 587481147945, 111993304590, -283877755890], ![-363158362263, 2525902068033, 9529908, 0, 0]], ![![142627205889, 1108706489257, 549088181689, 104674337541, -265325825943], ![-339425299818, 2360829753450, 8907111, 0, 0]], ![![188309201798, 1463813532138, 724955358775, 138200428377, -350306901064], ![-448139658119, 3116978725815, 11759964, 0, 0]], ![![98223144872, 763533418792, 378140816030, 72086125207, -182722061194], ![-233752180699, 1625833735362, 6134064, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-9, -253, 277, 0, 0], ![-108, -271, 0, 277, 0], ![-34, -156, 0, 0, 277]], ![![0, 1, -4, -5, 13], ![3, 53, -65, -13, 33], ![48, 221, -134, -127, 45], ![-270, -762, 2235, 2661, -6870], ![-97, -221, 862, 1078, -2869]]]
  hle1 := by decide
  hle2 := by decide

lemma NI277N1 : Nat.card (O ⧸ I277N1) = 76729 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI277N1)

def MemCI277N1 : IdealMemCertificate O ℤ B I277N1
  ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![9, 253, 1, 0, 0], ![108, 271, 0, 1, 0], ![34, 156, 0, 0, 1]] ![361060, -13687847, -8619661, -9954070, 25087050] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI277N1
 g := ![1083097, 3433428, -8619661, -9954070, 25087050]
 hmem := by decide

def P277P1 : CertificateIrreducibleZModOfList' 277 2 2 8 [18, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [262, 276], [0, 1]]
 g := ![![[47, 211], [120], [148, 147], [71], [144, 117], [70], [225], [1]],![[206, 66], [120], [159, 130], [71], [51, 160], [70], [225], [1]]]
 h' := ![![[262, 276], [212, 52], [106, 61], [213, 79], [178, 25], [238, 242], [152, 212], [259, 262], [0, 1]],![[0, 1], [263, 225], [22, 216], [136, 198], [80, 252], [209, 35], [19, 65], [207, 15], [262, 276]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [143]]
 b := ![[], [190, 210]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N1 : PrimeIdeal O 277 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I277N1
  hcard := NI277N1
  P := [18, 15, 1]
  f := ofList [18, 15, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P277P1
  hneq := by decide
  hlen := by decide
  c := ![361060, -13687847, -8619661, -9954070, 25087050]
  a := ![-526, 2412, 1421, 1723, -4419]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI277N1
  hpmem := by 
    show  _ ∈ I277N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI277N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := PrimeIdeal_isPrime PI277N1
def MulI277N0 : IdealMulEqCertificate O ℤ timesTableO (I277N0) I277N1
  ![![277, 0, 0, 0, 0], ![-1309, -764, -442, -553, 1438]] ![![277, 0, 0, 0, 0], ![-134, -62, -4, -5, 13]]
  ![![277, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![76729, 0, 0, 0, 0], ![-37118, -17174, -1108, -1385, 3601]], ![![-362593, -211628, -122434, -153181, 398326], ![389739, 201656, 117725, 151242, -388631]]]
 hmul := by decide
 f :=  ![![![![133474132212890590289776165136683158, 1037569537084378499190266073774013718, 513854559113937004315640164692416580, 97954624874269656595837708841256567, -248301187101588593636423257424940392], ![-317646035411214996628670592966803154, 2209358377283806531994214935111081190, 18602671532319637274014666350, 0, 0]], ![![614234485253497397, 8585248, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![277, 0, 0, 0, 0]], ![![-134, -62, -4, -5, 13]]], ![![![-1309, -764, -442, -553, 1438]], ![![1407, 728, 425, 546, -1403]]]]
 hle1 := by decide
 hle2 := by decide

def PBC277 : PrimesBelowPCertificate 277 ![I277N0, I277N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI277N0
    exact isPrimeI277N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI277N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp281 : Fact (Nat.Prime 281) := {out := by norm_num}
def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![281, 0, 0, 0, 0]] i)))

def SI281N0: IdealEqSpanCertificate O ℤ timesTableO I281N0
 ![![281, 0, 0, 0, 0]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![0, 0, 0, 281, 0], ![0, 0, 0, 0, 281]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![0, 0, 0, 281, 0], ![0, 0, 0, 0, 281]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI281N0 : Nat.card (O ⧸ I281N0) = 1751989905401 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI281N0)

def MemCI281N0 : IdealMemCertificate O ℤ B I281N0
  ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![0, 0, 0, 281, 0], ![0, 0, 0, 0, 281]] ![127049284363608, -6952172270947, -20096213077277, 22509817840110, -19186156124394] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI281N0
 g := ![452132684568, -24740826587, -71516772517, 80106113310, -68278135674]
 hmem := by decide

def P281P0 : CertificateIrreducibleZModOfList' 281 5 2 8 [20, 151, 15, 31, 184, 1] where
 m := 1
 P := ![5]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [179, 78, 52, 83, 57], [156, 154, 219, 116, 157], [150, 114, 220, 26, 161], [174, 215, 71, 56, 187], [0, 1]]
 g := ![![[258, 83, 240, 280, 9], [150, 146, 253, 267], [27, 230, 142, 141], [229, 239, 235, 209, 116], [110, 191, 153, 185, 33], [138, 105, 97, 1], [], []],![[9, 265, 122, 134, 192, 170, 231, 247], [176, 122, 24, 20], [61, 232, 118, 250], [216, 234, 3, 95, 123, 123, 224, 100], [243, 39, 87, 95, 196, 170, 270, 58], [49, 266, 199, 116], [98, 41, 203, 100], [268, 251, 60, 158]],![[35, 253, 217, 198, 13, 26, 212, 8], [46, 278, 247, 70], [48, 13, 110, 274], [146, 240, 224, 64, 249, 46, 234, 277], [130, 128, 151, 55, 40, 109, 79, 125], [98, 82, 54, 35], [65, 119, 116, 57], [49, 139, 99, 202]],![[239, 29, 225, 87, 54, 161, 87, 134], [155, 54, 89, 196], [158, 112, 71, 215], [218, 25, 229, 166, 98, 222, 11, 67], [276, 250, 274, 105, 264, 4, 172, 122], [124, 88, 105, 203], [250, 118, 115, 79], [162, 75, 172, 69]],![[41, 272, 153, 8, 269, 259, 162, 233], [103, 109, 206, 201], [263, 170, 200, 100], [210, 249, 50, 195, 174, 154, 88, 251], [171, 240, 167, 162, 261, 6, 48, 173], [30, 54, 12, 9], [184, 129, 84, 62], [212, 41, 192, 125]]]
 h' := ![![[179, 78, 52, 83, 57], [90, 1, 214, 229, 3], [53, 0, 104, 276, 148], [197, 37, 19, 270, 66], [48, 54, 172, 107, 39], [50, 104, 86, 274, 95], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]],![[156, 154, 219, 116, 157], [64, 168, 222, 10, 81], [178, 243, 196, 121, 150], [214, 50, 27, 6, 237], [174, 247, 244, 234, 187], [46, 256, 64, 161, 139], [203, 160, 166, 275, 242], [267, 139, 125, 45, 10], [179, 78, 52, 83, 57]],![[150, 114, 220, 26, 161], [80, 76, 193, 161, 278], [193, 168, 248, 256, 114], [121, 113, 131, 143, 214], [268, 96, 99, 179, 97], [130, 127, 12, 101, 248], [70, 28, 61, 56, 63], [33, 215, 57, 123, 251], [156, 154, 219, 116, 157]],![[174, 215, 71, 56, 187], [256, 125, 65, 248, 188], [69, 272, 217, 164, 267], [177, 265, 29, 230, 55], [27, 28, 219, 9, 44], [118, 219, 133, 234, 62], [120, 153, 195, 228, 259], [152, 89, 262, 14, 172], [150, 114, 220, 26, 161]],![[0, 1], [109, 192, 149, 195, 12], [157, 160, 78, 26, 164], [42, 97, 75, 194, 271], [206, 137, 109, 33, 195], [41, 137, 267, 73, 18], [109, 221, 140, 3, 278], [184, 119, 117, 99, 129], [174, 215, 71, 56, 187]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [175, 68, 139, 167], [], [], []]
 b := ![[], [4, 179, 109, 57, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : PrimeIdeal O 281 where 
  r := 5
  n := 5
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I281N0
  hcard := NI281N0
  P := [20, 151, 15, 31, 184, 1]
  f := ofList [20, 151, 15, 31, 184, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P281P0
  hneq := by decide
  hlen := by decide
  c := ![127049284363608, -6952172270947, -20096213077277, 22509817840110, -19186156124394]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI281N0
  hpmem := by 
    show  _ ∈ I281N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI281N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := PrimeIdeal_isPrime PI281N0
def PBC281 : PrimesBelowPCertificate 281 ![I281N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI281N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    #unfold I281N
    unfold I281N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp283 : Fact (Nat.Prime 283) := {out := by norm_num}
def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-344821, -181171, -101765, -132134, 344130]] i)))

def SI283N0: IdealEqSpanCertificate O ℤ timesTableO I283N0
 ![![-344821, -181171, -101765, -132134, 344130]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![0, 0, 283, 0, 0], ![50, 194, 243, 1, 0], ![252, 44, 173, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-344821, -181171, -101765, -132134, 344130], ![-949620, -488716, -269757, -347296, 901746], ![-2504202, -1255799, -677516, -862338, 2229750], ![-2648100, -1266296, -653092, -811749, 2080458], ![-2420328, -1192163, -632653, -798412, 2057987]]]
  hmulB := by decide
  f := ![![![3983, -865, 715, 1128, -2202]], ![![10314, -14808, -11881, -12058, 29826]], ![![-91392, 37191, 2354, -5324, 1818]], ![![-70850, 22071, -5576, -12193, 20544]], ![![-50838, 19840, 373, -3978, 3425]]]
  g := ![![![-284307, 36435, -97271, -132134, 344130], ![-744964, 96148, -253989, -347296, 901746], ![-1841994, 240031, -625004, -862338, 2229750], ![-1718502, 228526, -577093, -811749, 2080458], ![-1700044, 223139, -574736, -798412, 2057987]]]
  hle1 := by decide
  hle2 := by decide

lemma NI283N0 : Nat.card (O ⧸ I283N0) = 22665187 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI283N0)

def MemCI283N0 : IdealMemCertificate O ℤ B I283N0
  ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![0, 0, 283, 0, 0], ![50, 194, 243, 1, 0], ![252, 44, 173, 0, 1]] ![38584286, 183499024, 125761946, 175502210, -397600728] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI283N0
 g := ![323176174, -57842748, 92804420, 175502210, -397600728]
 hmem := by decide

def P283P0 : CertificateIrreducibleZModOfList' 283 3 2 8 [8, 23, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [211, 43, 194], [24, 239, 89], [0, 1]]
 g := ![![[9, 31, 66], [202, 263, 266], [259, 218], [237, 165, 100], [132, 66, 74], [186, 6], [235, 1], []],![[119, 225, 3, 72], [243, 66, 91, 259], [72, 116], [247, 222, 224, 213], [59, 116, 180, 107], [167, 74], [142, 238], [131, 280]],![[119, 259, 53, 246], [230, 94, 55, 99], [93, 40], [125, 30, 130, 237], [13, 46, 37, 86], [254, 99], [106, 151], [236, 280]]]
 h' := ![![[211, 43, 194], [82, 127, 241], [59, 24, 242], [85, 137, 255], [76, 36, 10], [223, 5, 192], [101, 247, 17], [0, 0, 1], [0, 1]],![[24, 239, 89], [44, 240, 167], [253, 214, 234], [65, 52, 76], [73, 15, 35], [160, 270, 163], [274, 6, 192], [174, 158, 239], [211, 43, 194]],![[0, 1], [219, 199, 158], [91, 45, 90], [206, 94, 235], [272, 232, 238], [26, 8, 211], [139, 30, 74], [103, 125, 43], [24, 239, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [256, 97], []]
 b := ![[], [166, 268, 141], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : PrimeIdeal O 283 where 
  r := 5
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I283N0
  hcard := NI283N0
  P := [8, 23, 48, 1]
  f := ofList [8, 23, 48, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P283P0
  hneq := by decide
  hlen := by decide
  c := ![38584286, 183499024, 125761946, 175502210, -397600728]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI283N0
  hpmem := by 
    show  _ ∈ I283N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI283N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := PrimeIdeal_isPrime PI283N0
def I283N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3983, 865, -715, -1128, 2202]] i)))

def SI283N1: IdealEqSpanCertificate O ℤ timesTableO I283N1
 ![![-3983, 865, -715, -1128, 2202]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![70, 80, 1, 0, 0], ![30, 90, 0, 1, 0], ![149, 5, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-3983, 865, -715, -1128, 2202], ![-10314, 14808, 11881, 12058, -29826], ![91392, -37191, -2354, 5324, -1818], ![42360, -124682, -119134, -125965, 303966], ![33870, -50209, -40901, -41574, 102679]]]
  hmulB := by decide
  f := ![![![344821, 181171, 101765, 132134, -344130]], ![![949620, 488716, 269757, 347296, -901746]], ![![362584, 187403, 103822, 133906, -347910]], ![![347910, 179102, 98884, 127323, -330606]], ![![206879, 108234, 60581, 78526, -204389]]]
  g := ![![![-877, 525, -715, -1128, 2202], ![11450, -6614, 11881, 12058, -29826], ![1298, -1127, -2354, 5324, -1818], ![-117068, 67926, -119134, -125965, 303966], ![-39417, 22792, -40901, -41574, 102679]]]
  hle1 := by decide
  hle2 := by decide

lemma NI283N1 : Nat.card (O ⧸ I283N1) = 80089 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI283N1)

def MemCI283N1 : IdealMemCertificate O ℤ B I283N1
  ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![70, 80, 1, 0, 0], ![30, 90, 0, 1, 0], ![149, 5, 0, 0, 1]] ![249082, -13174091, -8316988, -9587071, 24145803] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI283N1
 g := ![-9638425, 4926828, -8316988, -9587071, 24145803]
 hmem := by decide

def P283P1 : CertificateIrreducibleZModOfList' 283 2 2 8 [78, 228, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 282], [0, 1]]
 g := ![![[90, 127], [109, 252], [13], [179, 203], [257, 4], [11], [195], [1]],![[0, 156], [102, 31], [13], [24, 80], [194, 279], [11], [195], [1]]]
 h' := ![![[55, 282], [271, 134], [87, 95], [188, 182], [47, 130], [80, 2], [213, 164], [205, 55], [0, 1]],![[0, 1], [0, 149], [218, 188], [10, 101], [122, 153], [190, 281], [177, 119], [117, 228], [55, 282]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [150]]
 b := ![[], [60, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N1 : PrimeIdeal O 283 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I283N1
  hcard := NI283N1
  P := [78, 228, 1]
  f := ofList [78, 228, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P283P1
  hneq := by decide
  hlen := by decide
  c := ![249082, -13174091, -8316988, -9587071, 24145803]
  a := ![-526, 2412, 1421, 1723, -4419]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI283N1
  hpmem := by 
    show  _ ∈ I283N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI283N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI283N1 : Ideal.IsPrime I283N1 := PrimeIdeal_isPrime PI283N1
def MulI283N0 : IdealMulEqCertificate O ℤ timesTableO (I283N0) I283N1
  ![![-344821, -181171, -101765, -132134, 344130]] ![![-3983, 865, -715, -1128, 2202]]
  ![![283, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![-283, 0, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![-1, 0, 0, 0, 0]]]]
 g :=  ![![![![-1, 0, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC283 : PrimesBelowPCertificate 283 ![I283N0, I283N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI283N0
    exact isPrimeI283N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI283N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp293 : Fact (Nat.Prime 293) := {out := by norm_num}
def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![293, 0, 0, 0, 0], ![-2078, -1390, -717, -939, 2458]] i)))

def SI293N0: IdealEqSpanCertificate O ℤ timesTableO I293N0
 ![![293, 0, 0, 0, 0], ![-2078, -1390, -717, -939, 2458]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![0, 0, 0, 293, 0], ![100, 178, 279, 92, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![0, 0, 0, 293, 0], ![0, 0, 0, 0, 293]], ![![-2078, -1390, -717, -939, 2458], ![-6711, -3431, -2219, -2705, 7044], ![-19443, -9768, -5230, -7363, 18414], ![-24246, -1505, -145, -261, 2166], ![-19601, -6041, -3110, -4133, 11105]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![128, 86, 45, 58, -151], ![18, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-100, -178, -279, -92, 293]], ![![-846, -1498, -2343, -775, 2458], ![-2427, -4291, -6715, -2221, 7044], ![-6351, -11220, -17552, -5807, 18414], ![-822, -1321, -2063, -681, 2166], ![-3857, -6767, -10585, -3501, 11105]]]
  hle1 := by decide
  hle2 := by decide

lemma NI293N0 : Nat.card (O ⧸ I293N0) = 7370050801 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI293N0)

def MemCI293N0 : IdealMemCertificate O ℤ B I293N0
  ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![0, 0, 0, 293, 0], ![100, 178, 279, 92, 1]] ![-100023570572, -59612288202, -42381700566, -87167801312, 176467868976] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI293N0
 g := ![-60569319004, -107409191010, -168180604590, -55707207328, 176467868976]
 hmem := by decide

def P293P0 : CertificateIrreducibleZModOfList' 293 4 2 8 [266, 11, 187, 175, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 15, 249, 140], [245, 244, 108, 276], [100, 33, 229, 170], [0, 1]]
 g := ![![[35, 223, 51, 137], [121, 9, 233], [131, 269, 202, 132], [223, 10, 158], [88, 201, 123], [68, 128, 292, 153], [1], []],![[197, 110, 115, 90, 209, 144], [291, 260, 184], [6, 237, 185, 215, 268, 90], [208, 235, 197], [236, 107, 256], [219, 247, 52, 37, 108, 254], [273, 257, 170], [264, 137, 262]],![[123, 285, 162, 244, 284, 287], [76, 67, 152], [65, 145, 90, 204, 123, 77], [29, 153, 197], [133, 275, 229], [30, 62, 147, 166, 101, 132], [176, 140, 145], [39, 251, 289]],![[291, 67, 4, 190, 213, 132], [134, 124, 73], [82, 141, 291, 269, 190, 239], [142, 205, 284], [128, 111, 226], [183, 16, 117, 170, 234, 258], [16, 225, 115], [81, 188, 186]]]
 h' := ![![[66, 15, 249, 140], [192, 138, 0, 161], [21, 85, 10, 164], [65, 273, 168, 99], [256, 46, 101, 47], [78, 214, 198, 228], [27, 282, 106, 118], [0, 0, 1], [0, 1]],![[245, 244, 108, 276], [15, 270, 76, 19], [77, 230, 29, 105], [122, 208, 154, 90], [69, 246, 279, 37], [266, 28, 199, 277], [72, 37, 154, 251], [57, 138, 133, 180], [66, 15, 249, 140]],![[100, 33, 229, 170], [190, 227, 131, 11], [90, 227, 167, 93], [258, 55, 266, 66], [190, 105, 72, 37], [212, 255, 285, 225], [147, 85, 167, 189], [134, 211, 37, 32], [245, 244, 108, 276]],![[0, 1], [46, 244, 86, 102], [108, 44, 87, 224], [106, 50, 291, 38], [9, 189, 134, 172], [216, 89, 197, 149], [236, 182, 159, 28], [174, 237, 122, 81], [100, 33, 229, 170]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [174, 123, 289], []]
 b := ![[], [], [189, 195, 143, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : PrimeIdeal O 293 where 
  r := 5
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I293N0
  hcard := NI293N0
  P := [266, 11, 187, 175, 1]
  f := ofList [266, 11, 187, 175, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P293P0
  hneq := by decide
  hlen := by decide
  c := ![-100023570572, -59612288202, -42381700566, -87167801312, 176467868976]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI293N0
  hpmem := by 
    show  _ ∈ I293N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI293N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := PrimeIdeal_isPrime PI293N0
def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![293, 0, 0, 0, 0], ![77, 1, 0, 0, 0]] i)))

def SI293N1: IdealEqSpanCertificate O ℤ timesTableO I293N1
 ![![293, 0, 0, 0, 0], ![77, 1, 0, 0, 0]] 
 ![![293, 0, 0, 0, 0], ![77, 1, 0, 0, 0], ![224, 0, 1, 0, 0], ![274, 0, 0, 1, 0], ![229, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![0, 0, 0, 293, 0], ![0, 0, 0, 0, 293]], ![![77, 1, 0, 0, 0], ![0, 77, 1, 0, 0], ![0, 1, 77, 2, 0], ![15, -70, -41, 26, 126], ![3, -27, -16, -20, 128]]]
  hmulB := by decide
  f := ![![![-179596313886, -11116550477, -776663336058, -20173753200, -1118880], ![683398453783, -4954390326, 2955421019880, 2601840, 0]], ![![-47568753092, -2944383630, -205710827890, -5343318372, -296352], ![181008237909, -1312243864, 782787182730, 689136, 0]], ![![-137852302628, -8532703444, -596141573955, -15484718316, -858816], ![524554476804, -3802829126, 2268485271150, 1997088, 0]], ![![-167946823180, -10395476899, -726285173801, -18865185427, -1046304], ![639069905142, -4633024595, 2763718035120, 2433072, 0]], ![![-140367084836, -8688362009, -607016737056, -15767199600, -874483], ![534123705901, -3872202552, 2309868305640, 2033520, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-77, 293, 0, 0, 0], ![-224, 0, 293, 0, 0], ![-274, 0, 0, 293, 0], ![-229, 0, 0, 0, 293]], ![![0, 1, 0, 0, 0], ![-21, 77, 1, 0, 0], ![-61, 1, 77, 2, 0], ![-73, -70, -41, 26, 126], ![-62, -27, -16, -20, 128]]]
  hle1 := by decide
  hle2 := by decide

lemma NI293N1 : Nat.card (O ⧸ I293N1) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI293N1)

lemma isPrimeI293N1 : Ideal.IsPrime I293N1 := prime_ideal_of_norm_prime hp293.out _ NI293N1
def MulI293N0 : IdealMulEqCertificate O ℤ timesTableO (I293N0) I293N1
  ![![293, 0, 0, 0, 0], ![-2078, -1390, -717, -939, 2458]] ![![293, 0, 0, 0, 0], ![77, 1, 0, 0, 0]]
  ![![293, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![85849, 0, 0, 0, 0], ![22561, 293, 0, 0, 0]], ![![-608854, -407270, -210081, -275127, 720194], ![-166717, -110461, -57428, -75008, 196310]]]
 hmul := by decide
 f :=  ![![![![-15646008264722555721044, -972976136969522923364, -68066107415779730604321, -1767989420553347770690, -240096810335348], ![59536109262194094961157, -434603959748204527805, 259010442852913540131220, 558320015795088, 0]], ![![17672122, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![293, 0, 0, 0, 0]], ![![77, 1, 0, 0, 0]]], ![![![-2078, -1390, -717, -939, 2458]], ![![-569, -377, -196, -256, 670]]]]
 hle1 := by decide
 hle2 := by decide

def PBC293 : PrimesBelowPCertificate 293 ![I293N0, I293N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI293N0
    exact isPrimeI293N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI293N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp307 : Fact (Nat.Prime 307) := {out := by norm_num}
def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![307, 0, 0, 0, 0], ![781, 548, 334, 417, -1084]] i)))

def SI307N0: IdealEqSpanCertificate O ℤ timesTableO I307N0
 ![![307, 0, 0, 0, 0], ![781, 548, 334, 417, -1084]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![0, 0, 307, 0, 0], ![88, 4, 84, 1, 0], ![145, 231, 275, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![0, 0, 307, 0, 0], ![0, 0, 0, 307, 0], ![0, 0, 0, 0, 307]], ![![781, 548, 334, 417, -1084], ![3003, 1193, 795, 1081, -2742], ![7989, 2162, 744, 1299, -3636], ![2787, 7391, 3142, 3439, -9510], ![5486, 4467, 2063, 2533, -6837]]]
  hmulB := by decide
  f := ![![![70843873, -23539916, -8907996, -4034776, 15943992], ![66743028, -24600524, 0, 0, 0]], ![![-264506, 87722, 33169, 14968, -59266], ![-248977, 91793, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![20303437, -6746564, -2553066, -1156436, 4569708], ![19128369, -7050420, 0, 0, 0]], ![![33261204, -11052358, -4182500, -1894537, 7486277], ![31336330, -11550071, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-88, -4, -84, 307, 0], ![-145, -231, -275, 0, 307]], ![![395, 812, 858, 417, -1084], ![995, 2053, 2163, 1081, -2742], ![1371, 2726, 2904, 1299, -3636], ![3515, 7135, 7588, 3439, -9510], ![2521, 5126, 5438, 2533, -6837]]]
  hle1 := by decide
  hle2 := by decide

lemma NI307N0 : Nat.card (O ⧸ I307N0) = 28934443 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI307N0)

def MemCI307N0 : IdealMemCertificate O ℤ B I307N0
  ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![0, 0, 307, 0, 0], ![88, 4, 84, 1, 0], ![145, 231, 275, 0, 1]] ![39480098, 143391330, 100841982, 143859256, -321772416] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI307N0
 g := ![110869270, 240708086, 249198954, 143859256, -321772416]
 hmem := by decide

def P307P0 : CertificateIrreducibleZModOfList' 307 3 2 8 [69, 217, 175, 1] where
 m := 1
 P := ![3]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [214, 116, 130], [225, 190, 177], [0, 1]]
 g := ![![[295, 235, 104], [145], [150, 227], [148, 170], [46, 23, 134], [247, 280, 225], [132, 1], []],![[171, 74, 128, 61], [108, 92, 234, 3], [305, 177], [252, 119], [158, 52, 58, 125], [10, 56, 96, 82], [63, 181], [212, 15]],![[68, 221, 16, 54], [69, 160, 302, 304], [212, 145], [304, 232], [140, 267, 6, 229], [78, 244, 49, 216], [6, 255], [165, 15]]]
 h' := ![![[214, 116, 130], [126, 195, 248], [188, 51], [297, 227, 29], [203, 194, 28], [149, 113, 21], [102, 145, 15], [0, 0, 1], [0, 1]],![[225, 190, 177], [122, 85, 18], [50, 83, 183], [126, 69, 22], [177, 79, 147], [82, 50, 260], [84, 81, 210], [161, 153, 190], [214, 116, 130]],![[0, 1], [27, 27, 41], [304, 173, 124], [14, 11, 256], [226, 34, 132], [145, 144, 26], [266, 81, 82], [251, 154, 116], [225, 190, 177]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [210, 258], []]
 b := ![[], [169, 283, 220], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : PrimeIdeal O 307 where 
  r := 5
  n := 3
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I307N0
  hcard := NI307N0
  P := [69, 217, 175, 1]
  f := ofList [69, 217, 175, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P307P0
  hneq := by decide
  hlen := by decide
  c := ![39480098, 143391330, 100841982, 143859256, -321772416]
  a := ![-85, 395, 229, 286, -714]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI307N0
  hpmem := by 
    show  _ ∈ I307N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI307N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := PrimeIdeal_isPrime PI307N0
def I307N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![307, 0, 0, 0, 0], ![102, 6, -4, -5, 13]] i)))

def SI307N1: IdealEqSpanCertificate O ℤ timesTableO I307N1
 ![![307, 0, 0, 0, 0], ![102, 6, -4, -5, 13]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![280, 139, 1, 0, 0], ![188, 304, 0, 1, 0], ![1, 231, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![0, 0, 307, 0, 0], ![0, 0, 0, 307, 0], ![0, 0, 0, 0, 307]], ![![102, 6, -4, -5, 13], ![-36, 97, 3, -13, 33], ![-96, -14, 102, 9, 45], ![153, -968, -553, -571, 1698], ![-29, -393, -226, -282, 835]]]
  hmulB := by decide
  f := ![![![6406335421075, -18598152035978, -555281743760, 2512506197381, -6379366576093], ![1461186095503, 58771811022564, 7908320, 0, 0]], ![![2287976001492, -6642194442383, -198314827476, 897323275366, -2278344275046], ![521851963710, 20989923933724, 2824400, 0, 0]], ![![6878742613690, -19969591433663, -596228567871, 2697779980462, -6849785069168], ![1568934874799, 63105681234708, 8491485, 0, 0]], ![![6188715842390, -17966383365630, -536419138044, 2427157787684, -6162663113745], ![1411550432991, 56775365954704, 7639680, 0, 0]], ![![1742439061069, -5058452990969, -151029338404, 683368673641, -1735103889622], ![397423419431, 15985160389944, 2150960, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-280, -139, 307, 0, 0], ![-188, -304, 0, 307, 0], ![-1, -231, 0, 0, 307]], ![![7, -3, -4, -5, 13], ![5, -13, 3, -13, 33], ![-99, -89, 102, 9, 45], ![849, -465, -553, -571, 1698], ![376, -248, -226, -282, 835]]]
  hle1 := by decide
  hle2 := by decide

lemma NI307N1 : Nat.card (O ⧸ I307N1) = 94249 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI307N1)

def MemCI307N1 : IdealMemCertificate O ℤ B I307N1
  ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![280, 139, 1, 0, 0], ![188, 304, 0, 1, 0], ![1, 231, 0, 0, 1]] ![321246, -13504535, -8511665, -9823122, 24751206] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI307N1
 g := ![13698968, -5086914, -8511665, -9823122, 24751206]
 hmem := by decide

def P307P1 : CertificateIrreducibleZModOfList' 307 2 2 8 [180, 91, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [216, 306], [0, 1]]
 g := ![![[183, 169], [142, 181], [176], [277], [265, 272], [43, 11], [299], [1]],![[154, 138], [249, 126], [176], [277], [73, 35], [270, 296], [299], [1]]]
 h' := ![![[216, 306], [228, 294], [214, 117], [205, 100], [192, 225], [242, 235], [70, 25], [127, 216], [0, 1]],![[0, 1], [183, 13], [5, 190], [8, 207], [286, 82], [40, 72], [251, 282], [119, 91], [216, 306]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [167]]
 b := ![[], [192, 237]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N1 : PrimeIdeal O 307 where 
  r := 5
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I307N1
  hcard := NI307N1
  P := [180, 91, 1]
  f := ofList [180, 91, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P307P1
  hneq := by decide
  hlen := by decide
  c := ![321246, -13504535, -8511665, -9823122, 24751206]
  a := ![-526, 2412, 1421, 1723, -4419]
  z := ![1, 0, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI307N1
  hpmem := by 
    show  _ ∈ I307N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI307N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI307N1 : Ideal.IsPrime I307N1 := PrimeIdeal_isPrime PI307N1
def MulI307N0 : IdealMulEqCertificate O ℤ timesTableO (I307N0) I307N1
  ![![307, 0, 0, 0, 0], ![781, 548, 334, 417, -1084]] ![![307, 0, 0, 0, 0], ![102, 6, -4, -5, 13]]
  ![![307, 0, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![94249, 0, 0, 0, 0], ![31314, 1842, -1228, -1535, 3991]], ![![239767, 168236, 102538, 128019, -332788], ![123107, 75522, 46971, 59558, -153807]]]
 hmul := by decide
 f :=  ![![![![324535938604421202718832700647, -942156558556101250570805745492, -28129669362152112715333482316, 127280084081011513073796388710, -323169786848127370935468593594], ![74021620242124593606603782746, 2977298286301294868624870520070, 1139660073766925621050, 0, 0]], ![![-45365465818906, -2071938, 0, 0, 0], ![0, 0, 0, 0, 0]]]]
 g :=  ![![![![307, 0, 0, 0, 0]], ![![102, 6, -4, -5, 13]]], ![![![781, 548, 334, 417, -1084]], ![![401, 246, 153, 194, -501]]]]
 hle1 := by decide
 hle2 := by decide

def PBC307 : PrimesBelowPCertificate 307 ![I307N0, I307N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI307N0
    exact isPrimeI307N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI307N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl

