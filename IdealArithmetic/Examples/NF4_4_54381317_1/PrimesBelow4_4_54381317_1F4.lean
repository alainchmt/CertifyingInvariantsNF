
import IdealArithmetic.Examples.NF4_4_54381317_1.RI4_4_54381317_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic

set_option linter.all false

open Classical Polynomial

noncomputable section 
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}
def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-321, -146, -7, 2]] i)))

def SI179N0: IdealEqSpanCertificate timesTableO I179N0
 ![![-321, -146, -7, 2]] 
 ![![179, 0, 0, 0], ![0, 179, 0, 0], ![36, 83, 1, 0], ![55, 128, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-321, -146, -7, 2], ![766, 343, 14, -5], ![-1915, -894, -57, 9], ![3447, 1073, -174, -48]]]
  hmulB := by decide
  f := ![![![-411, -213, -11, 3]], ![![1149, 585, 27, -8]], ![![433, 220, 10, -3]], ![![736, 371, 16, -5]]]
  g := ![![![-1, 1, -7, 2], ![3, -1, 14, -5], ![-2, 15, -57, 9], ![69, 121, -174, -48]]]
  hle1 := by decide
  hle2 := by decide

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI179N0)

def MemCI179N0 : IdealMemCertificate B I179N0
  ![![179, 0, 0, 0], ![0, 179, 0, 0], ![36, 83, 1, 0], ![55, 128, 0, 1]] ![33023, 29637, 8196, 596] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI179N0
 g := ![-1647, -4061, 8196, 596]
 hmem := by decide

def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [85, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 178], [0, 1]]
 g := ![![[125, 139], [28, 59], [93], [4], [31, 147], [52, 158], [1]],![[0, 40], [11, 120], [93], [4], [110, 32], [143, 21], [1]]]
 h' := ![![[115, 178], [126, 153], [115, 43], [12, 123], [50, 2], [55, 133], [94, 115], [0, 1]],![[0, 1], [0, 26], [48, 136], [16, 56], [101, 177], [135, 46], [73, 64], [115, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [81, 120]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal O 179 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I179N0
  hcard := NI179N0
  P := [85, 64, 1]
  f := ofList [85, 64, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P179P0
  hneq := by decide
  hlen := by decide
  c := ![33023, 29637, 8196, 596]
  a := ![0, -1, -1, -1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI179N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI179N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal.isPrime PI179N0
def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-411, -213, -11, 3]] i)))

def SI179N1: IdealEqSpanCertificate timesTableO I179N1
 ![![-411, -213, -11, 3]] 
 ![![179, 0, 0, 0], ![0, 179, 0, 0], ![54, 95, 1, 0], ![61, 158, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-411, -213, -11, 3], ![1149, 585, 27, -8], ![-3064, -1507, -55, 19], ![7277, 3244, 13, -36]]]
  hmulB := by decide
  f := ![![![-321, -146, -7, 2]], ![![766, 343, 14, -5]], ![![299, 133, 5, -2]], ![![586, 259, 9, -4]]]
  g := ![![![0, 2, -11, 3], ![1, -4, 27, -8], ![-7, 4, -55, 19], ![49, 43, 13, -36]]]
  hle1 := by decide
  hle2 := by decide

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 32041 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI179N1)

def MemCI179N1 : IdealMemCertificate B I179N1
  ![![179, 0, 0, 0], ![0, 179, 0, 0], ![54, 95, 1, 0], ![61, 158, 0, 1]] ![1552933, 1297952, 275524, -6046] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI179N1
 g := ![-72383, -133640, 275524, -6046]
 hmem := by decide

def P179P1 : CertificateIrreducibleZModOfList' 179 2 2 7 [94, 115, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 178], [0, 1]]
 g := ![![[125, 173], [132, 149], [75], [89], [170, 77], [49, 158], [1]],![[99, 6], [2, 30], [75], [89], [86, 102], [137, 21], [1]]]
 h' := ![![[64, 178], [122, 129], [73, 68], [121, 84], [130, 39], [48, 163], [85, 64], [0, 1]],![[0, 1], [144, 50], [129, 111], [127, 95], [120, 140], [98, 16], [64, 115], [64, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [159, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N1 : CertifiedPrimeIdeal O 179 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I179N1
  hcard := NI179N1
  P := [94, 115, 1]
  f := ofList [94, 115, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P179P1
  hneq := by decide
  hlen := by decide
  c := ![1552933, 1297952, 275524, -6046]
  a := ![-2, 3, -64, 1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI179N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI179N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := CertifiedPrimeIdeal.isPrime PI179N1
def MulI179N0 : IdealMulEqCertificate timesTableO (I179N0) I179N1
  ![![-321, -146, -7, 2]] ![![-411, -213, -11, 3]]
  ![![179, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![179, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC179 : IsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI179N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}
def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0, 0], ![37, 1, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate timesTableO I181N0
 ![![181, 0, 0, 0], ![37, 1, 0, 0]] 
 ![![181, 0, 0, 0], ![37, 1, 0, 0], ![79, 0, 1, 0], ![154, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![181, 0, 0, 0], ![0, 181, 0, 0], ![0, 0, 181, 0], ![0, 0, 0, 181]], ![![37, 1, 0, 0], ![0, 37, 1, 0], ![0, 0, 37, 1], ![383, 332, 80, 38]]]
  hmulB := by decide
  f := ![![![3516, -238, 278786, 7535], ![-17195, 1629, -1363835, 0]], ![![666, -56, 60826, 1644], ![-3257, 362, -297564, 0]], ![![1488, -108, 121652, 3288], ![-7277, 725, -595128, 0]], ![![3014, -207, 237199, 6411], ![-14740, 1411, -1160390, 0]]]
  g := ![![![1, 0, 0, 0], ![-37, 181, 0, 0], ![-79, 0, 181, 0], ![-154, 0, 0, 181]], ![![0, 1, 0, 0], ![-8, 37, 1, 0], ![-17, 0, 37, 1], ![-133, 332, 80, 38]]]
  hle1 := by decide
  hle2 := by decide

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0
def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0, 0], ![64, 1, 0, 0]] i)))

def SI181N1: IdealEqSpanCertificate timesTableO I181N1
 ![![181, 0, 0, 0], ![64, 1, 0, 0]] 
 ![![181, 0, 0, 0], ![64, 1, 0, 0], ![67, 0, 1, 0], ![56, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![181, 0, 0, 0], ![0, 181, 0, 0], ![0, 0, 181, 0], ![0, 0, 0, 181]], ![![64, 1, 0, 0], ![0, 64, 1, 0], ![0, 0, 64, 1], ![383, 332, 80, 65]]]
  hmulB := by decide
  f := ![![![9217, -630576, -11007, -18], ![-26064, 1783755, 3258, 0]], ![![3136, -222991, -3933, -7], ![-8868, 630785, 1267, 0]], ![![3415, -233419, -4096, -7], ![-9657, 660289, 1267, 0]], ![![2840, -195133, -3434, -6], ![-8031, 551986, 1087, 0]]]
  g := ![![![1, 0, 0, 0], ![-64, 181, 0, 0], ![-67, 0, 181, 0], ![-56, 0, 0, 181]], ![![0, 1, 0, 0], ![-23, 64, 1, 0], ![-24, 0, 64, 1], ![-165, 332, 80, 65]]]
  hle1 := by decide
  hle2 := by decide

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0, 0], ![-89, 1, 0, 0]] i)))

def SI181N2: IdealEqSpanCertificate timesTableO I181N2
 ![![181, 0, 0, 0], ![-89, 1, 0, 0]] 
 ![![181, 0, 0, 0], ![92, 1, 0, 0], ![43, 0, 1, 0], ![26, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![181, 0, 0, 0], ![0, 181, 0, 0], ![0, 0, 181, 0], ![0, 0, 0, 181]], ![![-89, 1, 0, 0], ![0, -89, 1, 0], ![0, 0, -89, 1], ![383, 332, 80, -88]]]
  hmulB := by decide
  f := ![![![25900, -648033, 8791, -17], ![52671, -1317318, 3077, 0]], ![![13262, -329271, 4499, -9], ![26970, -669338, 1629, 0]], ![![6274, -153951, 2085, -4], ![12759, -312948, 724, 0]], ![![3806, -93004, 1312, -3], ![7740, -189056, 544, 0]]]
  g := ![![![1, 0, 0, 0], ![-92, 181, 0, 0], ![-43, 0, 181, 0], ![-26, 0, 0, 181]], ![![-1, 1, 0, 0], ![45, -89, 1, 0], ![21, 0, -89, 1], ![-173, 332, 80, -88]]]
  hle1 := by decide
  hle2 := by decide

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def I181N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0, 0], ![-13, 1, 0, 0]] i)))

def SI181N3: IdealEqSpanCertificate timesTableO I181N3
 ![![181, 0, 0, 0], ![-13, 1, 0, 0]] 
 ![![181, 0, 0, 0], ![168, 1, 0, 0], ![12, 0, 1, 0], ![156, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![181, 0, 0, 0], ![0, 181, 0, 0], ![0, 0, 181, 0], ![0, 0, 0, 181]], ![![-13, 1, 0, 0], ![0, -13, 1, 0], ![0, 0, -13, 1], ![383, 332, 80, -12]]]
  hmulB := by decide
  f := ![![![209, -3, 30211, -2324], ![2896, 181, 420644, 0]], ![![378, -28213, 2181, -1], ![5250, -392408, 181, 0]], ![![27, -1991, 166, -1], ![375, -27692, 181, 0]], ![![182, 0, 26038, -2003], ![2522, 194, 362544, 0]]]
  g := ![![![1, 0, 0, 0], ![-168, 181, 0, 0], ![-12, 0, 181, 0], ![-156, 0, 0, 181]], ![![-1, 1, 0, 0], ![12, -13, 1, 0], ![0, 0, -13, 1], ![-301, 332, 80, -12]]]
  hle1 := by decide
  hle2 := by decide

lemma NI181N3 : Nat.card (O ⧸ I181N3) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI181N3)

lemma isPrimeI181N3 : Ideal.IsPrime I181N3 := prime_ideal_of_norm_prime hp181.out _ NI181N3
def MulI181N0 : IdealMulEqCertificate timesTableO (I181N0) I181N1
  ![![181, 0, 0, 0], ![37, 1, 0, 0]] ![![181, 0, 0, 0], ![64, 1, 0, 0]]
  ![![181, 0, 0, 0], ![-127, -92, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![32761, 0, 0, 0], ![11584, 181, 0, 0]], ![![6697, 181, 0, 0], ![2368, 101, 1, 0]]]
 hmul := by decide
 f :=  ![![![![-7561232110793044, 506772926445666302, 8795553777347995, 13677824957301], ![21384102675512037, -1433551309394636719, -2475686317272141, 0]], ![![11914075649, 0, 0, 0], ![-2172, 119460, 0, 0]]], ![![![5234325443190475, -350817748208931905, -6088794821895043, -9468587411640], ![-14803321875869577, 992387746186581923, 1713814321507297, 0]], ![![-8247617378, 0, 0, 0], ![1524, -82716, 0, 0]]]]
 g :=  ![![![![30241298, 12530987, -2161636, -236081], ![-27541684, -23424115, 0, 0]], ![![10659730, 4417066, -761944, -83216], ![-9707935, -8256677, 0, 0]]], ![![![6148534, 2547757, -439492, -47999], ![-5599597, -4762472, 0, 0]], ![![2167275, 898062, -154911, -16919], ![-1973692, -1678677, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI181N1 : IdealMulEqCertificate timesTableO (I181N0*I181N1) I181N2
  ![![181, 0, 0, 0], ![-127, -92, -4, 1]] ![![181, 0, 0, 0], ![-89, 1, 0, 0]]
  ![![181, 0, 0, 0], ![-4484, -2303, -135, 34]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI181N0
 hI2 := rfl
 M :=  ![![![32761, 0, 0, 0], ![-16109, 181, 0, 0]], ![![-22987, -16652, -724, 181], ![11686, 8393, 344, -92]]]
 hmul := by decide
 f :=  ![![![![2916677063442004, -72763555067903390, 977744261886039, -1803873312003], ![5931668233278543, -147913166897869582, 326500473242525, 0]], ![![596224958, 0, 0, 0], ![-9955, 0, 0, 0]]], ![![![-72256315672195314, 1802608341635346417, -24222152983276028, 44688265663141], ![-146948216413342356, 3664327673915610920, -8088561314320809, 0]], ![![-14770582358, 0, 0, 0], ![246620, 0, 0, 0]]]]
 g :=  ![![![![181, 0, 0, 0], ![0, 0, 0, 0]], ![![4395, 2304, 135, -34], ![181, 0, 0, 0]]], ![![![4357, 2211, 131, -33], ![181, 0, 0, 0]], ![![3954, 2044, 119, -30], ![157, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI181N2 : IdealMulEqCertificate timesTableO (I181N0*I181N1*I181N2) I181N3
  ![![181, 0, 0, 0], ![-4484, -2303, -135, 34]] ![![181, 0, 0, 0], ![-13, 1, 0, 0]]
  ![![181, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI181N1
 hI2 := rfl
 M :=  ![![![32761, 0, 0, 0], ![-2353, 181, 0, 0]], ![![-811604, -416843, -24435, 6154], ![71314, 36743, 2172, -543]]]
 hmul := by decide
 f :=  ![![![![49416616015, -3734537230966, 288463525510, -114359778], ![686315000546, -51944337199044, 20529935002, 0]], ![![4976024, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![181, 0, 0, 0]], ![![-13, 1, 0, 0]]], ![![![-4484, -2303, -135, 34]], ![![394, 203, 12, -3]]]]
 hle1 := by decide
 hle2 := by decide

def PBC181 : IsPrimesAboveP 181 ![I181N0, I181N1, I181N2, I181N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
    exact isPrimeI181N3
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI181N2, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}
def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate timesTableO I191N0
 ![![191, 0, 0, 0]] 
 ![![191, 0, 0, 0], ![0, 191, 0, 0], ![0, 0, 191, 0], ![0, 0, 0, 191]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![191, 0, 0, 0], ![0, 191, 0, 0], ![0, 0, 191, 0], ![0, 0, 0, 191]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI191N0 : Nat.card (O ⧸ I191N0) = 1330863361 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI191N0)

def MemCI191N0 : IdealMemCertificate B I191N0
  ![![191, 0, 0, 0], ![0, 191, 0, 0], ![0, 0, 191, 0], ![0, 0, 0, 191]] ![2861126016524, 2731243839888, 839028217754, 82388564340] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI191N0
 g := ![14979717364, 14299705968, 4392817894, 431353740]
 hmem := by decide

def P191P0 : CertificateIrreducibleZModOfList' 191 4 2 7 [189, 185, 189, 115, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [186, 163, 2, 60], [71, 31, 126, 137], [10, 187, 63, 185], [0, 1]]
 g := ![![[93, 49, 144, 13], [163, 5, 141, 5], [98, 35, 57, 43], [129, 174, 94, 120], [105, 67, 36, 12], [76, 1], []],![[30, 78, 117, 96, 98, 49], [101, 117, 76, 162, 51, 51], [137, 91, 172, 16, 52, 92], [59, 100, 185, 7, 165, 30], [129, 48, 36, 7, 3, 102], [160, 128, 187, 155, 143, 43], [122, 137, 162]],![[114, 30, 113, 93, 61, 19], [41, 188, 103, 85, 147, 44], [156, 77, 65, 154, 166, 155], [58, 186, 135, 112, 96, 73], [125, 179, 110, 39, 26, 173], [157, 122, 143, 178, 10, 94], [135, 9, 51]],![[141, 3, 188, 39, 98, 82], [101, 105, 10, 163, 106, 186], [171, 22, 134, 56, 64, 179], [75, 67, 167, 148, 97, 126], [107, 105, 52, 66, 81, 21], [143, 140, 0, 42, 31, 82], [50, 70, 36]]]
 h' := ![![[186, 163, 2, 60], [135, 58, 156, 83], [5, 181, 29, 177], [67, 146, 78, 59], [19, 184, 104, 87], [152, 76, 158, 48], [0, 0, 1], [0, 1]],![[71, 31, 126, 137], [185, 34, 187, 2], [140, 118, 175, 121], [175, 13, 95, 72], [16, 146, 31, 67], [78, 142, 30, 21], [78, 140, 53, 65], [186, 163, 2, 60]],![[10, 187, 63, 185], [14, 128, 75, 9], [23, 86, 127, 29], [189, 160, 148, 117], [185, 184, 8, 56], [103, 63, 67, 183], [154, 73, 179, 32], [71, 31, 126, 137]],![[0, 1], [34, 162, 155, 97], [161, 188, 51, 55], [190, 63, 61, 134], [2, 59, 48, 172], [141, 101, 127, 130], [9, 169, 149, 94], [10, 187, 63, 185]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [67, 97, 28], []]
 b := ![[], [], [166, 62, 177, 142], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal O 191 where 
  r := 4
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I191N0
  hcard := NI191N0
  P := [189, 185, 189, 115, 1]
  f := ofList [189, 185, 189, 115, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P191P0
  hneq := by decide
  hlen := by decide
  c := ![2861126016524, 2731243839888, 839028217754, 82388564340]
  a := ![-1, 1, 1, -3]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI191N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI191N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal.isPrime PI191N0
def PBC191 : IsPrimesAboveP 191 ![I191N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I191N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}
def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0, 0], ![21, 1, 0, 0]] i)))

def SI193N0: IdealEqSpanCertificate timesTableO I193N0
 ![![193, 0, 0, 0], ![21, 1, 0, 0]] 
 ![![193, 0, 0, 0], ![21, 1, 0, 0], ![138, 0, 1, 0], ![190, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![193, 0, 0, 0], ![0, 193, 0, 0], ![0, 0, 193, 0], ![0, 0, 0, 193]], ![![21, 1, 0, 0], ![0, 21, 1, 0], ![0, 0, 21, 1], ![383, 332, 80, 22]]]
  hmulB := by decide
  f := ![![![883, 21, 6761, 322], ![-8106, 193, -62146, 0]], ![![63, -18, 965, 46], ![-578, 193, -8878, 0]], ![![654, 10, 4829, 230], ![-6004, 194, -44390, 0]], ![![898, 24, 6656, 317], ![-8244, 172, -61180, 0]]]
  g := ![![![1, 0, 0, 0], ![-21, 193, 0, 0], ![-138, 0, 193, 0], ![-190, 0, 0, 193]], ![![0, 1, 0, 0], ![-3, 21, 1, 0], ![-16, 0, 21, 1], ![-113, 332, 80, 22]]]
  hle1 := by decide
  hle2 := by decide

lemma NI193N0 : Nat.card (O ⧸ I193N0) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI193N0)

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := prime_ideal_of_norm_prime hp193.out _ NI193N0
def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0, 0], ![34, 1, 0, 0]] i)))

def SI193N1: IdealEqSpanCertificate timesTableO I193N1
 ![![193, 0, 0, 0], ![34, 1, 0, 0]] 
 ![![193, 0, 0, 0], ![34, 1, 0, 0], ![2, 0, 1, 0], ![125, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![193, 0, 0, 0], ![0, 193, 0, 0], ![0, 0, 193, 0], ![0, 0, 0, 193]], ![![34, 1, 0, 0], ![0, 34, 1, 0], ![0, 0, 34, 1], ![383, 332, 80, 35]]]
  hmulB := by decide
  f := ![![![4081, -390, 580433, 17072], ![-23160, 2895, -3294896, 0]], ![![714, -81, 107709, 3168], ![-4052, 579, -611424, 0]], ![![6, -34, 5983, 176], ![-34, 194, -33968, 0]], ![![2653, -256, 375928, 11057], ![-15056, 1896, -2134000, 0]]]
  g := ![![![1, 0, 0, 0], ![-34, 193, 0, 0], ![-2, 0, 193, 0], ![-125, 0, 0, 193]], ![![0, 1, 0, 0], ![-6, 34, 1, 0], ![-1, 0, 34, 1], ![-80, 332, 80, 35]]]
  hle1 := by decide
  hle2 := by decide

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0, 0], ![59, 1, 0, 0]] i)))

def SI193N2: IdealEqSpanCertificate timesTableO I193N2
 ![![193, 0, 0, 0], ![59, 1, 0, 0]] 
 ![![193, 0, 0, 0], ![59, 1, 0, 0], ![186, 0, 1, 0], ![27, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![193, 0, 0, 0], ![0, 193, 0, 0], ![0, 0, 193, 0], ![0, 0, 0, 193]], ![![59, 1, 0, 0], ![0, 59, 1, 0], ![0, 0, 59, 1], ![383, 332, 80, 60]]]
  hmulB := by decide
  f := ![![![3895, -76752, -1420, -2], ![-12738, 251286, 386, 0]], ![![1121, -23463, -457, -1], ![-3666, 76814, 193, 0]], ![![3618, -73984, -1373, -2], ![-11832, 242216, 386, 0]], ![![411, -10772, -242, -1], ![-1344, 35260, 194, 0]]]
  g := ![![![1, 0, 0, 0], ![-59, 193, 0, 0], ![-186, 0, 193, 0], ![-27, 0, 0, 193]], ![![0, 1, 0, 0], ![-19, 59, 1, 0], ![-57, 0, 59, 1], ![-185, 332, 80, 60]]]
  hle1 := by decide
  hle2 := by decide

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def I193N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0, 0], ![78, 1, 0, 0]] i)))

def SI193N3: IdealEqSpanCertificate timesTableO I193N3
 ![![193, 0, 0, 0], ![78, 1, 0, 0]] 
 ![![193, 0, 0, 0], ![78, 1, 0, 0], ![92, 0, 1, 0], ![158, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![193, 0, 0, 0], ![0, 193, 0, 0], ![0, 0, 193, 0], ![0, 0, 0, 193]], ![![78, 1, 0, 0], ![0, 78, 1, 0], ![0, 0, 78, 1], ![383, 332, 80, 79]]]
  hmulB := by decide
  f := ![![![5305, -2116, 1218488, 15622], ![-13124, 5404, -3015046, 0]], ![![2106, -909, 501060, 6424], ![-5210, 2316, -1239832, 0]], ![![2528, -1060, 580774, 7446], ![-6254, 2703, -1437078, 0]], ![![4406, -1784, 997518, 12789], ![-10900, 4554, -2468276, 0]]]
  g := ![![![1, 0, 0, 0], ![-78, 193, 0, 0], ![-92, 0, 193, 0], ![-158, 0, 0, 193]], ![![0, 1, 0, 0], ![-32, 78, 1, 0], ![-38, 0, 78, 1], ![-235, 332, 80, 79]]]
  hle1 := by decide
  hle2 := by decide

lemma NI193N3 : Nat.card (O ⧸ I193N3) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI193N3)

lemma isPrimeI193N3 : Ideal.IsPrime I193N3 := prime_ideal_of_norm_prime hp193.out _ NI193N3
def MulI193N0 : IdealMulEqCertificate timesTableO (I193N0) I193N1
  ![![193, 0, 0, 0], ![21, 1, 0, 0]] ![![193, 0, 0, 0], ![34, 1, 0, 0]]
  ![![-407, -204, -11, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![37249, 0, 0, 0], ![6562, 193, 0, 0]], ![![4053, 193, 0, 0], ![714, 55, 1, 0]]]
 hmul := by decide
 f :=  ![![![![299301063465539, -31369710860342, 45812150882387609, 1347450953884729], ![-1698971734357258, 228039090795760, -260058034099752096, 0]], ![![-3156224634, 0, 0, 0], ![4070, -115990, 0, 0]]]]
 g :=  ![![![![69287, 49022, 5790, -965]], ![![10291, 7335, 874, -145]]], ![![![5624, 4033, 484, -80]], ![![832, 602, 73, -12]]]]
 hle1 := by decide
 hle2 := by decide

def MulI193N1 : IdealMulEqCertificate timesTableO (I193N0*I193N1) I193N2
  ![![-407, -204, -11, 3]] ![![193, 0, 0, 0], ![59, 1, 0, 0]]
  ![![193, 0, 0, 0], ![-2345, -1306, -71, 18]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI193N0
 hI2 := rfl
 M :=  ![![![-78551, -39372, -2123, 579], ![-22864, -11447, -613, 169]]]
 hmul := by decide
 f :=  ![![![![-117132460, 80861090596, 1370560079, -9], ![383162121, -264518197405, 1732, 0]]], ![![![1436427853, -991622148910, -16807561221, 110], ![-4698823303, 3243860568872, -21240, 0]]]]
 g :=  ![![![![1938, 1102, 60, -15], ![193, 0, 0, 0]], ![![647, 367, 20, -5], ![63, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI193N2 : IdealMulEqCertificate timesTableO (I193N0*I193N1*I193N2) I193N3
  ![![193, 0, 0, 0], ![-2345, -1306, -71, 18]] ![![193, 0, 0, 0], ![78, 1, 0, 0]]
  ![![193, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI193N1
 hI2 := rfl
 M :=  ![![![37249, 0, 0, 0], ![15054, 193, 0, 0]], ![![-452585, -252058, -13703, 3474], ![-176016, -98237, -5404, 1351]]]
 hmul := by decide
 f :=  ![![![![17516024431503, -2106931875132179, -30790148749702, -48401611448], ![-43340919950241, 5213861453264694, 9341503647032, 0]], ![![409024, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![193, 0, 0, 0]], ![![78, 1, 0, 0]]], ![![![-2345, -1306, -71, 18]], ![![-912, -509, -28, 7]]]]
 hle1 := by decide
 hle2 := by decide

def PBC193 : IsPrimesAboveP 193 ![I193N0, I193N1, I193N2, I193N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
    exact isPrimeI193N2
    exact isPrimeI193N3
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI193N2, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}
def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 0, 0, 0]] i)))

def SI197N0: IdealEqSpanCertificate timesTableO I197N0
 ![![197, 0, 0, 0]] 
 ![![197, 0, 0, 0], ![0, 197, 0, 0], ![0, 0, 197, 0], ![0, 0, 0, 197]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![197, 0, 0, 0], ![0, 197, 0, 0], ![0, 0, 197, 0], ![0, 0, 0, 197]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 1506138481 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI197N0)

def MemCI197N0 : IdealMemCertificate B I197N0
  ![![197, 0, 0, 0], ![0, 197, 0, 0], ![0, 0, 197, 0], ![0, 0, 0, 197]] ![29686790102, 28381411760, 8738400905, 861192001] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI197N0
 g := ![150694366, 144068080, 44357365, 4371533]
 hmem := by decide

def P197P0 : CertificateIrreducibleZModOfList' 197 4 2 7 [119, 143, 113, 107, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [126, 123, 115, 169], [13, 8, 196, 23], [148, 65, 83, 5], [0, 1]]
 g := ![![[138, 5, 91, 154], [127, 70, 150], [68, 131, 146, 26], [107, 96, 9], [67, 153, 190], [107, 90, 1], []],![[125, 164, 180, 183, 192, 154], [164, 50, 112], [51, 130, 67, 21, 120, 196], [107, 177, 97], [127, 166, 136], [66, 40, 168], [141, 155, 164, 157, 32, 112]],![[126, 187, 139, 27, 59, 133], [191, 180, 193], [114, 183, 134, 60, 107, 55], [120, 190, 107], [92, 56, 136], [157, 176, 90], [169, 66, 161, 48, 93, 150]],![[5, 51, 8, 5, 158, 84], [172, 172, 142], [154, 81, 64, 111, 99, 8], [107, 110, 97], [29, 162, 64], [39, 72, 116], [105, 185, 29, 18, 139, 125]]]
 h' := ![![[126, 123, 115, 169], [84, 86, 114, 96], [182, 40, 120, 100], [48, 8, 162, 82], [166, 163, 78, 3], [72, 190, 136, 105], [0, 0, 0, 1], [0, 1]],![[13, 8, 196, 23], [159, 103, 196, 68], [70, 63, 194, 30], [114, 37, 1, 105], [47, 163, 18, 140], [42, 64, 159, 50], [4, 59, 185, 103], [126, 123, 115, 169]],![[148, 65, 83, 5], [33, 24, 27, 10], [111, 130, 80, 28], [54, 20, 10, 99], [100, 130, 174, 111], [4, 179, 20, 50], [13, 9, 196, 22], [13, 8, 196, 23]],![[0, 1], [193, 181, 57, 23], [31, 161, 0, 39], [12, 132, 24, 108], [48, 135, 124, 140], [97, 158, 79, 189], [73, 129, 13, 71], [148, 65, 83, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [153, 87, 3], []]
 b := ![[], [], [24, 99, 180, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal O 197 where 
  r := 4
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I197N0
  hcard := NI197N0
  P := [119, 143, 113, 107, 1]
  f := ofList [119, 143, 113, 107, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P197P0
  hneq := by decide
  hlen := by decide
  c := ![29686790102, 28381411760, 8738400905, 861192001]
  a := ![0, -1, -1, 1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI197N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI197N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal.isPrime PI197N0
def PBC197 : IsPrimesAboveP 197 ![I197N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I197N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}
def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0, 0]] i)))

def SI199N0: IdealEqSpanCertificate timesTableO I199N0
 ![![199, 0, 0, 0]] 
 ![![199, 0, 0, 0], ![0, 199, 0, 0], ![0, 0, 199, 0], ![0, 0, 0, 199]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![199, 0, 0, 0], ![0, 199, 0, 0], ![0, 0, 199, 0], ![0, 0, 0, 199]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI199N0 : Nat.card (O ⧸ I199N0) = 1568239201 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI199N0)

def MemCI199N0 : IdealMemCertificate B I199N0
  ![![199, 0, 0, 0], ![0, 199, 0, 0], ![0, 0, 199, 0], ![0, 0, 0, 199]] ![3167816453554, 3028206976714, 932148067059, 91819080784] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI199N0
 g := ![15918675646, 15217120486, 4684161141, 461402416]
 hmem := by decide

def P199P0 : CertificateIrreducibleZModOfList' 199 4 2 7 [29, 58, 82, 154, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [115, 96, 139, 59], [110, 134, 26, 130], [19, 167, 34, 10], [0, 1]]
 g := ![![[147, 114, 79, 124], [49, 105, 33, 92], [72, 25, 44, 172], [192, 188, 121], [104, 110, 106], [152, 45, 1], []],![[91, 133, 59, 97, 22, 41], [136, 163, 22, 20, 107, 77], [99, 40, 100, 127, 120, 135], [161, 29, 9], [27, 1, 111], [104, 167, 56], [63, 136, 189, 59, 168, 11]],![[53, 170, 1, 19, 195, 81], [149, 116, 18, 79, 54, 65], [25, 41, 49, 17, 36, 10], [110, 62, 193], [124, 96, 162], [79, 37, 47], [187, 177, 136, 100, 33, 40]],![[147, 94, 194, 138, 50, 98], [47, 183, 93, 127, 180, 2], [107, 139, 165, 24, 123, 45], [104, 46, 70], [10, 29, 43], [28, 151, 31], [128, 192, 22, 76, 77, 5]]]
 h' := ![![[115, 96, 139, 59], [171, 135, 126, 129], [101, 82, 71, 93], [159, 38, 139, 157], [73, 43, 49, 188], [169, 28, 21, 107], [0, 0, 0, 1], [0, 1]],![[110, 134, 26, 130], [153, 152, 166, 50], [115, 196, 109, 41], [29, 83, 13, 137], [188, 22, 129, 196], [162, 40, 64, 132], [81, 103, 7, 102], [115, 96, 139, 59]],![[19, 167, 34, 10], [5, 171, 185, 33], [51, 2, 69, 10], [193, 180, 158, 134], [0, 137, 52, 118], [148, 94, 116, 180], [38, 183, 106, 131], [110, 134, 26, 130]],![[0, 1], [157, 139, 120, 186], [105, 118, 149, 55], [92, 97, 88, 169], [116, 196, 168, 95], [159, 37, 197, 178], [162, 112, 86, 164], [19, 167, 34, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [192, 118, 126], []]
 b := ![[], [], [190, 130, 8, 97], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal O 199 where 
  r := 4
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I199N0
  hcard := NI199N0
  P := [29, 58, 82, 154, 1]
  f := ofList [29, 58, 82, 154, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P199P0
  hneq := by decide
  hlen := by decide
  c := ![3167816453554, 3028206976714, 932148067059, 91819080784]
  a := ![19, 1, -1, 3]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI199N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI199N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal.isPrime PI199N0
def PBC199 : IsPrimesAboveP 199 ![I199N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I199N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}
def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0, 0], ![-53, -50, -4, 1]] i)))

def SI211N0: IdealEqSpanCertificate timesTableO I211N0
 ![![211, 0, 0, 0], ![-53, -50, -4, 1]] 
 ![![211, 0, 0, 0], ![0, 211, 0, 0], ![200, 183, 1, 0], ![114, 49, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![211, 0, 0, 0], ![0, 211, 0, 0], ![0, 0, 211, 0], ![0, 0, 0, 211]], ![![-53, -50, -4, 1], ![383, 279, 30, -3], ![-1149, -613, 39, 27], ![10341, 7815, 1547, 66]]]
  hmulB := by decide
  f := ![![![8869245, 6259800, 697392, -59148], ![-3724572, -5401600, 0, 0]], ![![-44307, -31261, -3484, 295], ![18779, 27008, 0, 0]], ![![8368408, 5906317, 658011, -55808], ![-3514240, -5096576, 0, 0]], ![![4781613, 3374801, 375980, -31888], ![-2008015, -2912128, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-200, -183, 211, 0], ![-114, -49, 0, 211]], ![![3, 3, -4, 1], ![-25, -24, 30, -3], ![-57, -43, 39, 27], ![-1453, -1320, 1547, 66]]]
  hle1 := by decide
  hle2 := by decide

lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI211N0)

def MemCI211N0 : IdealMemCertificate B I211N0
  ![![211, 0, 0, 0], ![0, 211, 0, 0], ![200, 183, 1, 0], ![114, 49, 0, 1]] ![126103, 112292, 30581, 2443] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI211N0
 g := ![-29709, -26558, 30581, 2443]
 hmem := by decide

def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [170, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [136, 210], [0, 1]]
 g := ![![[168, 36], [164, 5], [196], [183], [181, 49], [117], [136, 1]],![[0, 175], [0, 206], [196], [183], [93, 162], [117], [61, 210]]]
 h' := ![![[136, 210], [183, 205], [189, 146], [148, 197], [36, 82], [26, 204], [90, 180], [0, 1]],![[0, 1], [0, 6], [0, 65], [143, 14], [5, 129], [129, 7], [94, 31], [136, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [29, 133]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal O 211 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I211N0
  hcard := NI211N0
  P := [170, 75, 1]
  f := ofList [170, 75, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P211P0
  hneq := by decide
  hlen := by decide
  c := ![126103, 112292, 30581, 2443]
  a := ![-1, 0, 1, 2]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI211N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI211N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal.isPrime PI211N0
def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0, 0], ![-197, -150, -4, 1]] i)))

def SI211N1: IdealEqSpanCertificate timesTableO I211N1
 ![![211, 0, 0, 0], ![-197, -150, -4, 1]] 
 ![![211, 0, 0, 0], ![0, 211, 0, 0], ![54, 27, 1, 0], ![19, 169, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![211, 0, 0, 0], ![0, 211, 0, 0], ![0, 0, 211, 0], ![0, 0, 0, 211]], ![![-197, -150, -4, 1], ![383, 135, -70, -3], ![-1149, -613, -105, -73], ![-27959, -25385, -6453, -178]]]
  hmulB := by decide
  f := ![![![4342195, -4800, -1556032, -44362], ![-4021238, -4460540, 0, 0]], ![![-30844, 166, 11118, 316], ![28907, 31861, 0, 0]], ![![1107351, -1188, -396803, -11313], ![-1025406, -1137483, 0, 0]], ![![366185, -386, -131214, -3741], ![-339071, -376141, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-54, -27, 211, 0], ![-19, -169, 0, 211]], ![![0, -1, -4, 1], ![20, 12, -70, -3], ![28, 69, -105, -73], ![1535, 848, -6453, -178]]]
  hle1 := by decide
  hle2 := by decide

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 44521 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI211N1)

def MemCI211N1 : IdealMemCertificate B I211N1
  ![![211, 0, 0, 0], ![0, 211, 0, 0], ![54, 27, 1, 0], ![19, 169, 0, 1]] ![124113, 109100, 28780, 2018] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI211N1
 g := ![-6959, -4782, 28780, 2018]
 hmem := by decide

def P211P1 : CertificateIrreducibleZModOfList' 211 2 2 7 [161, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [178, 210], [0, 1]]
 g := ![![[12, 173], [15, 58], [154], [46], [105, 134], [93], [178, 1]],![[0, 38], [0, 153], [154], [46], [114, 77], [93], [145, 210]]]
 h' := ![![[178, 210], [117, 157], [101, 67], [182, 24], [186, 62], [186, 150], [38, 84], [0, 1]],![[0, 1], [0, 54], [0, 144], [23, 187], [39, 149], [89, 61], [9, 127], [178, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [127, 110]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N1 : CertifiedPrimeIdeal O 211 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I211N1
  hcard := NI211N1
  P := [161, 33, 1]
  f := ofList [161, 33, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P211P1
  hneq := by decide
  hlen := by decide
  c := ![124113, 109100, 28780, 2018]
  a := ![-5, 0, 0, 2]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI211N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI211N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := CertifiedPrimeIdeal.isPrime PI211N1
def MulI211N0 : IdealMulEqCertificate timesTableO (I211N0) I211N1
  ![![211, 0, 0, 0], ![-53, -50, -4, 1]] ![![211, 0, 0, 0], ![-197, -150, -4, 1]]
  ![![211, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![44521, 0, 0, 0], ![-41567, -31650, -844, 211]], ![![-11183, -10550, -844, 211], ![-32072, -21733, -2321, 211]]]
 hmul := by decide
 f :=  ![![![![13031724150261518211953, -14538715433572719858, -4670004758642206994048, -133139431693337869886], ![-12068824505609515116760, -13387081517349790708333, 0, 0]], ![![40854433511808, -8633, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![211, 0, 0, 0]], ![![-197, -150, -4, 1]]], ![![![-53, -50, -4, 1]], ![![-152, -103, -11, 1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC211 : IsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI211N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}
def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0, 0]] i)))

def SI223N0: IdealEqSpanCertificate timesTableO I223N0
 ![![223, 0, 0, 0]] 
 ![![223, 0, 0, 0], ![0, 223, 0, 0], ![0, 0, 223, 0], ![0, 0, 0, 223]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![223, 0, 0, 0], ![0, 223, 0, 0], ![0, 0, 223, 0], ![0, 0, 0, 223]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI223N0 : Nat.card (O ⧸ I223N0) = 2472973441 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI223N0)

def MemCI223N0 : IdealMemCertificate B I223N0
  ![![223, 0, 0, 0], ![0, 223, 0, 0], ![0, 0, 223, 0], ![0, 0, 0, 223]] ![27040287362, 18043334076, 2012288891, -342409141] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI223N0
 g := ![121256894, 80911812, 9023717, -1535467]
 hmem := by decide

def P223P0 : CertificateIrreducibleZModOfList' 223 4 2 7 [89, 48, 190, 74, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 192, 88, 128], [172, 141, 136, 199], [141, 112, 222, 119], [0, 1]]
 g := ![![[72, 48, 192, 101], [140, 68, 147, 33], [203, 26, 64, 169], [32, 126, 200, 58], [39, 160, 204, 136], [157, 149, 1], []],![[71, 167, 105, 208, 186, 200], [182, 85, 19, 2, 50, 130], [214, 103, 179, 106, 87, 55], [212, 145, 91, 78, 188, 181], [166, 76, 109, 29, 134, 30], [39, 179, 146], [9, 185, 128, 189, 88, 60]],![[152, 221, 182, 184, 180, 112], [63, 149, 217, 156, 84, 66], [172, 34, 207, 206, 29, 39], [83, 129, 128, 44, 214, 74], [210, 56, 142, 197, 48, 120], [177, 137, 201], [199, 43, 67, 107, 41, 2]],![[103, 105, 112, 158, 169, 218], [82, 195, 194, 75, 120, 100], [49, 71, 149, 58, 15, 33], [55, 22, 28, 175, 108, 152], [82, 148, 130, 94, 75, 199], [7, 147, 60], [151, 25, 185, 54, 167, 171]]]
 h' := ![![[59, 192, 88, 128], [28, 178, 151, 18], [219, 132, 163, 207], [51, 4, 209, 13], [97, 145, 85, 113], [76, 165, 170, 164], [0, 0, 0, 1], [0, 1]],![[172, 141, 136, 199], [116, 163, 9, 166], [51, 193, 68, 89], [154, 100, 148, 44], [130, 160, 16, 201], [84, 26, 130, 155], [87, 114, 44, 102], [59, 192, 88, 128]],![[141, 112, 222, 119], [139, 121, 38, 211], [217, 79, 171, 62], [116, 19, 80, 159], [85, 150, 141, 57], [112, 97, 194, 21], [163, 165, 202, 147], [172, 141, 136, 199]],![[0, 1], [44, 207, 25, 51], [34, 42, 44, 88], [184, 100, 9, 7], [151, 214, 204, 75], [74, 158, 175, 106], [52, 167, 200, 196], [141, 112, 222, 119]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [108, 213, 34], []]
 b := ![[], [], [101, 51, 162, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal O 223 where 
  r := 4
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I223N0
  hcard := NI223N0
  P := [89, 48, 190, 74, 1]
  f := ofList [89, 48, 190, 74, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P223P0
  hneq := by decide
  hlen := by decide
  c := ![27040287362, 18043334076, 2012288891, -342409141]
  a := ![-10, 2, 13, -1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI223N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI223N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal.isPrime PI223N0
def PBC223 : IsPrimesAboveP 223 ![I223N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I223N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}
def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0, 0], ![-19, -131, -4, 1]] i)))

def SI227N0: IdealEqSpanCertificate timesTableO I227N0
 ![![227, 0, 0, 0], ![-19, -131, -4, 1]] 
 ![![227, 0, 0, 0], ![0, 227, 0, 0], ![193, 149, 1, 0], ![72, 11, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![227, 0, 0, 0], ![0, 227, 0, 0], ![0, 0, 227, 0], ![0, 0, 0, 227]], ![![-19, -131, -4, 1], ![383, 313, -51, -3], ![-1149, -613, 73, -54], ![-20682, -19077, -4933, 19]]]
  hmulB := by decide
  f := ![![![11337283, 6800778, -1649028, -70638], ![-4844634, -6959820, 0, 0]], ![![-53980, -32335, 7854, 336], ![23154, 33142, 0, 0]], ![![9603750, 5760894, -1396883, -59837], ![-4103879, -5895626, 0, 0]], ![![3593356, 2155545, -522658, -22389], ![-1535438, -2205914, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-193, -149, 227, 0], ![-72, -11, 0, 227]], ![![3, 2, -4, 1], ![46, 35, -51, -3], ![-50, -48, 73, -54], ![4097, 3153, -4933, 19]]]
  hle1 := by decide
  hle2 := by decide

lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI227N0)

def MemCI227N0 : IdealMemCertificate B I227N0
  ![![227, 0, 0, 0], ![0, 227, 0, 0], ![193, 149, 1, 0], ![72, 11, 0, 1]] ![39727, 37790, 11024, 1000] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI227N0
 g := ![-9515, -7118, 11024, 1000]
 hmem := by decide

def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [132, 145, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 226], [0, 1]]
 g := ![![[106, 43], [186, 101], [160], [23], [166], [220, 81], [82, 1]],![[0, 184], [69, 126], [160], [23], [166], [52, 146], [164, 226]]]
 h' := ![![[82, 226], [191, 161], [113, 151], [24, 198], [136, 134], [16, 47], [72, 9], [0, 1]],![[0, 1], [0, 66], [10, 76], [143, 29], [1, 93], [11, 180], [129, 218], [82, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [210]]
 b := ![[], [8, 105]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal O 227 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I227N0
  hcard := NI227N0
  P := [132, 145, 1]
  f := ofList [132, 145, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P227P0
  hneq := by decide
  hlen := by decide
  c := ![39727, 37790, 11024, 1000]
  a := ![1, 1, -4, -1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI227N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI227N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal.isPrime PI227N0
def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0, 0], ![-158, -50, -4, 1]] i)))

def SI227N1: IdealEqSpanCertificate timesTableO I227N1
 ![![227, 0, 0, 0], ![-158, -50, -4, 1]] 
 ![![227, 0, 0, 0], ![0, 227, 0, 0], ![58, 77, 1, 0], ![74, 31, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![227, 0, 0, 0], ![0, 227, 0, 0], ![0, 0, 227, 0], ![0, 0, 0, 227]], ![![-158, -50, -4, 1], ![383, 174, 30, -3], ![-1149, -613, -66, 27], ![10341, 7815, 1547, -39]]]
  hmulB := by decide
  f := ![![![1448734, 771496, 157058, -12584], ![-1181081, -1345883, 0, 0]], ![![-11815, -6325, -1294, 103], ![9988, 11123, 0, 0]], ![![366097, 194959, 39689, -3180], ![-298467, -340109, 0, 0]], ![![470787, 250677, 51026, -4089], ![-383477, -437227, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-58, -77, 227, 0], ![-74, -31, 0, 227]], ![![0, 1, -4, 1], ![-5, -9, 30, -3], ![3, 16, -66, 27], ![-337, -485, 1547, -39]]]
  hle1 := by decide
  hle2 := by decide

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 51529 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI227N1)

def MemCI227N1 : IdealMemCertificate B I227N1
  ![![227, 0, 0, 0], ![0, 227, 0, 0], ![58, 77, 1, 0], ![74, 31, 0, 1]] ![31548, 26860, 6593, 351] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI227N1
 g := ![-1660, -2166, 6593, 351]
 hmem := by decide

def P227P1 : CertificateIrreducibleZModOfList' 227 2 2 7 [208, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [202, 226], [0, 1]]
 g := ![![[154, 79], [136, 129], [136], [16], [182], [17, 7], [202, 1]],![[222, 148], [89, 98], [136], [16], [182], [69, 220], [177, 226]]]
 h' := ![![[202, 226], [87, 144], [171, 122], [159, 131], [189, 223], [96, 149], [206, 190], [0, 1]],![[0, 1], [119, 83], [72, 105], [62, 96], [62, 4], [3, 78], [223, 37], [202, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136]]
 b := ![[], [169, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N1 : CertifiedPrimeIdeal O 227 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I227N1
  hcard := NI227N1
  P := [208, 25, 1]
  f := ofList [208, 25, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P227P1
  hneq := by decide
  hlen := by decide
  c := ![31548, 26860, 6593, 351]
  a := ![-3, 1, -1, 1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI227N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI227N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := CertifiedPrimeIdeal.isPrime PI227N1
def MulI227N0 : IdealMulEqCertificate timesTableO (I227N0) I227N1
  ![![227, 0, 0, 0], ![-19, -131, -4, 1]] ![![227, 0, 0, 0], ![-158, -50, -4, 1]]
  ![![227, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![51529, 0, 0, 0], ![-35866, -11350, -908, 227]], ![![-4313, -29737, -908, 227], ![-32234, -11577, -2043, 227]]]
 hmul := by decide
 f :=  ![![![![1706664247942394105778, 908865853914991500216, 185022676968402988812, -14824558781829110676], ![-1391414797961688479211, -1585524905440390312069, 0, 0]], ![![14925115707587850, -6026202, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![227, 0, 0, 0]], ![![-158, -50, -4, 1]]], ![![![-19, -131, -4, 1]], ![![-142, -51, -9, 1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC227 : IsPrimesAboveP 227 ![I227N0, I227N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI227N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0, 0], ![44, 1, 0, 0]] i)))

def SI229N0: IdealEqSpanCertificate timesTableO I229N0
 ![![229, 0, 0, 0], ![44, 1, 0, 0]] 
 ![![229, 0, 0, 0], ![44, 1, 0, 0], ![125, 0, 1, 0], ![225, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![229, 0, 0, 0], ![0, 229, 0, 0], ![0, 0, 229, 0], ![0, 0, 0, 229]], ![![44, 1, 0, 0], ![0, 44, 1, 0], ![0, 0, 44, 1], ![383, 332, 80, 45]]]
  hmulB := by decide
  f := ![![![5941, 47, 98250, 2233], ![-30915, 458, -511357, 0]], ![![1100, -19, 26795, 609], ![-5724, 229, -139461, 0]], ![![3221, 29, 53591, 1218], ![-16761, 230, -278922, 0]], ![![5833, 53, 96534, 2194], ![-30353, 414, -502425, 0]]]
  g := ![![![1, 0, 0, 0], ![-44, 229, 0, 0], ![-125, 0, 229, 0], ![-225, 0, 0, 229]], ![![0, 1, 0, 0], ![-9, 44, 1, 0], ![-25, 0, 44, 1], ![-150, 332, 80, 45]]]
  hle1 := by decide
  hle2 := by decide

lemma NI229N0 : Nat.card (O ⧸ I229N0) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI229N0)

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := prime_ideal_of_norm_prime hp229.out _ NI229N0
def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0, 0], ![70, 1, 0, 0]] i)))

def SI229N1: IdealEqSpanCertificate timesTableO I229N1
 ![![229, 0, 0, 0], ![70, 1, 0, 0]] 
 ![![229, 0, 0, 0], ![70, 1, 0, 0], ![138, 0, 1, 0], ![187, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![229, 0, 0, 0], ![0, 229, 0, 0], ![0, 0, 229, 0], ![0, 0, 0, 229]], ![![70, 1, 0, 0], ![0, 70, 1, 0], ![0, 0, 70, 1], ![383, 332, 80, 71]]]
  hmulB := by decide
  f := ![![![4621, -91214, -1444, -2], ![-15114, 298616, 458, 0]], ![![1330, -27981, -470, -1], ![-4350, 91600, 229, 0]], ![![2682, -55052, -857, -1], ![-8772, 180224, 229, 0]], ![![3823, -74544, -1206, -2], ![-12504, 244044, 459, 0]]]
  g := ![![![1, 0, 0, 0], ![-70, 229, 0, 0], ![-138, 0, 229, 0], ![-187, 0, 0, 229]], ![![0, 1, 0, 0], ![-22, 70, 1, 0], ![-43, 0, 70, 1], ![-206, 332, 80, 71]]]
  hle1 := by decide
  hle2 := by decide

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulEqCertificate timesTableO (I229N0) I229N0
  ![![229, 0, 0, 0], ![44, 1, 0, 0]] ![![229, 0, 0, 0], ![44, 1, 0, 0]]
  ![![229, 0, 0, 0], ![-179, 23, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![52441, 0, 0, 0], ![10076, 229, 0, 0]], ![![10076, 229, 0, 0], ![1936, 88, 1, 0]]]
 hmul := by decide
 f :=  ![![![![553835062754804685, -164764794295811733177, -3902265455880868416, -3575567458750583], ![-2882458600956975375, 857591167837260985975, 818800315438468280, 0]], ![![0, 0, 0, 0], ![-6023829859355, 1060996184028891, -1429819572, 0]]], ![![![-410103222653560056, 122004866908364819611, 2889545546551007907, 2647632546692969], ![2134400006272756644, -635028233676700240843, -606304422838350018, 0]], ![![0, 0, 0, 0], ![4460519393176, -785645372702377, 1058751339, 0]]]]
 g :=  ![![![![539067877, 375277824, 219666048, -4902912], ![-387533952, -503433600, 0, 0]], ![![103537236, 72078457, 42190592, -941688], ![-74432328, -96692960, 0, 0]]], ![![![103537236, 72078457, 42190592, -941688], ![-74432328, -96692960, 0, 0]], ![![19886057, 13843891, 8103417, -180867], ![-14296017, -18571520, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI229N1 : IdealMulEqCertificate timesTableO (I229N0*I229N0) I229N1
  ![![229, 0, 0, 0], ![-179, 23, -4, 1]] ![![229, 0, 0, 0], ![70, 1, 0, 0]]
  ![![229, 0, 0, 0], ![-5403, -2862, -163, 41]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI229N0
 hI2 := rfl
 M :=  ![![![52441, 0, 0, 0], ![16030, 229, 0, 0]], ![![-40991, 5267, -916, 229], ![-12147, 1763, -177, 67]]]
 hmul := by decide
 f :=  ![![![![14566700140867, -282902847149551, -4388296892470, -4930577781], ![-47643795667449, 926175781987782, 1125143454277, 0]], ![![3958843770, 0, 0, 0], ![47174, 0, 0, 0]]], ![![![-343685106085069, 6674778370729790, 103536989737061, 116331504809], ![1124102426075478, -21852088585866550, -26546509755178, 0]], ![![-93404520440, 0, 0, 0], ![-1113018, 0, 0, 0]]]]
 g :=  ![![![![229, 0, 0, 0], ![0, 0, 0, 0]], ![![70, 1, 0, 0], ![0, 0, 0, 0]]], ![![![5224, 2885, 159, -40], ![229, 0, 0, 0]], ![![2094, 1145, 64, -16], ![91, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI229N2 : IdealMulEqCertificate timesTableO (I229N0*I229N0*I229N1) I229N1
  ![![229, 0, 0, 0], ![-5403, -2862, -163, 41]] ![![229, 0, 0, 0], ![70, 1, 0, 0]]
  ![![229, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI229N1
 hI2 := rfl
 M :=  ![![![52441, 0, 0, 0], ![16030, 229, 0, 0]], ![![-1237287, -655398, -37327, 9389], ![-362507, -192131, -10992, 2748]]]
 hmul := by decide
 f :=  ![![![![288660815838, -5506178718877, -85399887844, -95931214], ![-944132889414, 18026664180312, 21861934162, 0]], ![![0, 0, 0, 0], ![8859487, 0, 0, 0]]]]
 g :=  ![![![![229, 0, 0, 0]], ![![70, 1, 0, 0]]], ![![![-5403, -2862, -163, 41]], ![![-1583, -839, -48, 12]]]]
 hle1 := by decide
 hle2 := by decide

def PBC229 : IsPrimesAboveP 229 ![I229N0, I229N0, I229N1, I229N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N0
    exact isPrimeI229N1
    exact isPrimeI229N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI229N2, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl

