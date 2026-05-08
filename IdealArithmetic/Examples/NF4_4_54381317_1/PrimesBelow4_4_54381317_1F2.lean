
import IdealArithmetic.Examples.NF4_4_54381317_1.RI4_4_54381317_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic

set_option linter.all false

open Classical Polynomial

noncomputable section 
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}
def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate timesTableO I73N0
 ![![73, 0, 0, 0]] 
 ![![73, 0, 0, 0], ![0, 73, 0, 0], ![0, 0, 73, 0], ![0, 0, 0, 73]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![73, 0, 0, 0], ![0, 73, 0, 0], ![0, 0, 73, 0], ![0, 0, 0, 73]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 28398241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI73N0)

def MemCI73N0 : IdealMemCertificate B I73N0
  ![![73, 0, 0, 0], ![0, 73, 0, 0], ![0, 0, 73, 0], ![0, 0, 0, 73]] ![59457294624, 56854485464, 17508324234, 1725597141] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI73N0
 g := ![814483488, 778828568, 239840058, 23638317]
 hmem := by decide

def P73P0 : CertificateIrreducibleZModOfList' 73 4 2 6 [50, 39, 7, 12, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 22, 65, 61], [52, 59, 42, 5], [12, 64, 39, 7], [0, 1]]
 g := ![![[57, 2, 32, 41], [2, 60, 18], [55, 12, 6], [7, 9, 46, 71], [1], []],![[46, 72, 59, 27, 49, 27], [21, 66, 6], [61, 17, 50], [4, 51, 23, 41, 25, 23], [54, 42, 12], [24, 70, 71]],![[13, 57, 28, 29, 66, 42], [71], [53, 24, 55], [19, 33, 35, 56, 13, 47], [9, 68, 65], [9, 47, 25]],![[72, 41, 55, 47, 19, 62], [57, 70, 57], [1, 30, 64], [36, 40, 27, 65, 33, 51], [16, 3, 32], [23, 31, 49]]]
 h' := ![![[70, 22, 65, 61], [70, 8, 28, 25], [30, 49, 67, 50], [15, 25, 32, 15], [23, 34, 66, 61], [0, 0, 1], [0, 1]],![[52, 59, 42, 5], [26, 44, 44, 69], [28, 60, 10, 58], [31, 66, 9, 14], [19, 62, 16, 49], [50, 31, 70, 42], [70, 22, 65, 61]],![[12, 64, 39, 7], [29, 10, 43, 13], [32, 40, 61], [28, 3, 46, 36], [69, 46, 63, 43], [64, 4, 31, 49], [52, 59, 42, 5]],![[0, 1], [9, 11, 31, 39], [42, 70, 8, 38], [26, 52, 59, 8], [40, 4, 1, 66], [16, 38, 44, 55], [12, 64, 39, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [28, 49, 33], []]
 b := ![[], [], [11, 60, 19, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal O 73 where 
  r := 4
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I73N0
  hcard := NI73N0
  P := [50, 39, 7, 12, 1]
  f := ofList [50, 39, 7, 12, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P73P0
  hneq := by decide
  hlen := by decide
  c := ![59457294624, 56854485464, 17508324234, 1725597141]
  a := ![0, -1, -1, -1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI73N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI73N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal.isPrime PI73N0
def PBC73 : IsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I73N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}
def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0], ![-100, -73, -4, 1]] i)))

def SI79N0: IdealEqSpanCertificate timesTableO I79N0
 ![![79, 0, 0, 0], ![-100, -73, -4, 1]] 
 ![![79, 0, 0, 0], ![0, 79, 0, 0], ![15, 29, 1, 0], ![39, 43, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![79, 0, 0, 0], ![0, 79, 0, 0], ![0, 0, 79, 0], ![0, 0, 0, 79]], ![![-100, -73, -4, 1], ![383, 232, 7, -3], ![-1149, -613, -8, 4], ![1532, 179, -293, -4]]]
  hmulB := by decide
  f := ![![![39165, 13932, -996, -136], ![-62252, -24332, 0, 0]], ![![-3524, -1239, 92, 12], ![5688, 2212, 0, 0]], ![![6201, 2233, -153, -22], ![-9686, -3808, 0, 0]], ![![17457, 6233, -440, -61], ![-27604, -10808, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-15, -29, 79, 0], ![-39, -43, 0, 79]], ![![-1, 0, -4, 1], ![5, 2, 7, -3], ![-15, -7, -8, 4], ![77, 112, -293, -4]]]
  hle1 := by decide
  hle2 := by decide

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI79N0)

def MemCI79N0 : IdealMemCertificate B I79N0
  ![![79, 0, 0, 0], ![0, 79, 0, 0], ![15, 29, 1, 0], ![39, 43, 0, 1]] ![1553026, 1297694, 281028, -6132] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI79N0
 g := ![-30674, -83398, 281028, -6132]
 hmem := by decide

def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [15, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 78], [0, 1]]
 g := ![![[23, 40], [31, 13], [30, 72], [30, 55], [51], [1]],![[48, 39], [49, 66], [75, 7], [15, 24], [51], [1]]]
 h' := ![![[50, 78], [9, 35], [24, 48], [24, 54], [13, 23], [64, 50], [0, 1]],![[0, 1], [21, 44], [54, 31], [38, 25], [57, 56], [36, 29], [50, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [12, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal O 79 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I79N0
  hcard := NI79N0
  P := [15, 29, 1]
  f := ofList [15, 29, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P79P0
  hneq := by decide
  hlen := by decide
  c := ![1553026, 1297694, 281028, -6132]
  a := ![-2, 3, -64, 1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI79N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI79N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal.isPrime PI79N0
def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0], ![-153, -84, -4, 1]] i)))

def SI79N1: IdealEqSpanCertificate timesTableO I79N1
 ![![79, 0, 0, 0], ![-153, -84, -4, 1]] 
 ![![79, 0, 0, 0], ![0, 79, 0, 0], ![64, 49, 1, 0], ![24, 33, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![79, 0, 0, 0], ![0, 79, 0, 0], ![0, 0, 79, 0], ![0, 0, 0, 79]], ![![-153, -84, -4, 1], ![383, 179, -4, -3], ![-1149, -613, -61, -7], ![-2681, -3473, -1173, -68]]]
  hmulB := by decide
  f := ![![![261817, 36408, -41248, -3416], ![-543520, -271128, 0, 0]], ![![-3235, -399, 532, 43], ![7031, 3476, 0, 0]], ![![209988, 29187, -33089, -2740], ![-436016, -217492, 0, 0]], ![![78219, 10911, -12308, -1020], ![-162167, -80916, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-64, -49, 79, 0], ![-24, -33, 0, 79]], ![![1, 1, -4, 1], ![9, 6, -4, -3], ![37, 33, -61, -7], ![937, 712, -1173, -68]]]
  hle1 := by decide
  hle2 := by decide

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 6241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI79N1)

def MemCI79N1 : IdealMemCertificate B I79N1
  ![![79, 0, 0, 0], ![0, 79, 0, 0], ![64, 49, 1, 0], ![24, 33, 0, 1]] ![274985, 239559, 61918, 3846] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI79N1
 g := ![-47849, -36979, 61918, 3846]
 hmem := by decide

def P79P1 : CertificateIrreducibleZModOfList' 79 2 2 6 [26, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 78], [0, 1]]
 g := ![![[50, 76], [59, 10], [16, 19], [43, 2], [32], [1]],![[0, 3], [15, 69], [43, 60], [50, 77], [32], [1]]]
 h' := ![![[43, 78], [46, 32], [58, 22], [67, 63], [2, 9], [53, 43], [0, 1]],![[0, 1], [0, 47], [56, 57], [11, 16], [73, 70], [6, 36], [43, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [40, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N1 : CertifiedPrimeIdeal O 79 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I79N1
  hcard := NI79N1
  P := [26, 36, 1]
  f := ofList [26, 36, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P79P1
  hneq := by decide
  hlen := by decide
  c := ![274985, 239559, 61918, 3846]
  a := ![-1, 1, 1, -3]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI79N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI79N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := CertifiedPrimeIdeal.isPrime PI79N1
def MulI79N0 : IdealMulEqCertificate timesTableO (I79N0) I79N1
  ![![79, 0, 0, 0], ![-100, -73, -4, 1]] ![![79, 0, 0, 0], ![-153, -84, -4, 1]]
  ![![79, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![6241, 0, 0, 0], ![-12087, -6636, -316, 79]], ![![-7900, -5767, -316, 79], ![-10744, -5688, -237, 79]]]
 hmul := by decide
 f :=  ![![![![688063795371162836406, 95607883699166904654, -108434653319152930657, -8978570213494954133], ![-1428861555436136926300, -712722862479842832116, 0, 0]], ![![14862708778014, -342815, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![79, 0, 0, 0]], ![![-153, -84, -4, 1]]], ![![![-100, -73, -4, 1]], ![![-136, -72, -3, 1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC79 : IsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI79N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}
def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0, 0], ![-114, -67, -4, 1]] i)))

def SI83N0: IdealEqSpanCertificate timesTableO I83N0
 ![![83, 0, 0, 0], ![-114, -67, -4, 1]] 
 ![![83, 0, 0, 0], ![0, 83, 0, 0], ![41, 17, 1, 0], ![50, 1, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![83, 0, 0, 0], ![0, 83, 0, 0], ![0, 0, 83, 0], ![0, 0, 0, 83]], ![![-114, -67, -4, 1], ![383, 218, 13, -3], ![-1149, -613, -22, 10], ![3830, 2171, 187, -12]]]
  hmulB := by decide
  f := ![![![203782, 106673, 6341, -1124], ![-366113, -153135, 0, 0]], ![![-4417, -2304, -137, 24], ![8217, 3403, 0, 0]], ![![99723, 52201, 3103, -550], ![-179194, -74948, 0, 0]], ![![122729, 64246, 3819, -677], ![-220435, -92209, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-41, -17, 83, 0], ![-50, -1, 0, 83]], ![![0, 0, -4, 1], ![0, 0, 13, -3], ![-9, -3, -22, 10], ![-39, -12, 187, -12]]]
  hle1 := by decide
  hle2 := by decide

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI83N0)

def MemCI83N0 : IdealMemCertificate B I83N0
  ![![83, 0, 0, 0], ![0, 83, 0, 0], ![41, 17, 1, 0], ![50, 1, 0, 1]] ![29938, 25489, 6268, 356] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI83N0
 g := ![-2950, -981, 6268, 356]
 hmem := by decide

def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [64, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 82], [0, 1]]
 g := ![![[73, 48], [61, 44], [27], [75], [38, 78], [1]],![[0, 35], [1, 39], [27], [75], [75, 5], [1]]]
 h' := ![![[59, 82], [80, 31], [59, 58], [58, 39], [58, 18], [19, 59], [0, 1]],![[0, 1], [0, 52], [78, 25], [35, 44], [41, 65], [14, 24], [59, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [2, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal O 83 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I83N0
  hcard := NI83N0
  P := [64, 24, 1]
  f := ofList [64, 24, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P83P0
  hneq := by decide
  hlen := by decide
  c := ![29938, 25489, 6268, 356]
  a := ![0, -1, -1, 1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI83N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI83N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal.isPrime PI83N0
def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0, 0], ![-149, -67, -4, 1]] i)))

def SI83N1: IdealEqSpanCertificate timesTableO I83N1
 ![![83, 0, 0, 0], ![-149, -67, -4, 1]] 
 ![![83, 0, 0, 0], ![0, 83, 0, 0], ![19, 65, 1, 0], ![10, 27, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![83, 0, 0, 0], ![0, 83, 0, 0], ![0, 0, 83, 0], ![0, 0, 0, 83]], ![![-149, -67, -4, 1], ![383, 183, 13, -3], ![-1149, -613, -57, 10], ![3830, 2171, 187, -47]]]
  hmulB := by decide
  f := ![![![24221, 14340, 1520, -300], ![-54780, -26560, 0, 0]], ![![-531, -324, -36, 7], ![1411, 664, 0, 0]], ![![5100, 3016, 319, -63], ![-11451, -5560, 0, 0]], ![![2767, 1632, 172, -34], ![-6129, -2984, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-19, -65, 83, 0], ![-10, -27, 0, 83]], ![![-1, 2, -4, 1], ![2, -7, 13, -3], ![-2, 34, -57, 10], ![9, -105, 187, -47]]]
  hle1 := by decide
  hle2 := by decide

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 6889 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI83N1)

def MemCI83N1 : IdealMemCertificate B I83N1
  ![![83, 0, 0, 0], ![0, 83, 0, 0], ![19, 65, 1, 0], ![10, 27, 0, 1]] ![280067, 243552, 62801, 4085] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI83N1
 g := ![-11494, -47576, 62801, 4085]
 hmem := by decide

def P83P1 : CertificateIrreducibleZModOfList' 83 2 2 6 [21, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [78, 82], [0, 1]]
 g := ![![[20, 4], [43, 75], [3], [38], [2, 25], [1]],![[0, 79], [0, 8], [3], [38], [43, 58], [1]]]
 h' := ![![[78, 82], [10, 2], [7, 18], [53, 70], [41, 72], [62, 78], [0, 1]],![[0, 1], [0, 81], [0, 65], [35, 13], [13, 11], [4, 5], [78, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [24, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N1 : CertifiedPrimeIdeal O 83 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I83N1
  hcard := NI83N1
  P := [21, 5, 1]
  f := ofList [21, 5, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P83P1
  hneq := by decide
  hlen := by decide
  c := ![280067, 243552, 62801, 4085]
  a := ![19, 1, -1, 3]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI83N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI83N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := CertifiedPrimeIdeal.isPrime PI83N1
def MulI83N0 : IdealMulEqCertificate timesTableO (I83N0) I83N1
  ![![83, 0, 0, 0], ![-114, -67, -4, 1]] ![![83, 0, 0, 0], ![-149, -67, -4, 1]]
  ![![83, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![6889, 0, 0, 0], ![-12367, -5561, -332, 83]], ![![-9462, -5561, -332, 83], ![-249, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![9157668676, 5429060124, 576486264, -113710884], ![-20851316791, -10096346424, 0, 0]], ![![280891, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![83, 0, 0, 0]], ![![-149, -67, -4, 1]]], ![![![-114, -67, -4, 1]], ![![-3, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC83 : IsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI83N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}
def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate timesTableO I89N0
 ![![89, 0, 0, 0]] 
 ![![89, 0, 0, 0], ![0, 89, 0, 0], ![0, 0, 89, 0], ![0, 0, 0, 89]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![89, 0, 0, 0], ![0, 89, 0, 0], ![0, 0, 89, 0], ![0, 0, 0, 89]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 62742241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI89N0)

def MemCI89N0 : IdealMemCertificate B I89N0
  ![![89, 0, 0, 0], ![0, 89, 0, 0], ![0, 0, 89, 0], ![0, 0, 0, 89]] ![796538998710, 761617871486, 234518657811, 23111002020] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI89N0
 g := ![8949876390, 8557504174, 2635041099, 259674180]
 hmem := by decide

def P89P0 : CertificateIrreducibleZModOfList' 89 4 2 6 [76, 58, 43, 39, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 33, 15, 81], [73, 31, 63, 16], [28, 24, 11, 81], [0, 1]]
 g := ![![[44, 20, 56, 20], [8, 50, 21], [1, 5, 34], [73, 57, 74, 68], [50, 1], []],![[51, 22, 87, 26, 81, 4], [27, 81, 34], [21, 61, 47], [24, 84, 49, 4], [19, 57, 58, 67, 43, 44], [53, 23, 64]],![[37, 76, 41, 56, 3, 39], [53, 63, 57], [59, 85, 69], [51, 58, 39, 47, 66, 85], [5, 43, 8, 68, 50, 88], [58, 42, 78]],![[79, 3, 3, 5, 87, 32], [77, 79, 39], [38, 14, 42], [1, 84, 20, 1, 32, 84], [29, 48, 64, 48, 23, 34], [0, 87, 64]]]
 h' := ![![[38, 33, 15, 81], [10, 68, 11, 38], [23, 40, 61, 56], [59, 84, 65, 52], [27, 50, 17, 54], [0, 0, 1], [0, 1]],![[73, 31, 63, 16], [83, 16, 34, 69], [55, 4, 13, 37], [7, 37, 75, 15], [55, 25, 69], [86, 0, 71, 22], [38, 33, 15, 81]],![[28, 24, 11, 81], [57, 19, 24, 50], [13, 19, 19, 18], [74, 23, 65, 46], [86, 24, 23, 72], [31, 17, 13, 53], [73, 31, 63, 16]],![[0, 1], [79, 75, 20, 21], [71, 26, 85, 67], [72, 34, 62, 65], [14, 79, 69, 52], [72, 72, 4, 14], [28, 24, 11, 81]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [26, 70, 76], []]
 b := ![[], [], [40, 79, 78, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal O 89 where 
  r := 4
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I89N0
  hcard := NI89N0
  P := [76, 58, 43, 39, 1]
  f := ofList [76, 58, 43, 39, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P89P0
  hneq := by decide
  hlen := by decide
  c := ![796538998710, 761617871486, 234518657811, 23111002020]
  a := ![-1, 0, 1, 2]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI89N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI89N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal.isPrime PI89N0
def PBC89 : IsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I89N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}
def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0], ![-162, -67, -4, 1]] i)))

def SI97N0: IdealEqSpanCertificate timesTableO I97N0
 ![![97, 0, 0, 0], ![-162, -67, -4, 1]] 
 ![![97, 0, 0, 0], ![0, 97, 0, 0], ![91, 66, 1, 0], ![8, 3, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![97, 0, 0, 0], ![0, 97, 0, 0], ![0, 0, 97, 0], ![0, 0, 0, 97]], ![![-162, -67, -4, 1], ![383, 170, 13, -3], ![-1149, -613, -70, 10], ![3830, 2171, 187, -60]]]
  hmulB := by decide
  f := ![![![32258, 17644, 2111, -435], ![-65766, -35987, 0, 0]], ![![-4585, -2510, -301, 62], ![9409, 5141, 0, 0]], ![![27158, 14851, 1776, -366], ![-55287, -30263, 0, 0]], ![![2527, 1381, 165, -34], ![-5128, -2809, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-91, -66, 97, 0], ![-8, -3, 0, 97]], ![![2, 2, -4, 1], ![-8, -7, 13, -3], ![53, 41, -70, 10], ![-131, -103, 187, -60]]]
  hle1 := by decide
  hle2 := by decide

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI97N0)

def MemCI97N0 : IdealMemCertificate B I97N0
  ![![97, 0, 0, 0], ![0, 97, 0, 0], ![91, 66, 1, 0], ![8, 3, 0, 1]] ![124004, 109100, 28780, 2020] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI97N0
 g := ![-25888, -18520, 28780, 2020]
 hmem := by decide

def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [57, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 96], [0, 1]]
 g := ![![[4, 6], [72], [43], [91], [54], [63, 1]],![[91, 91], [72], [43], [91], [54], [29, 96]]]
 h' := ![![[63, 96], [63, 54], [44, 13], [78, 25], [30, 73], [95, 32], [0, 1]],![[0, 1], [70, 43], [87, 84], [4, 72], [70, 24], [74, 65], [63, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74]]
 b := ![[], [47, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal O 97 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I97N0
  hcard := NI97N0
  P := [57, 34, 1]
  f := ofList [57, 34, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P97P0
  hneq := by decide
  hlen := by decide
  c := ![124004, 109100, 28780, 2020]
  a := ![-5, 0, 0, 2]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI97N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI97N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal.isPrime PI97N0
def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0], ![-42, 1, 0, 0]] i)))

def SI97N1: IdealEqSpanCertificate timesTableO I97N1
 ![![97, 0, 0, 0], ![-42, 1, 0, 0]] 
 ![![97, 0, 0, 0], ![55, 1, 0, 0], ![79, 0, 1, 0], ![20, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![97, 0, 0, 0], ![0, 97, 0, 0], ![0, 0, 97, 0], ![0, 0, 0, 97]], ![![-42, 1, 0, 0], ![0, -42, 1, 0], ![0, 0, -42, 1], ![383, 332, 80, -41]]]
  hmulB := by decide
  f := ![![![6637, -83066, 2310, -8], ![15326, -191478, 776, 0]], ![![3823, -47089, 1329, -5], ![8828, -108543, 485, 0]], ![![5395, -67622, 1901, -7], ![12458, -155878, 679, 0]], ![![1436, -17068, 490, -2], ![3316, -39340, 195, 0]]]
  g := ![![![1, 0, 0, 0], ![-55, 97, 0, 0], ![-79, 0, 97, 0], ![-20, 0, 0, 97]], ![![-1, 1, 0, 0], ![23, -42, 1, 0], ![34, 0, -42, 1], ![-241, 332, 80, -41]]]
  hle1 := by decide
  hle2 := by decide

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0, 0], ![-25, 1, 0, 0]] i)))

def SI97N2: IdealEqSpanCertificate timesTableO I97N2
 ![![97, 0, 0, 0], ![-25, 1, 0, 0]] 
 ![![97, 0, 0, 0], ![72, 1, 0, 0], ![54, 0, 1, 0], ![89, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![97, 0, 0, 0], ![0, 97, 0, 0], ![0, 0, 97, 0], ![0, 0, 0, 97]], ![![-25, 1, 0, 0], ![0, -25, 1, 0], ![0, 0, -25, 1], ![383, 332, 80, -24]]]
  hmulB := by decide
  f := ![![![1951, -28, 14848, -594], ![7566, 194, 57618, 0]], ![![1426, -7, 11548, -462], ![5530, 194, 44814, 0]], ![![1082, -18, 8249, -330], ![4196, 98, 32010, 0]], ![![1787, -40, 13624, -545], ![6930, 122, 52866, 0]]]
  g := ![![![1, 0, 0, 0], ![-72, 97, 0, 0], ![-54, 0, 97, 0], ![-89, 0, 0, 97]], ![![-1, 1, 0, 0], ![18, -25, 1, 0], ![13, 0, -25, 1], ![-265, 332, 80, -24]]]
  hle1 := by decide
  hle2 := by decide

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulEqCertificate timesTableO (I97N0) I97N1
  ![![97, 0, 0, 0], ![-162, -67, -4, 1]] ![![97, 0, 0, 0], ![-42, 1, 0, 0]]
  ![![97, 0, 0, 0], ![5829, 3081, 181, -45]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![9409, 0, 0, 0], ![-4074, 97, 0, 0]], ![![-15714, -6499, -388, 97], ![7187, 2984, 181, -45]]]
 hmul := by decide
 f :=  ![![![![284291025494231412, -3536570622819255617, 97590606607785339, -322566099877454], ![656576177964820017, -8152161586720383366, 31288726512693219, 0]], ![![185175417884, 0, 0, 0], ![-4171, 0, 0, 0]]], ![![![17083871906781424968, -212522781556311590736, 5864502474863845613, -19383932089295915], ![39455566006330765683, -489887023583658504391, 1880230284933886907, 0]], ![![11127727700568, 0, 0, 0], ![-250647, 0, 0, 0]]]]
 g :=  ![![![![-5732, -3081, -181, 45], ![97, 0, 0, 0]], ![![-42, 1, 0, 0], ![0, 0, 0, 0]]], ![![![-162, -67, -4, 1], ![0, 0, 0, 0]], ![![-5815, -3082, -181, 45], ![98, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI97N1 : IdealMulEqCertificate timesTableO (I97N0*I97N1) I97N2
  ![![97, 0, 0, 0], ![5829, 3081, 181, -45]] ![![97, 0, 0, 0], ![-25, 1, 0, 0]]
  ![![97, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI97N0
 hI2 := rfl
 M :=  ![![![9409, 0, 0, 0], ![-2425, 97, 0, 0]], ![![565413, 298857, 17557, -4365], ![-162960, -86136, -5044, 1261]]]
 hmul := by decide
 f :=  ![![![![8763037463, 111097220, 192876238884, -7715788326], ![34000459450, 1791009042, 748431443322, 0]], ![![-540, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![97, 0, 0, 0]], ![![-25, 1, 0, 0]]], ![![![5829, 3081, 181, -45]], ![![-1680, -888, -52, 13]]]]
 hle1 := by decide
 hle2 := by decide

def PBC97 : IsPrimesAboveP 97 ![I97N0, I97N1, I97N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI97N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}
def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate timesTableO I101N0
 ![![101, 0, 0, 0]] 
 ![![101, 0, 0, 0], ![0, 101, 0, 0], ![0, 0, 101, 0], ![0, 0, 0, 101]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![101, 0, 0, 0], ![0, 101, 0, 0], ![0, 0, 101, 0], ![0, 0, 0, 101]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 104060401 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI101N0)

def MemCI101N0 : IdealMemCertificate B I101N0
  ![![101, 0, 0, 0], ![0, 101, 0, 0], ![0, 0, 101, 0], ![0, 0, 0, 101]] ![27930885117, 18652113693, 2084033394, -354231644] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI101N0
 g := ![276543417, 184674393, 20633994, -3507244]
 hmem := by decide

def P101P0 : CertificateIrreducibleZModOfList' 101 4 2 6 [89, 21, 72, 91, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 80, 85, 41], [81, 16, 51, 87], [13, 4, 66, 74], [0, 1]]
 g := ![![[94, 99, 9, 80], [99, 64, 64], [29, 38, 79, 100], [29, 66, 17], [28, 10, 1], []],![[42, 88, 7, 54, 80, 2], [92, 30, 30], [73, 99, 5, 39, 35, 32], [91, 93, 16], [14, 64, 45], [27, 20, 87, 12, 98, 39]],![[72, 91, 66, 91, 30, 54], [82, 31, 68], [98, 59, 75, 49, 28, 58], [64, 65, 49], [15, 82, 49], [62, 78, 84, 95, 23, 84]],![[11, 51, 23, 78, 28, 8], [17, 81, 87], [21, 72, 8, 69, 5, 38], [97, 10, 65], [23, 88, 47], [60, 12, 26, 81, 32, 12]]]
 h' := ![![[17, 80, 85, 41], [82, 7, 57, 79], [45, 73, 36, 93], [23, 100, 41, 91], [33, 37, 8, 44], [0, 0, 0, 1], [0, 1]],![[81, 16, 51, 87], [47, 52, 11, 80], [85, 25, 31, 38], [1, 62, 81, 17], [90, 85, 80, 4], [86, 50, 27, 34], [17, 80, 85, 41]],![[13, 4, 66, 74], [54, 33, 63, 96], [79, 3, 91, 88], [75, 65, 50, 88], [32, 84, 52, 94], [16, 48, 43, 7], [81, 16, 51, 87]],![[0, 1], [70, 9, 71, 48], [13, 0, 44, 84], [6, 76, 30, 6], [16, 97, 62, 60], [89, 3, 31, 59], [13, 4, 66, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [98, 73, 88], []]
 b := ![[], [], [27, 44, 24, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal O 101 where 
  r := 4
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I101N0
  hcard := NI101N0
  P := [89, 21, 72, 91, 1]
  f := ofList [89, 21, 72, 91, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P101P0
  hneq := by decide
  hlen := by decide
  c := ![27930885117, 18652113693, 2084033394, -354231644]
  a := ![-10, 2, 13, -1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI101N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI101N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal.isPrime PI101N0
def PBC101 : IsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I101N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}
def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0], ![-97, -67, -4, 1]] i)))

def SI103N0: IdealEqSpanCertificate timesTableO I103N0
 ![![103, 0, 0, 0], ![-97, -67, -4, 1]] 
 ![![103, 0, 0, 0], ![0, 103, 0, 0], ![92, 34, 1, 0], ![65, 69, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![103, 0, 0, 0], ![0, 103, 0, 0], ![0, 0, 103, 0], ![0, 0, 0, 103]], ![![-97, -67, -4, 1], ![383, 235, 13, -3], ![-1149, -613, -5, 10], ![3830, 2171, 187, 5]]]
  hmulB := by decide
  f := ![![![35453, 18460, 892, -172], ![-45320, -21012, 0, 0]], ![![-5844, -3031, -146, 28], ![7622, 3502, 0, 0]], ![![29700, 15462, 747, -144], ![-38004, -17612, 0, 0]], ![![18480, 9634, 466, -90], ![-23471, -10914, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-92, -34, 103, 0], ![-65, -69, 0, 103]], ![![2, 0, -4, 1], ![-6, 0, 13, -3], ![-13, -11, -5, 10], ![-133, -44, 187, 5]]]
  hle1 := by decide
  hle2 := by decide

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI103N0)

def MemCI103N0 : IdealMemCertificate B I103N0
  ![![103, 0, 0, 0], ![0, 103, 0, 0], ![92, 34, 1, 0], ![65, 69, 0, 1]] ![31370, 26867, 6586, 358] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI103N0
 g := ![-5804, -2153, 6586, 358]
 hmem := by decide

def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [51, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 102], [0, 1]]
 g := ![![[39, 100], [16, 64], [51, 23], [97], [56], [71, 1]],![[32, 3], [28, 39], [36, 80], [97], [56], [39, 102]]]
 h' := ![![[71, 102], [8, 93], [77, 95], [4, 34], [78, 32], [87, 46], [0, 1]],![[0, 1], [19, 10], [24, 8], [49, 69], [84, 71], [57, 57], [71, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [8, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal O 103 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I103N0
  hcard := NI103N0
  P := [51, 32, 1]
  f := ofList [51, 32, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P103P0
  hneq := by decide
  hlen := by decide
  c := ![31370, 26867, 6586, 358]
  a := ![-3, 1, -1, 1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI103N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI103N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal.isPrime PI103N0
def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0, 0], ![-166, -67, -4, 1]] i)))

def SI103N1: IdealEqSpanCertificate timesTableO I103N1
 ![![103, 0, 0, 0], ![-166, -67, -4, 1]] 
 ![![103, 0, 0, 0], ![0, 103, 0, 0], ![91, 68, 1, 0], ![95, 102, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![103, 0, 0, 0], ![0, 103, 0, 0], ![0, 0, 103, 0], ![0, 0, 0, 103]], ![![-166, -67, -4, 1], ![383, 166, 13, -3], ![-1149, -613, -74, 10], ![3830, 2171, 187, -64]]]
  hmulB := by decide
  f := ![![![652794, 344311, 42433, -8838], ![-1277715, -729343, 0, 0]], ![![-8931, -4711, -581, 121], ![17510, 9991, 0, 0]], ![![570936, 301124, 37108, -7729], ![-1117238, -637775, 0, 0]], ![![593294, 312922, 38563, -8032], ![-1161106, -662801, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-91, -68, 103, 0], ![-95, -102, 0, 103]], ![![1, 1, -4, 1], ![-5, -4, 13, -3], ![45, 33, -74, 10], ![-69, -39, 187, -64]]]
  hle1 := by decide
  hle2 := by decide

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 10609 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI103N1)

def MemCI103N1 : IdealMemCertificate B I103N1
  ![![103, 0, 0, 0], ![0, 103, 0, 0], ![91, 68, 1, 0], ![95, 102, 0, 1]] ![493788, 412628, 96038, 3361] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI103N1
 g := ![-83155, -62726, 96038, 3361]
 hmem := by decide

def P103P1 : CertificateIrreducibleZModOfList' 103 2 2 6 [80, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [99, 102], [0, 1]]
 g := ![![[67, 33], [100, 83], [25, 63], [8], [79], [99, 1]],![[38, 70], [77, 20], [82, 40], [8], [79], [95, 102]]]
 h' := ![![[99, 102], [34, 62], [60, 86], [30, 75], [84, 27], [11, 39], [0, 1]],![[0, 1], [95, 41], [25, 17], [39, 28], [79, 76], [61, 64], [99, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [61, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N1 : CertifiedPrimeIdeal O 103 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I103N1
  hcard := NI103N1
  P := [80, 4, 1]
  f := ofList [80, 4, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P103P1
  hneq := by decide
  hlen := by decide
  c := ![493788, 412628, 96038, 3361]
  a := ![3, 0, 7, -4]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI103N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI103N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := CertifiedPrimeIdeal.isPrime PI103N1
def MulI103N0 : IdealMulEqCertificate timesTableO (I103N0) I103N1
  ![![103, 0, 0, 0], ![-97, -67, -4, 1]] ![![103, 0, 0, 0], ![-166, -67, -4, 1]]
  ![![103, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![10609, 0, 0, 0], ![-17098, -6901, -412, 103]], ![![-9991, -6901, -412, 103], ![-1133, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![3524087373511, 1858771343333, 229079032859, -47712741514], ![-6898060319130, -3937490880709, 0, 0]], ![![52945, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![103, 0, 0, 0]], ![![-166, -67, -4, 1]]], ![![![-97, -67, -4, 1]], ![![-11, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC103 : IsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI103N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}
def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate timesTableO I107N0
 ![![107, 0, 0, 0]] 
 ![![107, 0, 0, 0], ![0, 107, 0, 0], ![0, 0, 107, 0], ![0, 0, 0, 107]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![107, 0, 0, 0], ![0, 107, 0, 0], ![0, 0, 107, 0], ![0, 0, 0, 107]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 131079601 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI107N0)

def MemCI107N0 : IdealMemCertificate B I107N0
  ![![107, 0, 0, 0], ![0, 107, 0, 0], ![0, 0, 107, 0], ![0, 0, 0, 107]] ![27466232641, 26190000413, 8032575386, 786879712] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI107N0
 g := ![256693763, 244766359, 75070798, 7354016]
 hmem := by decide

def P107P0 : CertificateIrreducibleZModOfList' 107 4 2 6 [58, 66, 77, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [102, 55, 58, 15], [24, 26, 63, 106], [83, 25, 93, 93], [0, 1]]
 g := ![![[13, 66, 87, 92], [47, 63, 11, 99], [59, 4, 41], [19, 88, 26, 10], [55, 102, 1], []],![[33, 61, 39, 4, 87, 45], [89, 104, 96, 72, 57, 78], [52, 18, 12], [28, 101, 89, 54, 21, 51], [33, 21, 90], [4, 99, 16, 11, 19, 58]],![[39, 46, 57, 64, 94, 78], [45, 86, 43, 4, 93, 78], [31, 81, 89], [88, 14, 15, 65, 19, 95], [36, 24, 102], [63, 52, 22, 11, 87, 106]],![[59, 67, 37, 56, 9, 78], [85, 3, 35, 89, 55, 5], [83, 47, 34], [50, 7, 45, 66, 80, 72], [55, 104, 30], [77, 12, 23, 70, 31, 38]]]
 h' := ![![[102, 55, 58, 15], [56, 102, 33, 78], [63, 11, 99, 62], [75, 34, 38, 83], [20, 84, 103, 44], [0, 0, 0, 1], [0, 1]],![[24, 26, 63, 106], [74, 82, 58, 89], [80, 35, 58, 35], [97, 58, 10, 36], [24, 105, 49, 14], [71, 45, 104, 82], [102, 55, 58, 15]],![[83, 25, 93, 93], [86, 26, 16, 52], [24, 40, 20, 55], [18, 22, 57, 14], [77, 21, 35, 71], [5, 90, 103, 67], [24, 26, 63, 106]],![[0, 1], [3, 4, 0, 102], [2, 21, 37, 62], [1, 100, 2, 81], [69, 4, 27, 85], [7, 79, 7, 64], [83, 25, 93, 93]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [22, 21, 72], []]
 b := ![[], [], [94, 94, 102, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal O 107 where 
  r := 4
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I107N0
  hcard := NI107N0
  P := [58, 66, 77, 5, 1]
  f := ofList [58, 66, 77, 5, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P107P0
  hneq := by decide
  hlen := by decide
  c := ![27466232641, 26190000413, 8032575386, 786879712]
  a := ![0, 1, 1, -1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI107N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI107N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal.isPrime PI107N0
def PBC107 : IsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I107N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}
def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate timesTableO I109N0
 ![![109, 0, 0, 0]] 
 ![![109, 0, 0, 0], ![0, 109, 0, 0], ![0, 0, 109, 0], ![0, 0, 0, 109]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![109, 0, 0, 0], ![0, 109, 0, 0], ![0, 0, 109, 0], ![0, 0, 0, 109]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 141158161 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI109N0)

def MemCI109N0 : IdealMemCertificate B I109N0
  ![![109, 0, 0, 0], ![0, 109, 0, 0], ![0, 0, 109, 0], ![0, 0, 0, 109]] ![940698994, 888653347, 268697208, 25718114] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI109N0
 g := ![8630266, 8152783, 2465112, 235946]
 hmem := by decide

def P109P0 : CertificateIrreducibleZModOfList' 109 4 2 6 [64, 78, 79, 11, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 31, 43, 47], [51, 6, 54, 100], [11, 71, 12, 71], [0, 1]]
 g := ![![[88, 58, 72, 81], [62, 34, 87], [97, 42, 87, 75], [63, 73, 106, 4], [42, 98, 1], []],![[48, 14, 67, 99, 105, 103], [46, 15, 108], [21, 44, 55, 79, 53, 91], [26, 78, 29, 11, 15, 33], [33, 106, 31], [32, 33, 8, 25, 84, 55]],![[45, 23, 45, 30, 8, 36], [75, 11, 16], [78, 33, 3, 97, 22, 93], [2, 3, 24, 85, 96, 88], [55, 83, 3], [49, 74, 99, 101, 104, 34]],![[57, 12, 76, 63, 92, 5], [56, 9, 93], [55, 92, 68, 93, 20, 49], [66, 61, 70, 65, 70, 87], [69, 73, 61], [7, 5, 93, 79, 50, 64]]]
 h' := ![![[36, 31, 43, 47], [90, 3, 108, 9], [5, 102, 86, 14], [1, 67, 80, 82], [37, 44, 92, 2], [0, 0, 0, 1], [0, 1]],![[51, 6, 54, 100], [88, 95, 60, 52], [78, 64, 66, 76], [58, 60, 74, 68], [34, 44, 61, 37], [27, 53, 52, 85], [36, 31, 43, 47]],![[11, 71, 12, 71], [41, 84, 96, 66], [46, 84, 72, 105], [92, 66, 74, 74], [61, 36, 58, 82], [23, 1, 70, 60], [51, 6, 54, 100]],![[0, 1], [40, 36, 63, 91], [38, 77, 103, 23], [68, 25, 99, 103], [65, 94, 7, 97], [11, 55, 96, 72], [11, 71, 12, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [58, 70, 14], []]
 b := ![[], [], [17, 12, 10, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal O 109 where 
  r := 4
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I109N0
  hcard := NI109N0
  P := [64, 78, 79, 11, 1]
  f := ofList [64, 78, 79, 11, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P109P0
  hneq := by decide
  hlen := by decide
  c := ![940698994, 888653347, 268697208, 25718114]
  a := ![-1, 3, 4, 0]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI109N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI109N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal.isPrime PI109N0
def PBC109 : IsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I109N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}
def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate timesTableO I113N0
 ![![113, 0, 0, 0]] 
 ![![113, 0, 0, 0], ![0, 113, 0, 0], ![0, 0, 113, 0], ![0, 0, 0, 113]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![113, 0, 0, 0], ![0, 113, 0, 0], ![0, 0, 113, 0], ![0, 0, 0, 113]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 163047361 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI113N0)

def MemCI113N0 : IdealMemCertificate B I113N0
  ![![113, 0, 0, 0], ![0, 113, 0, 0], ![0, 0, 113, 0], ![0, 0, 0, 113]] ![100141033969720, 95694487429328, 29441553446106, 2897707037204] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI113N0
 g := ![886203840440, 846853871056, 260544720762, 25643425108]
 hmem := by decide

def P113P0 : CertificateIrreducibleZModOfList' 113 4 2 6 [27, 11, 32, 45, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 67, 80, 28], [49, 74, 108, 50], [94, 84, 38, 35], [0, 1]]
 g := ![![[53, 41, 55, 102], [39, 17, 99], [89, 96, 63], [88, 62, 36], [110, 72, 68, 1], []],![[43, 82, 46, 77], [36, 55, 77], [3, 14, 1], [37, 69, 22], [73, 57, 49, 73, 24, 64], [112, 60, 38, 24, 21, 30]],![[78, 85, 47, 29, 57, 88], [81, 47, 49], [66, 74, 52], [98, 112, 18], [58, 108, 89, 34, 28, 1], [43, 64, 40, 38, 43, 22]],![[72, 65, 51, 64, 0, 6], [43, 97, 85], [81, 45, 102], [64, 20, 97], [99, 64, 62, 29, 76, 43], [2, 28, 78, 43, 82, 48]]]
 h' := ![![[38, 67, 80, 28], [47, 102, 32, 92], [99, 5, 75, 72], [4, 108, 43, 17], [81, 10, 67, 107], [0, 0, 0, 1], [0, 1]],![[49, 74, 108, 50], [63, 73, 12], [73, 1, 7, 90], [43, 81, 86, 1], [108, 70, 13, 19], [94, 33, 112, 99], [38, 67, 80, 28]],![[94, 84, 38, 35], [11, 73, 107, 100], [86, 57, 64, 7], [25, 85, 27, 74], [80, 41, 20, 40], [98, 60, 109, 39], [49, 74, 108, 50]],![[0, 1], [38, 91, 75, 34], [42, 50, 80, 57], [67, 65, 70, 21], [10, 105, 13, 60], [93, 20, 5, 87], [94, 84, 38, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [104, 49, 39], []]
 b := ![[], [], [88, 63, 73, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal O 113 where 
  r := 4
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I113N0
  hcard := NI113N0
  P := [27, 11, 32, 45, 1]
  f := ofList [27, 11, 32, 45, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P113P0
  hneq := by decide
  hlen := by decide
  c := ![100141033969720, 95694487429328, 29441553446106, 2897707037204]
  a := ![-1, 1, 0, 7]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI113N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI113N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal.isPrime PI113N0
def PBC113 : IsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I113N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl

