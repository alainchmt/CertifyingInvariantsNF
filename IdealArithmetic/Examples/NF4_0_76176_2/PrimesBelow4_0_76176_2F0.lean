
import IdealArithmetic.Examples.NF4_0_76176_2.RI4_0_76176_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0], ![-1, 1, 0, -1]] i)))

def SI2N0: IdealEqSpanCertificate timesTableO I2N0
 ![![2, 0, 0, 0], ![-1, 1, 0, -1]] 
 ![![2, 0, 0, 0], ![1, 1, 0, 0], ![1, 0, 1, 0], ![0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![2, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 2]], ![![-1, 1, 0, -1], ![-6, 7, 9, -18], ![36, 3, 7, -9], ![16, 4, 6, -9]]]
  hmulB := by decide
  f := ![![![174, -134, 7, 128], ![274, 0, -2, 0]], ![![86, -66, -1, 69], ![129, 1, -1, 0]], ![![88, -68, 4, 65], ![139, 0, -1, 0]], ![![-84, 64, -8, -55], ![-138, 1, 1, 0]]]
  g := ![![![1, 0, 0, 0], ![-1, 2, 0, 0], ![-1, 0, 2, 0], ![0, 0, 0, 2]], ![![-1, 1, 0, -1], ![-11, 7, 9, -18], ![13, 3, 7, -9], ![3, 4, 6, -9]]]
  hle1 := by decide
  hle2 := by decide

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0], ![0, 0, -1, 1]] i)))

def SI2N1: IdealEqSpanCertificate timesTableO I2N1
 ![![2, 0, 0, 0], ![0, 0, -1, 1]] 
 ![![2, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![2, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 2]], ![![0, 0, -1, 1], ![-10, 7, 8, -17], ![26, 6, 15, -26], ![10, 6, 10, -18]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0], ![0, 0, 0, 0]], ![![-22, 28, 18, -55], ![-35, -7, -1, 0]], ![![-17, 24, 16, -48], ![-32, -6, -1, 0]], ![![-13, -3, -30, 36], ![-45, 0, 1, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 2]], ![![0, 0, -1, 1], ![-5, 7, 8, -17], ![13, 6, 15, -26], ![5, 6, 10, -18]]]
  hle1 := by decide
  hle2 := by decide

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulEqCertificate timesTableO (I2N0) I2N0
  ![![2, 0, 0, 0], ![-1, 1, 0, -1]] ![![2, 0, 0, 0], ![-1, 1, 0, -1]]
  ![![2, 0, 0, 0], ![-1, 0, 1, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0], ![-2, 2, 0, -2]], ![![-2, 2, 0, -2], ![-21, 2, 3, -8]]]
 hmul := by decide
 f :=  ![![![![9278892, -8304264, 304341, 7992266], ![16956866, -28843, -49128, 0]], ![![0, 0, 0, 0], ![488, -648, -9, 0]]], ![![![-6161996, 5514757, -202118, -5307554], ![-11260859, 19157, 32625, 0]], ![![0, 0, 0, 0], ![-325, 430, 6, 0]]]]
 g :=  ![![![![2, 0, 0, 0], ![0, 0, 0, 0]], ![![-4, 1, -1, 2], ![2, 2, 0, 0]]], ![![![-4, 1, -1, 2], ![2, 2, 0, 0]], ![![-23, 1, -2, 7], ![7, 8, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI2N1 : IdealMulEqCertificate timesTableO (I2N0*I2N0) I2N1
  ![![2, 0, 0, 0], ![-1, 0, 1, -2]] ![![2, 0, 0, 0], ![0, 0, -1, 1]]
  ![![2, 0, 0, 0], ![-2, 0, 0, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI2N0
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0], ![0, 0, -2, 2]], ![![-2, 0, 2, -4], ![6, -6, -4, 9]]]
 hmul := by decide
 f :=  ![![![![157, -1, 696, -710], ![1320, 8, -9, 0]], ![![-1, 0, 0, 0], ![0, 0, 0, 0]]], ![![![-93, -6, -428, 448], ![-788, -3, 6, 0]], ![![4, 0, 0, 0], ![1, 0, 0, 0]]]]
 g :=  ![![![![2, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, -1, 1], ![0, 0, 0, 0]]], ![![![1, 0, 1, -1], ![2, 0, 0, 0]], ![![2, -3, -2, 4], ![-1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI2N2 : IdealMulEqCertificate timesTableO (I2N0*I2N0*I2N1) I2N1
  ![![2, 0, 0, 0], ![-2, 0, 0, -1]] ![![2, 0, 0, 0], ![0, 0, -1, 1]]
  ![![2, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI2N1
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0], ![0, 0, -2, 2]], ![![-4, 0, 0, -2], ![-10, -6, -8, 16]]]
 hmul := by decide
 f :=  ![![![![2268, 56, 10528, -10822], ![19827, 101, -135, 0]], ![![0, 0, 0, 0], ![3, 0, 0, 0]]]]
 g :=  ![![![![2, 0, 0, 0]], ![![0, 0, -1, 1]]], ![![![-2, 0, 0, -1]], ![![-5, -3, -4, 8]]]]
 hle1 := by decide
 hle2 := by decide

def PBC2 : IsPrimesAboveP 2 ![I2N0, I2N0, I2N1, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI2N2, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0], ![2, -1, -2, 4]] i)))

def SI3N0: IdealEqSpanCertificate timesTableO I3N0
 ![![3, 0, 0, 0], ![2, -1, -2, 4]] 
 ![![3, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![2, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, 0, 0, 0], ![0, 3, 0, 0], ![0, 0, 3, 0], ![0, 0, 0, 3]], ![![2, -1, -2, 4], ![-8, 0, -1, 2], ![-4, -9, 0, 1], ![-6, -4, 0, 0]]]
  hmulB := by decide
  f := ![![![-61, 17, -11, 20], ![-3, -27, 6, 0]], ![![-4, 1, 1, -2], ![2, -1, 0, 0]], ![![10, -2, 4, -7], ![3, 5, -1, 0]], ![![-40, 11, -8, 15], ![-3, -18, 4, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 3, 0, 0], ![0, 0, 3, 0], ![-2, 0, 0, 3]], ![![-2, -1, -2, 4], ![-4, 0, -1, 2], ![-2, -9, 0, 1], ![-2, -4, 0, 0]]]
  hle1 := by decide
  hle2 := by decide

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0], ![-1, 0, -2, 3]] i)))

def SI3N1: IdealEqSpanCertificate timesTableO I3N1
 ![![3, 0, 0, 0], ![-1, 0, -2, 3]] 
 ![![3, 0, 0, 0], ![2, 1, 0, 0], ![2, 0, 1, 0], ![1, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, 0, 0, 0], ![0, 3, 0, 0], ![0, 0, 3, 0], ![0, 0, 0, 3]], ![![-1, 0, -2, 3], ![-14, 5, 8, -16], ![32, -6, 5, -8], ![10, 0, 6, -11]]]
  hmulB := by decide
  f := ![![![254, -72, -44, 113], ![63, 36, -6, 0]], ![![164, -46, -28, 72], ![40, 23, -4, 0]], ![![127, -36, -22, 57], ![31, 18, -3, 0]], ![![85, -24, -14, 37], ![22, 12, -2, 0]]]
  g := ![![![1, 0, 0, 0], ![-2, 3, 0, 0], ![-2, 0, 3, 0], ![-1, 0, 0, 3]], ![![0, 0, -2, 3], ![-8, 5, 8, -16], ![14, -6, 5, -8], ![3, 0, 6, -11]]]
  hle1 := by decide
  hle2 := by decide

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulEqCertificate timesTableO (I3N0) I3N0
  ![![3, 0, 0, 0], ![2, -1, -2, 4]] ![![3, 0, 0, 0], ![2, -1, -2, 4]]
  ![![3, 0, 0, 0], ![-1, 0, 1, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![9, 0, 0, 0], ![6, -3, -6, 12]], ![![6, -3, -6, 12], ![-4, 0, -3, 4]]]
 hmul := by decide
 f :=  ![![![![236011, -68876, 49169, -92482], ![24216, 109701, -25740, 0]], ![![0, 0, 0, 0], ![-12122, -272, -8, 0]]], ![![![1895, -553, 397, -747], ![198, 882, -207, 0]], ![![0, 0, 0, 0], ![-98, -2, 0, 0]]]]
 g :=  ![![![![26, 0, 1, -8], ![-3, -18, 0, 0]], ![![25, -1, -1, -4], ![-3, -18, 0, 0]]], ![![![25, -1, -1, -4], ![-3, -18, 0, 0]], ![![-7, 0, -2, 5], ![3, 5, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI3N1 : IdealMulEqCertificate timesTableO (I3N0*I3N0) I3N1
  ![![3, 0, 0, 0], ![-1, 0, 1, -2]] ![![3, 0, 0, 0], ![-1, 0, -2, 3]]
  ![![3, 0, 0, 0], ![-1, 0, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI3N0
 hI2 := rfl
 M :=  ![![![9, 0, 0, 0], ![-3, 0, -6, 9]], ![![-3, 0, 3, -6], ![13, -6, -5, 11]]]
 hmul := by decide
 f :=  ![![![![-14452, 4104, 2600, -6599], ![-3511, -2052, 344, 0]], ![![-136, 0, 0, 0], ![-6, 0, 0, 0]]], ![![![4157, -1180, -746, 1895], ![1012, 590, -99, 0]], ![![40, 0, 0, 0], ![2, 0, 0, 0]]]]
 g :=  ![![![![3, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, -1, 2], ![3, 0, 0, 0]]], ![![![-1, 0, 1, -2], ![0, 0, 0, 0]], ![![5, -2, -1, 3], ![2, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI3N2 : IdealMulEqCertificate timesTableO (I3N0*I3N0*I3N1) I3N1
  ![![3, 0, 0, 0], ![-1, 0, -1, 1]] ![![3, 0, 0, 0], ![-1, 0, -2, 3]]
  ![![3, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI3N1
 hI2 := rfl
 M :=  ![![![9, 0, 0, 0], ![-3, 0, -6, 9]], ![![-3, 0, -3, 3], ![-21, 6, 3, -6]]]
 hmul := by decide
 f :=  ![![![![-5067, 1448, 914, -2318], ![-1234, -724, 118, 0]], ![![0, 0, 0, 0], ![-8, 0, 0, 0]]]]
 g :=  ![![![![3, 0, 0, 0]], ![![-1, 0, -2, 3]]], ![![![-1, 0, -1, 1]], ![![-7, 2, 1, -2]]]]
 hle1 := by decide
 hle2 := by decide

def PBC3 : IsPrimesAboveP 3 ![I3N0, I3N0, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI3N2, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0], ![-2, -1, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate timesTableO I5N0
 ![![5, 0, 0, 0], ![-2, -1, 0, 0]] 
 ![![5, 0, 0, 0], ![2, 1, 0, 0], ![1, 0, 1, 0], ![0, 0, 0, 5]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![5, 0, 0, 0], ![0, 5, 0, 0], ![0, 0, 5, 0], ![0, 0, 0, 5]], ![![-2, -1, 0, 0], ![0, -2, -1, 0], ![-16, 15, 14, -35], ![-6, 8, 8, -20]]]
  hmulB := by decide
  f := ![![![7, 5, 1, 0], ![15, 5, 0, 0]], ![![2, 3, 1, 0], ![4, 5, 0, 0]], ![![3, 3, 1, 0], ![7, 4, 0, 0]], ![![0, 0, 0, 1], ![0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![-2, 5, 0, 0], ![-1, 0, 5, 0], ![0, 0, 0, 1]], ![![0, -1, 0, 0], ![1, -2, -1, 0], ![-12, 15, 14, -7], ![-6, 8, 8, -4]]]
  hle1 := by decide
  hle2 := by decide

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI5N0)

def MemCI5N0 : IdealMemCertificate B I5N0
  ![![5, 0, 0, 0], ![2, 1, 0, 0], ![1, 0, 1, 0], ![0, 0, 0, 5]] ![-215071, -100524, -162518, 287820] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI5N0
 g := ![29699, -100524, -162518, 57564]
 hmem := by decide

def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [3, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 4], [0, 1]]
 g := ![![[4, 4], [1]],![[1, 1], [1]]]
 h' := ![![[3, 4], [2, 3], [0, 1]],![[0, 1], [1, 2], [3, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [4, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal O 5 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I5N0
  hcard := NI5N0
  P := [3, 2, 1]
  f := ofList [3, 2, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P5P0
  hneq := by decide
  hlen := by decide
  c := ![-215071, -100524, -162518, 287820]
  a := ![-6, 8, -60, -13]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI5N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI5N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal.isPrime PI5N0
def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0], ![-4, 1, 2, -4]] i)))

def SI5N1: IdealEqSpanCertificate timesTableO I5N1
 ![![5, 0, 0, 0], ![-4, 1, 2, -4]] 
 ![![5, 0, 0, 0], ![0, 5, 0, 0], ![2, 4, 1, 0], ![2, 3, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![5, 0, 0, 0], ![0, 5, 0, 0], ![0, 0, 5, 0], ![0, 0, 0, 5]], ![![-4, 1, 2, -4], ![8, -2, 1, -2], ![4, 9, -2, -1], ![6, 4, 0, -2]]]
  hmulB := by decide
  f := ![![![-13, -13, -2, 10], ![5, 0, 0, 15]], ![![18, 13, 0, -6], ![0, 0, 0, -15]], ![![10, 5, -1, 0], ![3, 0, 0, -6]], ![![4, 3, 0, -1], ![0, 0, 0, -3]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-2, -4, 5, 0], ![-2, -3, 0, 5]], ![![0, 1, 2, -4], ![2, 0, 1, -2], ![2, 4, -2, -1], ![2, 2, 0, -2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 25 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI5N1)

def MemCI5N1 : IdealMemCertificate B I5N1
  ![![5, 0, 0, 0], ![0, 5, 0, 0], ![2, 4, 1, 0], ![2, 3, 0, 1]] ![367, 672, 2684, -7123] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI5N1
 g := ![1849, 2261, 2684, -7123]
 hmem := by decide

def P5P1 : CertificateIrreducibleZModOfList' 5 2 2 2 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 4], [0, 1]]
 g := ![![[1, 1], [1]],![[0, 4], [1]]]
 h' := ![![[4, 4], [4, 4], [0, 1]],![[0, 1], [0, 1], [4, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [2, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N1 : CertifiedPrimeIdeal O 5 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I5N1
  hcard := NI5N1
  P := [1, 1, 1]
  f := ofList [1, 1, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P5P1
  hneq := by decide
  hlen := by decide
  c := ![367, 672, 2684, -7123]
  a := ![-59, 56, 59, -129]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI5N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI5N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := CertifiedPrimeIdeal.isPrime PI5N1
def MulI5N0 : IdealMulEqCertificate timesTableO (I5N0) I5N1
  ![![5, 0, 0, 0], ![-2, -1, 0, 0]] ![![5, 0, 0, 0], ![-4, 1, 2, -4]]
  ![![5, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![25, 0, 0, 0], ![-20, 5, 10, -20]], ![![-10, -5, 0, 0], ![0, 0, -5, 10]]]
 hmul := by decide
 f :=  ![![![![215, 173, 16, -114], ![-39, 0, 0, -207]], ![![-6, 2, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![5, 0, 0, 0]], ![![-4, 1, 2, -4]]], ![![![-2, -1, 0, 0]], ![![0, 0, -1, 2]]]]
 hle1 := by decide
 hle2 := by decide

def PBC5 : IsPrimesAboveP 5 ![I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI5N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0], ![-5, 1, 2, -4]] i)))

def SI7N0: IdealEqSpanCertificate timesTableO I7N0
 ![![7, 0, 0, 0], ![-5, 1, 2, -4]] 
 ![![7, 0, 0, 0], ![0, 7, 0, 0], ![4, 6, 1, 0], ![5, 1, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![7, 0, 0, 0], ![0, 7, 0, 0], ![0, 0, 7, 0], ![0, 0, 0, 7]], ![![-5, 1, 2, -4], ![8, -3, 1, -2], ![4, 9, -3, -1], ![6, 4, 0, -3]]]
  hmulB := by decide
  f := ![![![25, 16, 0, -12], ![0, 0, 0, -28]], ![![-1, -4, -2, 7], ![7, 0, 0, 7]], ![![12, 6, -1, -2], ![4, 0, 0, -10]], ![![17, 11, 0, -8], ![0, 0, 0, -19]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-4, -6, 7, 0], ![-5, -1, 0, 7]], ![![1, -1, 2, -4], ![2, -1, 1, -2], ![3, 4, -3, -1], ![3, 1, 0, -3]]]
  hle1 := by decide
  hle2 := by decide

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI7N0)

def MemCI7N0 : IdealMemCertificate B I7N0
  ![![7, 0, 0, 0], ![0, 7, 0, 0], ![4, 6, 1, 0], ![5, 1, 0, 1]] ![578, -8, 22, -105] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI7N0
 g := ![145, -5, 22, -105]
 hmem := by decide

def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [2, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 6], [0, 1]]
 g := ![![[6, 4], [2, 1]],![[0, 3], [4, 6]]]
 h' := ![![[2, 6], [3, 2], [0, 1]],![[0, 1], [0, 5], [2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [3, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal O 7 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I7N0
  hcard := NI7N0
  P := [2, 5, 1]
  f := ofList [2, 5, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P0
  hneq := by decide
  hlen := by decide
  c := ![578, -8, 22, -105]
  a := ![16, -16, -17, 35]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI7N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI7N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal.isPrime PI7N0
def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0], ![-3, -1, 0, 0]] i)))

def SI7N1: IdealEqSpanCertificate timesTableO I7N1
 ![![7, 0, 0, 0], ![-3, -1, 0, 0]] 
 ![![7, 0, 0, 0], ![3, 1, 0, 0], ![5, 0, 1, 0], ![0, 0, 0, 7]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![7, 0, 0, 0], ![0, 7, 0, 0], ![0, 0, 7, 0], ![0, 0, 0, 7]], ![![-3, -1, 0, 0], ![0, -3, -1, 0], ![-16, 15, 13, -35], ![-6, 8, 8, -21]]]
  hmulB := by decide
  f := ![![![10, 6, 1, 0], ![21, 7, 0, 0]], ![![6, 5, 1, 0], ![13, 7, 0, 0]], ![![8, 5, 1, 0], ![17, 6, 0, 0]], ![![0, 0, 0, 1], ![0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![-3, 7, 0, 0], ![-5, 0, 7, 0], ![0, 0, 0, 1]], ![![0, -1, 0, 0], ![2, -3, -1, 0], ![-18, 15, 13, -5], ![-10, 8, 8, -3]]]
  hle1 := by decide
  hle2 := by decide

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI7N1)

def MemCI7N1 : IdealMemCertificate B I7N1
  ![![7, 0, 0, 0], ![3, 1, 0, 0], ![5, 0, 1, 0], ![0, 0, 0, 7]] ![-129678, -19788, 43207, -137060] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI7N1
 g := ![-40907, -19788, 43207, -19580]
 hmem := by decide

def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [3, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 6], [0, 1]]
 g := ![![[2, 4], [1, 1]],![[6, 3], [2, 6]]]
 h' := ![![[1, 6], [4, 5], [0, 1]],![[0, 1], [2, 2], [1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [5, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal O 7 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I7N1
  hcard := NI7N1
  P := [3, 6, 1]
  f := ofList [3, 6, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P1
  hneq := by decide
  hlen := by decide
  c := ![-129678, -19788, 43207, -137060]
  a := ![257, -234, -239, 561]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI7N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI7N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal.isPrime PI7N1
def MulI7N0 : IdealMulEqCertificate timesTableO (I7N0) I7N1
  ![![7, 0, 0, 0], ![-5, 1, 2, -4]] ![![7, 0, 0, 0], ![-3, -1, 0, 0]]
  ![![7, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![49, 0, 0, 0], ![-21, -7, 0, 0]], ![![-35, 7, 14, -28], ![7, 0, -7, 14]]]
 hmul := by decide
 f :=  ![![![![3950538, 1710218, 118057, 47005], ![9080671, 990987, 0, 0]], ![![82294, 0, 0, -47], ![0, 0, 0, 0]]]]
 g :=  ![![![![7, 0, 0, 0]], ![![-3, -1, 0, 0]]], ![![![-5, 1, 2, -4]], ![![1, 0, -1, 2]]]]
 hle1 := by decide
 hle2 := by decide

def PBC7 : IsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI7N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}
def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 2, 2, -4]] i)))

def SI11N0: IdealEqSpanCertificate timesTableO I11N0
 ![![-1, 2, 2, -4]] 
 ![![11, 0, 0, 0], ![0, 11, 0, 0], ![3, 0, 1, 0], ![10, 5, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![-1, 2, 2, -4], ![8, 1, 2, -2], ![20, -6, -15, 34], ![12, -4, -8, 19]]]
  hmulB := by decide
  f := ![![![-3, 2, 2, -4]], ![![8, -1, 2, -2]], ![![1, 0, -1, 2]], ![![2, 1, 2, -3]]]
  g := ![![![3, 2, 2, -4], ![2, 1, 2, -2], ![-25, -16, -15, 34], ![-14, -9, -8, 19]]]
  hle1 := by decide
  hle2 := by decide

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI11N0)

def MemCI11N0 : IdealMemCertificate B I11N0
  ![![11, 0, 0, 0], ![0, 11, 0, 0], ![3, 0, 1, 0], ![10, 5, 0, 1]] ![128, 0, 259, -726] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI11N0
 g := ![601, 330, 259, -726]
 hmem := by decide

def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [9, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 10], [0, 1]]
 g := ![![[9, 5], [8, 5], [1]],![[0, 6], [10, 6], [1]]]
 h' := ![![[7, 10], [5, 4], [2, 7], [0, 1]],![[0, 1], [0, 7], [7, 4], [7, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [9, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal O 11 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I11N0
  hcard := NI11N0
  P := [9, 4, 1]
  f := ofList [9, 4, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P0
  hneq := by decide
  hlen := by decide
  c := ![128, 0, 259, -726]
  a := ![21, -20, -21, 46]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI11N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI11N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal.isPrime PI11N0
def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -2, -2, 4]] i)))

def SI11N1: IdealEqSpanCertificate timesTableO I11N1
 ![![3, -2, -2, 4]] 
 ![![11, 0, 0, 0], ![0, 11, 0, 0], ![4, 9, 1, 0], ![0, 4, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, -2, -2, 4], ![-8, 1, -2, 2], ![-20, 6, 17, -34], ![-12, 4, 8, -17]]]
  hmulB := by decide
  f := ![![![1, -2, -2, 4]], ![![-8, -1, -2, 2]], ![![-8, -1, -1, 0]], ![![-4, 0, 0, -1]]]
  g := ![![![1, 0, -2, 4], ![0, 1, -2, 2], ![-8, -1, 17, -34], ![-4, 0, 8, -17]]]
  hle1 := by decide
  hle2 := by decide

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI11N1)

def MemCI11N1 : IdealMemCertificate B I11N1
  ![![11, 0, 0, 0], ![0, 11, 0, 0], ![4, 9, 1, 0], ![0, 4, 0, 1]] ![-4029, -936, -240, -420] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI11N1
 g := ![-279, 264, -240, -420]
 hmem := by decide

def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [10, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 10], [0, 1]]
 g := ![![[3, 1], [0, 9], [1]],![[6, 10], [5, 2], [1]]]
 h' := ![![[3, 10], [0, 10], [1, 3], [0, 1]],![[0, 1], [8, 1], [10, 8], [3, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [7, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal O 11 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I11N1
  hcard := NI11N1
  P := [10, 8, 1]
  f := ofList [10, 8, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P1
  hneq := by decide
  hlen := by decide
  c := ![-4029, -936, -240, -420]
  a := ![-23, 20, 18, -50]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI11N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI11N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal.isPrime PI11N1
def MulI11N0 : IdealMulEqCertificate timesTableO (I11N0) I11N1
  ![![-1, 2, 2, -4]] ![![3, -2, -2, 4]]
  ![![11, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![-11, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![-1, 0, 0, 0]]]]
 g :=  ![![![![-1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC11 : IsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI11N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}
def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![1, 1, 0, -1]] i)))

def SI13N0: IdealEqSpanCertificate timesTableO I13N0
 ![![13, 0, 0, 0], ![1, 1, 0, -1]] 
 ![![13, 0, 0, 0], ![4, 1, 0, 0], ![10, 0, 1, 0], ![3, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![1, 1, 0, -1], ![-6, 9, 9, -18], ![36, 3, 9, -9], ![16, 4, 6, -7]]]
  hmulB := by decide
  f := ![![![12516, -17605, -17784, 35419], ![-3107, 25818, -130, 0]], ![![9128, -12838, -12969, 25829], ![-2272, 18828, -95, 0]], ![![9148, -12867, -12998, 25887], ![-2274, 18870, -95, 0]], ![![2888, -4063, -4104, 8174], ![-713, 5958, -30, 0]]]
  g := ![![![1, 0, 0, 0], ![-4, 13, 0, 0], ![-10, 0, 13, 0], ![-3, 0, 0, 13]], ![![0, 1, 0, -1], ![-6, 9, 9, -18], ![-3, 3, 9, -9], ![-3, 4, 6, -7]]]
  hle1 := by decide
  hle2 := by decide

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0
def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![4, 1, 0, -1]] i)))

def SI13N1: IdealEqSpanCertificate timesTableO I13N1
 ![![13, 0, 0, 0], ![4, 1, 0, -1]] 
 ![![13, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![9, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![4, 1, 0, -1], ![-6, 12, 9, -18], ![36, 3, 12, -9], ![16, 4, 6, -4]]]
  hmulB := by decide
  f := ![![![434449, -847242, -636948, 1271910], ![-29328, 920348, -234, 0]], ![![83412, -162668, -122292, 244203], ![-5628, 176704, -45, 0]], ![![-16686, 32535, 24460, -48843], ![1134, -35343, 9, 0]], ![![300773, -586552, -440964, 880553], ![-20306, 637164, -162, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![-9, 0, 0, 13]], ![![1, 1, 0, -1], ![12, 12, 9, -18], ![9, 3, 12, -9], ![4, 4, 6, -4]]]
  hle1 := by decide
  hle2 := by decide

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![-5, 1, 0, -1]] i)))

def SI13N2: IdealEqSpanCertificate timesTableO I13N2
 ![![13, 0, 0, 0], ![-5, 1, 0, -1]] 
 ![![13, 0, 0, 0], ![12, 1, 0, 0], ![12, 0, 1, 0], ![4, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![-5, 1, 0, -1], ![-6, 3, 9, -18], ![36, 3, 3, -9], ![16, 4, 6, -13]]]
  hmulB := by decide
  f := ![![![92066, -53456, -175695, 346271], ![-66157, 253825, -130, 0]], ![![120292, -69844, -229557, 452426], ![-86434, 331639, -170, 0]], ![![77924, -45244, -148703, 293074], ![-55988, 214830, -110, 0]], ![![28328, -16448, -54060, 106545], ![-20356, 78100, -40, 0]]]
  g := ![![![1, 0, 0, 0], ![-12, 13, 0, 0], ![-12, 0, 13, 0], ![-4, 0, 0, 13]], ![![-1, 1, 0, -1], ![-6, 3, 9, -18], ![0, 3, 3, -9], ![-4, 4, 6, -13]]]
  hle1 := by decide
  hle2 := by decide

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def I13N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![-8, 1, 0, -1]] i)))

def SI13N3: IdealEqSpanCertificate timesTableO I13N3
 ![![13, 0, 0, 0], ![-8, 1, 0, -1]] 
 ![![13, 0, 0, 0], ![8, 1, 0, 0], ![1, 0, 1, 0], ![3, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![-8, 1, 0, -1], ![-6, 0, 9, -18], ![36, 3, 0, -9], ![16, 4, 6, -16]]]
  hmulB := by decide
  f := ![![![643697, 48298, -1539720, 3030782], ![-625534, 2224040, -780, 0]], ![![406020, 30464, -971190, 1911689], ![-394555, 1402830, -492, 0]], ![![39621, 2972, -94763, 186532], ![-38492, 136880, -48, 0]], ![![148551, 11145, -355320, 699412], ![-144345, 513240, -180, 0]]]
  g := ![![![1, 0, 0, 0], ![-8, 13, 0, 0], ![-1, 0, 13, 0], ![-3, 0, 0, 13]], ![![-1, 1, 0, -1], ![3, 0, 9, -18], ![3, 3, 0, -9], ![2, 4, 6, -16]]]
  hle1 := by decide
  hle2 := by decide

lemma NI13N3 : Nat.card (O ⧸ I13N3) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI13N3)

lemma isPrimeI13N3 : Ideal.IsPrime I13N3 := prime_ideal_of_norm_prime hp13.out _ NI13N3
def MulI13N0 : IdealMulEqCertificate timesTableO (I13N0) I13N1
  ![![13, 0, 0, 0], ![1, 1, 0, -1]] ![![13, 0, 0, 0], ![4, 1, 0, -1]]
  ![![-5, 1, 1, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![169, 0, 0, 0], ![52, 13, 0, -13]], ![![13, 13, 0, -13], ![-18, 9, 3, -15]]]
 hmul := by decide
 f :=  ![![![![943292410703355, -1841966225289687, -1385151582596888, 2765405776665242], ![-64169412241654, 2000819254016121, -33559364190, 0]], ![![-29051494, 0, 0, 0], ![-58615, -279, 0, 0]]]]
 g :=  ![![![![-39, -13, -13, 26]], ![![-10, -10, -9, 22]]], ![![![-1, -7, -6, 16]], ![![6, -3, -3, 9]]]]
 hle1 := by decide
 hle2 := by decide

def MulI13N1 : IdealMulEqCertificate timesTableO (I13N0*I13N1) I13N2
  ![![-5, 1, 1, -2]] ![![13, 0, 0, 0], ![-5, 1, 0, -1]]
  ![![13, 0, 0, 0], ![4, 5, 0, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI13N0
 hI2 := rfl
 M :=  ![![![-65, 13, 13, -26], ![23, -7, 0, 4]]]
 hmul := by decide
 f :=  ![![![![-4127513, 2406498, 7905188, -15581807], ![2971226, -11418624, 57, 0]]], ![![![-435472, 253898, 834041, -1643966], ![313490, -1204728, 6, 0]]]]
 g :=  ![![![![-5, 1, 1, -2], ![0, 0, 0, 0]], ![![-1, -4, 0, 1], ![9, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI13N2 : IdealMulEqCertificate timesTableO (I13N0*I13N1*I13N2) I13N3
  ![![13, 0, 0, 0], ![4, 5, 0, -1]] ![![13, 0, 0, 0], ![-8, 1, 0, -1]]
  ![![13, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI13N1
 hI2 := rfl
 M :=  ![![![169, 0, 0, 0], ![-104, 13, 0, -13]], ![![52, 65, 0, -13], ![-78, 0, 39, -78]]]
 hmul := by decide
 f :=  ![![![![3109809421, 232745085, -7456078908, 14679307683], ![-3025002915, 10769891756, -227640, 0]], ![![-54, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![13, 0, 0, 0]], ![![-8, 1, 0, -1]]], ![![![4, 5, 0, -1]], ![![-6, 0, 3, -6]]]]
 hle1 := by decide
 hle2 := by decide

def PBC13 : IsPrimesAboveP 13 ![I13N0, I13N1, I13N2, I13N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
    exact isPrimeI13N3
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI13N2, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}
def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0], ![-4, -5, -4, 8]] i)))

def SI17N0: IdealEqSpanCertificate timesTableO I17N0
 ![![17, 0, 0, 0], ![-4, -5, -4, 8]] 
 ![![17, 0, 0, 0], ![0, 17, 0, 0], ![16, 16, 1, 0], ![16, 1, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![17, 0, 0, 0], ![0, 17, 0, 0], ![0, 0, 17, 0], ![0, 0, 0, 17]], ![![-4, -5, -4, 8], ![-16, -8, -5, 4], ![-56, 27, 40, -103], ![-30, 16, 24, -62]]]
  hmulB := by decide
  f := ![![![1421, 599, 342, -96], ![-629, 1666, 0, 0]], ![![-100, -40, -23, 4], ![51, -119, 0, 0]], ![![1244, 527, 301, -88], ![-541, 1456, 0, 0]], ![![1332, 562, 321, -91], ![-587, 1561, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-16, -16, 17, 0], ![-16, -1, 0, 17]], ![![-4, 3, -4, 8], ![0, 4, -5, 4], ![56, -30, 40, -103], ![34, -18, 24, -62]]]
  hle1 := by decide
  hle2 := by decide

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI17N0)

def MemCI17N0 : IdealMemCertificate B I17N0
  ![![17, 0, 0, 0], ![0, 17, 0, 0], ![16, 16, 1, 0], ![16, 1, 0, 1]] ![9275, 3444, 8830, -24820] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI17N0
 g := ![15595, -6648, 8830, -24820]
 hmem := by decide

def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [15, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 16], [0, 1]]
 g := ![![[14, 8], [4], [2], [1]],![[0, 9], [4], [2], [1]]]
 h' := ![![[11, 16], [4, 12], [8, 15], [2, 11], [0, 1]],![[0, 1], [0, 5], [3, 2], [4, 6], [11, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [13, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal O 17 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I17N0
  hcard := NI17N0
  P := [15, 6, 1]
  f := ofList [15, 6, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P17P0
  hneq := by decide
  hlen := by decide
  c := ![9275, 3444, 8830, -24820]
  a := ![-126, 117, 129, -275]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI17N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI17N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal.isPrime PI17N0
def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0], ![-14, 5, 6, -12]] i)))

def SI17N1: IdealEqSpanCertificate timesTableO I17N1
 ![![17, 0, 0, 0], ![-14, 5, 6, -12]] 
 ![![17, 0, 0, 0], ![0, 17, 0, 0], ![7, 16, 1, 0], ![16, 9, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![17, 0, 0, 0], ![0, 17, 0, 0], ![0, 0, 17, 0], ![0, 0, 0, 17]], ![![-14, 5, 6, -12], ![24, -8, 5, -6], ![44, -3, -40, 67], ![30, -4, -16, 28]]]
  hmulB := by decide
  f := ![![![1453, -474, 570, -828], ![-510, -1326, 0, 0]], ![![-102, 34, -48, 72], ![51, 102, 0, 0]], ![![499, -162, 191, -276], ![-166, -450, 0, 0]], ![![1302, -424, 516, -751], ![-467, -1194, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-7, -16, 17, 0], ![-16, -9, 0, 17]], ![![8, 1, 6, -12], ![5, -2, 5, -6], ![-44, 2, -40, 67], ![-18, 0, -16, 28]]]
  hle1 := by decide
  hle2 := by decide

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI17N1)

def MemCI17N1 : IdealMemCertificate B I17N1
  ![![17, 0, 0, 0], ![0, 17, 0, 0], ![7, 16, 1, 0], ![16, 9, 0, 1]] ![-910, -96, -98, 20] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI17N1
 g := ![-32, 76, -98, 20]
 hmem := by decide

def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [7, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 16], [0, 1]]
 g := ![![[3, 16], [13], [16], [1]],![[7, 1], [13], [16], [1]]]
 h' := ![![[13, 16], [2, 4], [5, 9], [10, 13], [0, 1]],![[0, 1], [3, 13], [3, 8], [9, 4], [13, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [6, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal O 17 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I17N1
  hcard := NI17N1
  P := [7, 4, 1]
  f := ofList [7, 4, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P17P1
  hneq := by decide
  hlen := by decide
  c := ![-910, -96, -98, 20]
  a := ![-5, 6, 2, -11]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI17N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI17N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal.isPrime PI17N1
def MulI17N0 : IdealMulEqCertificate timesTableO (I17N0) I17N1
  ![![17, 0, 0, 0], ![-4, -5, -4, 8]] ![![17, 0, 0, 0], ![-14, 5, 6, -12]]
  ![![17, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![289, 0, 0, 0], ![-238, 85, 102, -204]], ![![-68, -85, -68, 136], ![0, 0, -17, 34]]]
 hmul := by decide
 f :=  ![![![![54091124797, -17577185129, 21664523562, -31609066632], ![-19756807728, -49809912876, 0, 0]], ![![176618939, 2810, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![17, 0, 0, 0]], ![![-14, 5, 6, -12]]], ![![![-4, -5, -4, 8]], ![![0, 0, -1, 2]]]]
 hle1 := by decide
 hle2 := by decide

def PBC17 : IsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI17N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}
def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0], ![-5, -5, -4, 8]] i)))

def SI19N0: IdealEqSpanCertificate timesTableO I19N0
 ![![19, 0, 0, 0], ![-5, -5, -4, 8]] 
 ![![19, 0, 0, 0], ![0, 19, 0, 0], ![14, 18, 1, 0], ![4, 6, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![19, 0, 0, 0], ![0, 19, 0, 0], ![0, 0, 19, 0], ![0, 0, 0, 19]], ![![-5, -5, -4, 8], ![-16, -9, -5, 4], ![-56, 27, 39, -103], ![-30, 16, 24, -63]]]
  hmulB := by decide
  f := ![![![-155, -79, -39, 12], ![76, -209, 0, 0]], ![![161, 85, 43, -20], ![-57, 209, 0, 0]], ![![37, 21, 11, -8], ![-3, 44, 0, 0]], ![![19, 11, 6, -5], ![1, 22, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-14, -18, 19, 0], ![-4, -6, 0, 19]], ![![1, 1, -4, 8], ![2, 3, -5, 4], ![-10, -3, 39, -103], ![-6, -2, 24, -63]]]
  hle1 := by decide
  hle2 := by decide

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI19N0)

def MemCI19N0 : IdealMemCertificate B I19N0
  ![![19, 0, 0, 0], ![0, 19, 0, 0], ![14, 18, 1, 0], ![4, 6, 0, 1]] ![-2416, -432, 0, -509] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI19N0
 g := ![-20, 138, 0, -509]
 hmem := by decide

def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [18, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 18], [0, 1]]
 g := ![![[16, 11], [6, 6], [9], [1]],![[2, 8], [7, 13], [9], [1]]]
 h' := ![![[16, 18], [6, 12], [10, 5], [1, 16], [0, 1]],![[0, 1], [8, 7], [14, 14], [10, 3], [16, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [10, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal O 19 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I19N0
  hcard := NI19N0
  P := [18, 3, 1]
  f := ofList [18, 3, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P19P0
  hneq := by decide
  hlen := by decide
  c := ![-2416, -432, 0, -509]
  a := ![-17, 16, 13, -37]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI19N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI19N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal.isPrime PI19N0
def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0], ![-15, 5, 6, -12]] i)))

def SI19N1: IdealEqSpanCertificate timesTableO I19N1
 ![![19, 0, 0, 0], ![-15, 5, 6, -12]] 
 ![![19, 0, 0, 0], ![0, 19, 0, 0], ![11, 18, 1, 0], ![2, 7, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![19, 0, 0, 0], ![0, 19, 0, 0], ![0, 0, 19, 0], ![0, 0, 0, 19]], ![![-15, 5, 6, -12], ![24, -9, 5, -6], ![44, -3, -41, 67], ![30, -4, -16, 27]]]
  hmulB := by decide
  f := ![![![1978, -767, 786, -1140], ![-779, -2052, 0, 0]], ![![-327, 128, -132, 192], ![133, 342, 0, 0]], ![![833, -322, 331, -480], ![-328, -864, 0, 0]], ![![98, -37, 30, -41], ![-20, -90, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-11, -18, 19, 0], ![-2, -7, 0, 19]], ![![-3, -1, 6, -12], ![-1, -3, 5, -6], ![19, 14, -41, 67], ![8, 5, -16, 27]]]
  hle1 := by decide
  hle2 := by decide

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI19N1)

def MemCI19N1 : IdealMemCertificate B I19N1
  ![![19, 0, 0, 0], ![0, 19, 0, 0], ![11, 18, 1, 0], ![2, 7, 0, 1]] ![3441, -1224, -4341, 8610] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI19N1
 g := ![1788, 876, -4341, 8610]
 hmem := by decide

def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [18, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 18], [0, 1]]
 g := ![![[7, 17], [16, 16], [11], [1]],![[12, 2], [14, 3], [11], [1]]]
 h' := ![![[7, 18], [16, 6], [12, 15], [1, 7], [0, 1]],![[0, 1], [1, 13], [3, 4], [12, 12], [7, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [3, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal O 19 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I19N1
  hcard := NI19N1
  P := [18, 12, 1]
  f := ofList [18, 12, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P19P1
  hneq := by decide
  hlen := by decide
  c := ![3441, -1224, -4341, 8610]
  a := ![-31, 30, 41, -68]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI19N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI19N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal.isPrime PI19N1
def MulI19N0 : IdealMulEqCertificate timesTableO (I19N0) I19N1
  ![![19, 0, 0, 0], ![-5, -5, -4, 8]] ![![19, 0, 0, 0], ![-15, 5, 6, -12]]
  ![![19, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![361, 0, 0, 0], ![-285, 95, 114, -228]], ![![-95, -95, -76, 152], ![19, 0, -19, 38]]]
 hmul := by decide
 f :=  ![![![![5159672693632, -2002328800973, 2062969480992, -2995349883876], ![-2057090469295, -5370298113600, 0, 0]], ![![596682592, 4942, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![19, 0, 0, 0]], ![![-15, 5, 6, -12]]], ![![![-5, -5, -4, 8]], ![![1, 0, -1, 2]]]]
 hle1 := by decide
 hle2 := by decide

def PBC19 : IsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI19N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0], ![6, 1, 0, -1]] i)))

def SI23N0: IdealEqSpanCertificate timesTableO I23N0
 ![![23, 0, 0, 0], ![6, 1, 0, -1]] 
 ![![23, 0, 0, 0], ![4, 1, 0, 0], ![7, 0, 1, 0], ![21, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![23, 0, 0, 0], ![0, 23, 0, 0], ![0, 0, 23, 0], ![0, 0, 0, 23]], ![![6, 1, 0, -1], ![-6, 14, 9, -18], ![36, 3, 14, -9], ![16, 4, 6, -2]]]
  hmulB := by decide
  f := ![![![490375, -1137267, -728364, 1461027], ![14973, 1868244, -4416, 0]], ![![110594, -256493, -164271, 329512], ![3386, 421353, -996, 0]], ![![147911, -343035, -219697, 440691], ![4521, 563520, -1332, 0]], ![![447735, -1038374, -665028, 1333981], ![13666, 1705788, -4032, 0]]]
  g := ![![![1, 0, 0, 0], ![-4, 23, 0, 0], ![-7, 0, 23, 0], ![-21, 0, 0, 23]], ![![1, 1, 0, -1], ![11, 14, 9, -18], ![5, 3, 14, -9], ![0, 4, 6, -2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0
def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0], ![-10, 1, 0, -1]] i)))

def SI23N1: IdealEqSpanCertificate timesTableO I23N1
 ![![23, 0, 0, 0], ![-10, 1, 0, -1]] 
 ![![23, 0, 0, 0], ![18, 1, 0, 0], ![21, 0, 1, 0], ![5, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![23, 0, 0, 0], ![0, 23, 0, 0], ![0, 0, 23, 0], ![0, 0, 0, 23]], ![![-10, 1, 0, -1], ![-6, -2, 9, -18], ![36, 3, -2, -9], ![16, 4, 6, -18]]]
  hmulB := by decide
  f := ![![![1211127, 535121, -2270744, 4510559], ![-699407, 5802808, -920, 0]], ![![989936, 437389, -1856027, 3686774], ![-571664, 4743013, -752, 0]], ![![1103183, 487426, -2068355, 4108538], ![-637064, 5285610, -838, 0]], ![![263295, 116330, -493640, 980557], ![-152030, 1261480, -200, 0]]]
  g := ![![![1, 0, 0, 0], ![-18, 23, 0, 0], ![-21, 0, 23, 0], ![-5, 0, 0, 23]], ![![-1, 1, 0, -1], ![-3, -2, 9, -18], ![3, 3, -2, -9], ![-4, 4, 6, -18]]]
  hle1 := by decide
  hle2 := by decide

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulEqCertificate timesTableO (I23N0) I23N0
  ![![23, 0, 0, 0], ![6, 1, 0, -1]] ![![23, 0, 0, 0], ![6, 1, 0, -1]]
  ![![-1, 3, 3, -6]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![529, 0, 0, 0], ![138, 23, 0, -23]], ![![138, 23, 0, -23], ![14, 16, 3, -22]]]
 hmul := by decide
 f :=  ![![![![-80193846836421021, 185981977475696148, 119112401427095418, -238927800481791815], ![-2445795785262513, -305521896363985647, 722273258972328, 0]], ![![0, 0, 0, 0], ![60737234785, 144533168, -11937, 0]]]]
 g :=  ![![![![-115, 69, 69, -138]], ![![-36, 22, 33, -64]]], ![![![-36, 22, 33, -64]], ![![-8, 5, 12, -23]]]]
 hle1 := by decide
 hle2 := by decide

def MulI23N1 : IdealMulEqCertificate timesTableO (I23N0*I23N0) I23N1
  ![![-1, 3, 3, -6]] ![![23, 0, 0, 0], ![-10, 1, 0, -1]]
  ![![23, 0, 0, 0], ![2, 12, 4, -9]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI23N0
 hI2 := rfl
 M :=  ![![![-23, 69, 69, -138], ![4, -22, -15, 28]]]
 hmul := by decide
 f :=  ![![![![205416115, 90883912, -385820281, 766552883], ![-118688261, 986013738, 128588, 0]]], ![![![26939836, 11919205, -50599399, 100531562], ![-15565661, 129313323, 16864, 0]]]]
 g :=  ![![![![-3, -9, -1, 3], ![23, 0, 0, 0]], ![![0, -2, -1, 2], ![2, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI23N2 : IdealMulEqCertificate timesTableO (I23N0*I23N0*I23N1) I23N1
  ![![23, 0, 0, 0], ![2, 12, 4, -9]] ![![23, 0, 0, 0], ![-10, 1, 0, -1]]
  ![![23, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI23N1
 hI2 := rfl
 M :=  ![![![529, 0, 0, 0], ![-230, 23, 0, -23]], ![![46, 276, 92, -207], ![-92, -46, 46, -92]]]
 hmul := by decide
 f :=  ![![![![2176236211, 961548202, -4080247976, 8104919150], ![-1256770998, 10426931328, -1653496, 0]], ![![0, 0, 0, 0], ![7252, 0, 0, 0]]]]
 g :=  ![![![![23, 0, 0, 0]], ![![-10, 1, 0, -1]]], ![![![2, 12, 4, -9]], ![![-4, -2, 2, -4]]]]
 hle1 := by decide
 hle2 := by decide

def PBC23 : IsPrimesAboveP 23 ![I23N0, I23N0, I23N1, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI23N2, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}
def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0], ![10, 0, 1, -2]] i)))

def SI29N0: IdealEqSpanCertificate timesTableO I29N0
 ![![29, 0, 0, 0], ![10, 0, 1, -2]] 
 ![![29, 0, 0, 0], ![0, 29, 0, 0], ![2, 7, 1, 0], ![25, 18, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![29, 0, 0, 0], ![0, 29, 0, 0], ![0, 0, 29, 0], ![0, 0, 0, 29]], ![![10, 0, 1, -2], ![4, 11, 0, -1], ![-6, 12, 19, -18], ![0, 6, 4, 2]]]
  hmulB := by decide
  f := ![![![-9, 0, -1, 2], ![29, 0, 0, 0]], ![![-32, -87, 0, 8], ![0, 232, 0, 0]], ![![-8, -21, 0, 2], ![1, 56, 0, 0]], ![![-19, -54, 0, 5], ![0, 144, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-2, -7, 29, 0], ![-25, -18, 0, 29]], ![![2, 1, 1, -2], ![1, 1, 0, -1], ![14, 7, 19, -18], ![-2, -2, 4, 2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI29N0)

def MemCI29N0 : IdealMemCertificate B I29N0
  ![![29, 0, 0, 0], ![0, 29, 0, 0], ![2, 7, 1, 0], ![25, 18, 0, 1]] ![377, 216, 260, -595] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI29N0
 g := ![508, 314, 260, -595]
 hmem := by decide

def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [25, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 28], [0, 1]]
 g := ![![[5, 7], [6], [21, 4], [20, 1]],![[0, 22], [6], [14, 25], [11, 28]]]
 h' := ![![[20, 28], [4, 23], [26, 21], [22, 27], [0, 1]],![[0, 1], [0, 6], [11, 8], [11, 2], [20, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [2, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal O 29 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I29N0
  hcard := NI29N0
  P := [25, 9, 1]
  f := ofList [25, 9, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P29P0
  hneq := by decide
  hlen := by decide
  c := ![377, 216, 260, -595]
  a := ![-16, 16, 17, -35]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI29N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI29N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal.isPrime PI29N0
def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0], ![-11, 0, 1, -2]] i)))

def SI29N1: IdealEqSpanCertificate timesTableO I29N1
 ![![29, 0, 0, 0], ![-11, 0, 1, -2]] 
 ![![29, 0, 0, 0], ![0, 29, 0, 0], ![10, 20, 1, 0], ![25, 10, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![29, 0, 0, 0], ![0, 29, 0, 0], ![0, 0, 29, 0], ![0, 0, 0, 29]], ![![-11, 0, 1, -2], ![4, -10, 0, -1], ![-6, 12, -2, -18], ![0, 6, 4, -19]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0], ![0, 0, 0, 0]], ![![12, -29, 0, -3], ![0, -87, 0, 0]], ![![9, -20, 0, -2], ![1, -60, 0, 0]], ![![5, -10, 0, -1], ![0, -30, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-10, -20, 29, 0], ![-25, -10, 0, 29]], ![![1, 0, 1, -2], ![1, 0, 0, -1], ![16, 8, -2, -18], ![15, 4, 4, -19]]]
  hle1 := by decide
  hle2 := by decide

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI29N1)

def MemCI29N1 : IdealMemCertificate B I29N1
  ![![29, 0, 0, 0], ![0, 29, 0, 0], ![10, 20, 1, 0], ![25, 10, 0, 1]] ![757, -118, -383, 876] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI29N1
 g := ![-597, -42, -383, 876]
 hmem := by decide

def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [24, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 28], [0, 1]]
 g := ![![[15, 23], [1], [24, 16], [17, 1]],![[0, 6], [1], [6, 13], [5, 28]]]
 h' := ![![[17, 28], [21, 9], [4, 28], [27, 4], [0, 1]],![[0, 1], [0, 20], [16, 1], [8, 25], [17, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [7, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N1 : CertifiedPrimeIdeal O 29 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I29N1
  hcard := NI29N1
  P := [24, 12, 1]
  f := ofList [24, 12, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P29P1
  hneq := by decide
  hlen := by decide
  c := ![757, -118, -383, 876]
  a := ![-11, 13, 14, -24]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI29N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI29N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := CertifiedPrimeIdeal.isPrime PI29N1
def MulI29N0 : IdealMulEqCertificate timesTableO (I29N0) I29N1
  ![![29, 0, 0, 0], ![10, 0, 1, -2]] ![![29, 0, 0, 0], ![-11, 0, 1, -2]]
  ![![29, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![841, 0, 0, 0], ![-319, 0, 29, -58]], ![![290, 0, 29, -58], ![-116, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![5332, 0, 671, -1342], ![-1903, 0, 0, 0]], ![![-17556, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![29, 0, 0, 0]], ![![-11, 0, 1, -2]]], ![![![10, 0, 1, -2]], ![![-4, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC29 : IsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI29N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
