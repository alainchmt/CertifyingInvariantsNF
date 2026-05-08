
import IdealArithmetic.Examples.NF4_4_54381317_1.RI4_4_54381317_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic

set_option linter.all false

open Classical Polynomial

noncomputable section 
instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate timesTableO I2N0
 ![![2, 0, 0, 0]] 
 ![![2, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 2]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![2, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 2]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0]], ![![0, 1, 0, 0]], ![![0, 0, 1, 0]], ![![0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 16 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI2N0)

def MemCI2N0 : IdealMemCertificate B I2N0
  ![![2, 0, 0, 0], ![0, 2, 0, 0], ![0, 0, 2, 0], ![0, 0, 0, 2]] ![59882581222, 57263856106, 17635603102, 1738324180] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI2N0
 g := ![29941290611, 28631928053, 8817801551, 869162090]
 hmem := by decide

def P2P0 : CertificateIrreducibleZModOfList' 2 4 2 1 [1, 0, 0, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 1], [1, 0, 0, 1], [0, 1, 1, 1], [0, 1]]
 g := ![![[]],![[1]],![[1, 1, 1]],![[0, 1, 1]]]
 h' := ![![[0, 0, 1], [0, 1]],![[1, 0, 0, 1], [0, 0, 1]],![[0, 1, 1, 1], [1, 0, 0, 1]],![[0, 1], [0, 1, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1, 1, 1], []]
 b := ![[], [], [0, 1, 0, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal O 2 where 
  r := 4
  n := 4
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I2N0
  hcard := NI2N0
  P := [1, 0, 0, 1, 1]
  f := ofList [1, 0, 0, 1, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P2P0
  hneq := by decide
  hlen := by decide
  c := ![59882581222, 57263856106, 17635603102, 1738324180]
  a := ![0, -1, -1, -1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI2N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI2N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal.isPrime PI2N0
def PBC2 : IsPrimesAboveP 2 ![I2N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    unfold I2N0
    rw [Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}
def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0], ![-132, -67, -4, 1]] i)))

def SI3N0: IdealEqSpanCertificate timesTableO I3N0
 ![![3, 0, 0, 0], ![-132, -67, -4, 1]] 
 ![![3, 0, 0, 0], ![0, 3, 0, 0], ![2, 2, 1, 0], ![2, 1, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, 0, 0, 0], ![0, 3, 0, 0], ![0, 0, 3, 0], ![0, 0, 0, 3]], ![![-132, -67, -4, 1], ![383, 200, 13, -3], ![-1149, -613, -40, 10], ![3830, 2171, 187, -30]]]
  hmulB := by decide
  f := ![![![120, 66, 5, -1], ![-6, -3, 0, 0]], ![![0, 1, 0, 0], ![0, 0, 0, 0]], ![![124, 67, 5, -1], ![-3, -2, 0, 0]], ![![36, 22, 2, 0], ![-5, -2, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-2, -2, 3, 0], ![-2, -1, 0, 3]], ![![-42, -20, -4, 1], ![121, 59, 13, -3], ![-363, -181, -40, 10], ![1172, 609, 187, -30]]]
  hle1 := by decide
  hle2 := by decide

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI3N0)

def MemCI3N0 : IdealMemCertificate B I3N0
  ![![3, 0, 0, 0], ![0, 3, 0, 0], ![2, 2, 1, 0], ![2, 1, 0, 1]] ![1553070, 1297607, 282884, -6161] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI3N0
 g := ![333208, 246000, 282884, -6161]
 hmem := by decide

def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [1, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 2], [0, 1]]
 g := ![![[0, 1]],![[0, 2]]]
 h' := ![![[0, 2], [0, 1]],![[0, 1], [0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [0, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal O 3 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I3N0
  hcard := NI3N0
  P := [1, 0, 1]
  f := ofList [1, 0, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P3P0
  hneq := by decide
  hlen := by decide
  c := ![1553070, 1297607, 282884, -6161]
  a := ![-2, 3, -64, 1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI3N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI3N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal.isPrime PI3N0
def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0], ![1, 1, 0, 0]] i)))

def SI3N1: IdealEqSpanCertificate timesTableO I3N1
 ![![3, 0, 0, 0], ![1, 1, 0, 0]] 
 ![![3, 0, 0, 0], ![1, 1, 0, 0], ![2, 0, 1, 0], ![1, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, 0, 0, 0], ![0, 3, 0, 0], ![0, 0, 3, 0], ![0, 0, 0, 3]], ![![1, 1, 0, 0], ![0, 1, 1, 0], ![0, 0, 1, 1], ![383, 332, 80, 2]]]
  hmulB := by decide
  f := ![![![0, -2, 1, 2], ![3, 3, -6, 0]], ![![0, 0, 1, 1], ![1, 0, -3, 0]], ![![0, -1, 1, 1], ![2, 1, -3, 0]], ![![0, 0, 1, 1], ![1, -1, -2, 0]]]
  g := ![![![1, 0, 0, 0], ![-1, 3, 0, 0], ![-2, 0, 3, 0], ![-1, 0, 0, 3]], ![![0, 1, 0, 0], ![-1, 1, 1, 0], ![-1, 0, 1, 1], ![-37, 332, 80, 2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0], ![-1, 1, 0, 0]] i)))

def SI3N2: IdealEqSpanCertificate timesTableO I3N2
 ![![3, 0, 0, 0], ![-1, 1, 0, 0]] 
 ![![3, 0, 0, 0], ![2, 1, 0, 0], ![2, 0, 1, 0], ![2, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, 0, 0, 0], ![0, 3, 0, 0], ![0, 0, 3, 0], ![0, 0, 0, 3]], ![![-1, 1, 0, 0], ![0, -1, 1, 0], ![0, 0, -1, 1], ![383, 332, 80, 0]]]
  hmulB := by decide
  f := ![![![2, 1, 0, -2], ![3, 6, 6, 0]], ![![1, 1, 1, -2], ![1, 3, 6, 0]], ![![1, 1, 0, -1], ![1, 4, 3, 0]], ![![1, 1, 0, -1], ![1, 4, 4, 0]]]
  g := ![![![1, 0, 0, 0], ![-2, 3, 0, 0], ![-2, 0, 3, 0], ![-2, 0, 0, 3]], ![![-1, 1, 0, 0], ![0, -1, 1, 0], ![0, 0, -1, 1], ![-147, 332, 80, 0]]]
  hle1 := by decide
  hle2 := by decide

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulEqCertificate timesTableO (I3N0) I3N1
  ![![3, 0, 0, 0], ![-132, -67, -4, 1]] ![![3, 0, 0, 0], ![1, 1, 0, 0]]
  ![![3, 0, 0, 0], ![-169, -74, -3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![9, 0, 0, 0], ![3, 3, 0, 0]], ![![-396, -201, -12, 3], ![251, 133, 9, -2]]]
 hmul := by decide
 f :=  ![![![![457260, 205536, -163070, -10136], ![-812904, 479973, 26174, 0]], ![![4232, 0, 0, 0], ![-3, 0, 0, 0]]], ![![![-25802880, -11598436, 9201767, 571943], ![45871788, -27084133, -1476908, 0]], ![![-238808, 0, 0, 0], ![169, 0, 0, 0]]]]
 g :=  ![![![![3, 0, 0, 0], ![0, 0, 0, 0]], ![![1, 1, 0, 0], ![0, 0, 0, 0]]], ![![![37, 7, -1, 0], ![3, 0, 0, 0]], ![![140, 69, 4, -1], ![1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI3N1 : IdealMulEqCertificate timesTableO (I3N0*I3N1) I3N2
  ![![3, 0, 0, 0], ![-169, -74, -3, 1]] ![![3, 0, 0, 0], ![-1, 1, 0, 0]]
  ![![3, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI3N0
 hI2 := rfl
 M :=  ![![![9, 0, 0, 0], ![-3, 3, 0, 0]], ![![-507, -222, -9, 3], ![552, 237, 9, -3]]]
 hmul := by decide
 f :=  ![![![![2952, -2827, 1314, -132], ![6151, -3514, 380, 0]], ![![16, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![3, 0, 0, 0]], ![![-1, 1, 0, 0]]], ![![![-169, -74, -3, 1]], ![![184, 79, 3, -1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC3 : IsPrimesAboveP 3 ![I3N0, I3N1, I3N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI3N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}
def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0], ![-133, -67, -4, 1]] i)))

def SI5N0: IdealEqSpanCertificate timesTableO I5N0
 ![![5, 0, 0, 0], ![-133, -67, -4, 1]] 
 ![![5, 0, 0, 0], ![0, 5, 0, 0], ![4, 3, 1, 0], ![3, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![5, 0, 0, 0], ![0, 5, 0, 0], ![0, 0, 5, 0], ![0, 0, 0, 5]], ![![-133, -67, -4, 1], ![383, 199, 13, -3], ![-1149, -613, -41, 10], ![3830, 2171, 187, -31]]]
  hmulB := by decide
  f := ![![![75, 110, 20, -2], ![-170, -60, 0, 0]], ![![48, 7, -3, 0], ![45, 15, 0, 0]], ![![9, 52, 12, -1], ![-112, -39, 0, 0]], ![![45, 66, 12, -1], ![-102, -36, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-4, -3, 5, 0], ![-3, 0, 0, 5]], ![![-24, -11, -4, 1], ![68, 32, 13, -3], ![-203, -98, -41, 10], ![635, 322, 187, -31]]]
  hle1 := by decide
  hle2 := by decide

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI5N0)

def MemCI5N0 : IdealMemCertificate B I5N0
  ![![5, 0, 0, 0], ![0, 5, 0, 0], ![4, 3, 1, 0], ![3, 0, 0, 1]] ![274995, 239524, 61883, 3951] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI5N0
 g := ![3122, 10775, 61883, 3951]
 hmem := by decide

def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [1, 1, 1] where
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

def PI5N0 : CertifiedPrimeIdeal O 5 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I5N0
  hcard := NI5N0
  P := [1, 1, 1]
  f := ofList [1, 1, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P5P0
  hneq := by decide
  hlen := by decide
  c := ![274995, 239524, 61883, 3951]
  a := ![-1, 1, 1, -3]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI5N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI5N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal.isPrime PI5N0
def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0], ![2, 1, 0, 0]] i)))

def SI5N1: IdealEqSpanCertificate timesTableO I5N1
 ![![5, 0, 0, 0], ![2, 1, 0, 0]] 
 ![![5, 0, 0, 0], ![2, 1, 0, 0], ![1, 0, 1, 0], ![3, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![5, 0, 0, 0], ![0, 5, 0, 0], ![0, 0, 5, 0], ![0, 0, 0, 5]], ![![2, 1, 0, 0], ![0, 2, 1, 0], ![0, 0, 2, 1], ![383, 332, 80, 3]]]
  hmulB := by decide
  f := ![![![3, 1, 6, 3], ![-5, 0, -15, 0]], ![![-2, -3, 5, 3], ![6, 5, -15, 0]], ![![-1, -1, 0, 0], ![3, 1, 0, 0]], ![![1, -1, 3, 2], ![-1, 3, -9, 0]]]
  g := ![![![1, 0, 0, 0], ![-2, 5, 0, 0], ![-1, 0, 5, 0], ![-3, 0, 0, 5]], ![![0, 1, 0, 0], ![-1, 2, 1, 0], ![-1, 0, 2, 1], ![-74, 332, 80, 3]]]
  hle1 := by decide
  hle2 := by decide

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def I5N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0], ![-1, 1, 0, 0]] i)))

def SI5N2: IdealEqSpanCertificate timesTableO I5N2
 ![![5, 0, 0, 0], ![-1, 1, 0, 0]] 
 ![![5, 0, 0, 0], ![4, 1, 0, 0], ![4, 0, 1, 0], ![4, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![5, 0, 0, 0], ![0, 5, 0, 0], ![0, 0, 5, 0], ![0, 0, 0, 5]], ![![-1, 1, 0, 0], ![0, -1, 1, 0], ![0, 0, -1, 1], ![383, 332, 80, 0]]]
  hmulB := by decide
  f := ![![![4, -2, 3, -4], ![15, 5, 20, 0]], ![![3, -3, 2, -1], ![11, -5, 5, 0]], ![![2, -1, 3, -3], ![6, 1, 15, 0]], ![![2, -1, 3, -3], ![6, 1, 16, 0]]]
  g := ![![![1, 0, 0, 0], ![-4, 5, 0, 0], ![-4, 0, 5, 0], ![-4, 0, 0, 5]], ![![-1, 1, 0, 0], ![0, -1, 1, 0], ![0, 0, -1, 1], ![-253, 332, 80, 0]]]
  hle1 := by decide
  hle2 := by decide

lemma NI5N2 : Nat.card (O ⧸ I5N2) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI5N2)

lemma isPrimeI5N2 : Ideal.IsPrime I5N2 := prime_ideal_of_norm_prime hp5.out _ NI5N2
def MulI5N0 : IdealMulEqCertificate timesTableO (I5N0) I5N1
  ![![5, 0, 0, 0], ![-133, -67, -4, 1]] ![![5, 0, 0, 0], ![2, 1, 0, 0]]
  ![![5, 0, 0, 0], ![92, 60, 5, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![25, 0, 0, 0], ![10, 5, 0, 0]], ![![-665, -335, -20, 5], ![117, 65, 5, -1]]]
 hmul := by decide
 f :=  ![![![![12652609, 4466979, 45137420, 23024819], ![-30622733, 4652112, -115139265, 0]], ![![15168, 0, 0, 0], ![-10, 0, 0, 0]]], ![![![233112320, 82299840, 831614290, 424210524], ![-564194814, 85710785, -2121332113, 0]], ![![279456, 0, 0, 0], ![-184, 0, 0, 0]]]]
 g :=  ![![![![-87, -60, -5, 1], ![5, 0, 0, 0]], ![![-90, -59, -5, 1], ![5, 0, 0, 0]]], ![![![-41, -7, 1, 0], ![-5, 0, 0, 0]], ![![-87, -59, -5, 1], ![6, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI5N1 : IdealMulEqCertificate timesTableO (I5N0*I5N1) I5N2
  ![![5, 0, 0, 0], ![92, 60, 5, -1]] ![![5, 0, 0, 0], ![-1, 1, 0, 0]]
  ![![5, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI5N0
 hI2 := rfl
 M :=  ![![![25, 0, 0, 0], ![-5, 5, 0, 0]], ![![460, 300, 25, -5], ![-475, -300, -25, 5]]]
 hmul := by decide
 f :=  ![![![![246, -343, 232, -10], ![861, -1094, 46, 0]], ![![-4, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![5, 0, 0, 0]], ![![-1, 1, 0, 0]]], ![![![92, 60, 5, -1]], ![![-95, -60, -5, 1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC5 : IsPrimesAboveP 5 ![I5N0, I5N1, I5N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
    exact isPrimeI5N2
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI5N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}
def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0], ![-134, -65, -4, 1]] i)))

def SI7N0: IdealEqSpanCertificate timesTableO I7N0
 ![![7, 0, 0, 0], ![-134, -65, -4, 1]] 
 ![![7, 0, 0, 0], ![0, 7, 0, 0], ![3, 1, 1, 0], ![4, 2, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![7, 0, 0, 0], ![0, 7, 0, 0], ![0, 0, 7, 0], ![0, 0, 0, 7]], ![![-134, -65, -4, 1], ![383, 198, 15, -3], ![-1149, -613, -42, 12], ![4596, 2835, 347, -30]]]
  hmulB := by decide
  f := ![![![41, 166, 44, -2], ![-238, -84, 0, 0]], ![![114, -17, -18, 0], ![126, 42, 0, 0]], ![![53, 78, 17, -1], ![-83, -30, 0, 0]], ![![56, 90, 20, -1], ![-100, -36, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-3, -1, 7, 0], ![-4, -2, 0, 7]], ![![-18, -9, -4, 1], ![50, 27, 15, -3], ![-153, -85, -42, 12], ![525, 364, 347, -30]]]
  hle1 := by decide
  hle2 := by decide

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI7N0)

def MemCI7N0 : IdealMemCertificate B I7N0
  ![![7, 0, 0, 0], ![0, 7, 0, 0], ![3, 1, 1, 0], ![4, 2, 0, 1]] ![29878, 25513, 6292, 332] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI7N0
 g := ![1382, 2651, 6292, 332]
 hmem := by decide

def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [4, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 6], [0, 1]]
 g := ![![[0, 2], [0, 1]],![[0, 5], [0, 6]]]
 h' := ![![[0, 6], [0, 3], [0, 1]],![[0, 1], [0, 4], [0, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [0, 1]]
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
  P := [4, 0, 1]
  f := ofList [4, 0, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P0
  hneq := by decide
  hlen := by decide
  c := ![29878, 25513, 6292, 332]
  a := ![0, -1, -1, 1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI7N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI7N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal.isPrime PI7N0
def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0], ![-132, -70, -4, 1]] i)))

def SI7N1: IdealEqSpanCertificate timesTableO I7N1
 ![![7, 0, 0, 0], ![-132, -70, -4, 1]] 
 ![![7, 0, 0, 0], ![0, 7, 0, 0], ![3, 5, 1, 0], ![6, 6, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![7, 0, 0, 0], ![0, 7, 0, 0], ![0, 0, 7, 0], ![0, 0, 0, 7]], ![![-132, -70, -4, 1], ![383, 200, 10, -3], ![-1149, -613, -40, 7], ![2681, 1175, -53, -33]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0], ![0, 0, 0, 0]], ![![67, 21, -6, -1], ![-98, -35, 0, 0]], ![![86, 35, -3, -1], ![-68, -25, 0, 0]], ![![96, 38, -4, -1], ![-82, -30, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-3, -5, 7, 0], ![-6, -6, 0, 7]], ![![-18, -8, -4, 1], ![53, 24, 10, -3], ![-153, -65, -40, 7], ![434, 234, -53, -33]]]
  hle1 := by decide
  hle2 := by decide

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI7N1)

def MemCI7N1 : IdealMemCertificate B I7N1
  ![![7, 0, 0, 0], ![0, 7, 0, 0], ![3, 5, 1, 0], ![6, 6, 0, 1]] ![279991, 243549, 62804, 4076] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI7N1
 g := ![9589, -13561, 62804, 4076]
 hmem := by decide

def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 6], [0, 1]]
 g := ![![[1, 4], [5, 1]],![[0, 3], [3, 6]]]
 h' := ![![[5, 6], [4, 2], [0, 1]],![[0, 1], [0, 5], [5, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [4, 4]]
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
  P := [2, 2, 1]
  f := ofList [2, 2, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P7P1
  hneq := by decide
  hlen := by decide
  c := ![279991, 243549, 62804, 4076]
  a := ![19, 1, -1, 3]
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
  ![![7, 0, 0, 0], ![-134, -65, -4, 1]] ![![7, 0, 0, 0], ![-132, -70, -4, 1]]
  ![![7, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![49, 0, 0, 0], ![-924, -490, -28, 7]], ![![-938, -455, -28, 7], ![70, 7, -7, 0]]]
 hmul := by decide
 f :=  ![![![![8585591933, -7811126754, -6128969204, -456804606], ![-80351453602, -27846656914, 0, 0]], ![![9114670, -144, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![7, 0, 0, 0]], ![![-132, -70, -4, 1]]], ![![![-134, -65, -4, 1]], ![![10, 1, -1, 0]]]]
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
def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0], ![-130, -67, -4, 1]] i)))

def SI11N0: IdealEqSpanCertificate timesTableO I11N0
 ![![11, 0, 0, 0], ![-130, -67, -4, 1]] 
 ![![11, 0, 0, 0], ![0, 11, 0, 0], ![4, 1, 1, 0], ![7, 3, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![11, 0, 0, 0], ![0, 11, 0, 0], ![0, 0, 11, 0], ![0, 0, 0, 11]], ![![-130, -67, -4, 1], ![383, 202, 13, -3], ![-1149, -613, -38, 10], ![3830, 2171, 187, -28]]]
  hmulB := by decide
  f := ![![![121, 154, 28, -2], ![-638, -220, 0, 0]], ![![28, -3, -4, 0], ![132, 44, 0, 0]], ![![82, 74, 11, -1], ![-217, -76, 0, 0]], ![![61, 85, 16, -1], ![-372, -128, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-4, -1, 11, 0], ![-7, -3, 0, 11]], ![![-11, -6, -4, 1], ![32, 18, 13, -3], ![-97, -55, -38, 10], ![298, 188, 187, -28]]]
  hle1 := by decide
  hle2 := by decide

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI11N0)

def MemCI11N0 : IdealMemCertificate B I11N0
  ![![11, 0, 0, 0], ![0, 11, 0, 0], ![4, 1, 1, 0], ![7, 3, 0, 1]] ![126005, 112292, 30515, 2311] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI11N0
 g := ![-1112, 6804, 30515, 2311]
 hmem := by decide

def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [6, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 10], [0, 1]]
 g := ![![[7, 4], [6, 4], [1]],![[4, 7], [3, 7], [1]]]
 h' := ![![[2, 10], [8, 2], [5, 2], [0, 1]],![[0, 1], [1, 9], [9, 9], [2, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [1, 10]]
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
  P := [6, 9, 1]
  f := ofList [6, 9, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P0
  hneq := by decide
  hlen := by decide
  c := ![126005, 112292, 30515, 2311]
  a := ![-1, 0, 1, 2]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI11N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI11N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal.isPrime PI11N0
def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0], ![-133, -67, -4, 1]] i)))

def SI11N1: IdealEqSpanCertificate timesTableO I11N1
 ![![11, 0, 0, 0], ![-133, -67, -4, 1]] 
 ![![11, 0, 0, 0], ![0, 11, 0, 0], ![6, 9, 1, 0], ![1, 2, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![11, 0, 0, 0], ![0, 11, 0, 0], ![0, 0, 11, 0], ![0, 0, 0, 11]], ![![-133, -67, -4, 1], ![383, 199, 13, -3], ![-1149, -613, -41, 10], ![3830, 2171, 187, -31]]]
  hmulB := by decide
  f := ![![![70, 59, 8, -1], ![-121, -44, 0, 0]], ![![64, 9, -4, 0], ![132, 44, 0, 0]], ![![18, 3, -1, 0], ![36, 12, 0, 0]], ![![18, 7, 0, 0], ![13, 4, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-6, -9, 11, 0], ![-1, -2, 0, 11]], ![![-10, -3, -4, 1], ![28, 8, 13, -3], ![-83, -24, -41, 10], ![249, 50, 187, -31]]]
  hle1 := by decide
  hle2 := by decide

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI11N1)

def MemCI11N1 : IdealMemCertificate B I11N1
  ![![11, 0, 0, 0], ![0, 11, 0, 0], ![6, 9, 1, 0], ![1, 2, 0, 1]] ![124120, 109100, 28780, 1952] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI11N1
 g := ![-4592, -13984, 28780, 1952]
 hmem := by decide

def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [3, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 10], [0, 1]]
 g := ![![[0, 4], [], [1]],![[0, 7], [], [1]]]
 h' := ![![[0, 10], [0, 9], [8], [0, 1]],![[0, 1], [0, 2], [8], [0, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [0, 2]]
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
  P := [3, 0, 1]
  f := ofList [3, 0, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P11P1
  hneq := by decide
  hlen := by decide
  c := ![124120, 109100, 28780, 1952]
  a := ![-5, 0, 0, 2]
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
  ![![11, 0, 0, 0], ![-130, -67, -4, 1]] ![![11, 0, 0, 0], ![-133, -67, -4, 1]]
  ![![11, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![121, 0, 0, 0], ![-1463, -737, -44, 11]], ![![-1430, -737, -44, 11], ![55, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![-8046, 124913, 31256, -2499], ![-675019, -233860, 0, 0]], ![![928, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![11, 0, 0, 0]], ![![-133, -67, -4, 1]]], ![![![-130, -67, -4, 1]], ![![5, 0, 0, 0]]]]
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
def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![-136, -62, -4, 1]] i)))

def SI13N0: IdealEqSpanCertificate timesTableO I13N0
 ![![13, 0, 0, 0], ![-136, -62, -4, 1]] 
 ![![13, 0, 0, 0], ![0, 13, 0, 0], ![11, 6, 1, 0], ![12, 1, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![-136, -62, -4, 1], ![383, 196, 18, -3], ![-1149, -613, -44, 15], ![5745, 3831, 587, -29]]]
  hmulB := by decide
  f := ![![![-275, 1158, 396, -9], ![-2223, -780, 0, 0]], ![![114, -161, -64, 1], ![377, 130, 0, 0]], ![![-201, 896, 305, -7], ![-1709, -600, 0, 0]], ![![-266, 1047, 360, -8], ![-2025, -710, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-11, -6, 13, 0], ![-12, -1, 0, 13]], ![![-8, -3, -4, 1], ![17, 7, 18, -3], ![-65, -28, -44, 15], ![-28, 26, 587, -29]]]
  hle1 := by decide
  hle2 := by decide

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI13N0)

def MemCI13N0 : IdealMemCertificate B I13N0
  ![![13, 0, 0, 0], ![0, 13, 0, 0], ![11, 6, 1, 0], ![12, 1, 0, 1]] ![84352, 63427, 9440, -1377] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI13N0
 g := ![-228, 628, 9440, -1377]
 hmem := by decide

def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 12], [0, 1]]
 g := ![![[7, 12], [1], [12, 1]],![[8, 1], [1], [11, 12]]]
 h' := ![![[12, 12], [2, 8], [2, 12], [0, 1]],![[0, 1], [7, 5], [3, 1], [12, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [2, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal O 13 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I13N0
  hcard := NI13N0
  P := [2, 1, 1]
  f := ofList [2, 1, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P13P0
  hneq := by decide
  hlen := by decide
  c := ![84352, 63427, 9440, -1377]
  a := ![-10, 2, 13, -1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI13N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI13N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal.isPrime PI13N0
def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0], ![-134, -70, -4, 1]] i)))

def SI13N1: IdealEqSpanCertificate timesTableO I13N1
 ![![13, 0, 0, 0], ![-134, -70, -4, 1]] 
 ![![13, 0, 0, 0], ![0, 13, 0, 0], ![3, 6, 1, 0], ![8, 6, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![13, 0, 0, 0], ![0, 13, 0, 0], ![0, 0, 13, 0], ![0, 0, 0, 13]], ![![-134, -70, -4, 1], ![383, 198, 10, -3], ![-1149, -613, -42, 7], ![2681, 1175, -53, -35]]]
  hmulB := by decide
  f := ![![![414, 56, -98, -14], ![-2821, -1001, 0, 0]], ![![-1, 15, 10, 1], ![260, 91, 0, 0]], ![![126, 36, -17, -3], ![-528, -189, 0, 0]], ![![244, 36, -56, -8], ![-1617, -574, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-3, -6, 13, 0], ![-8, -6, 0, 13]], ![![-10, -4, -4, 1], ![29, 12, 10, -3], ![-83, -31, -42, 7], ![240, 131, -53, -35]]]
  hle1 := by decide
  hle2 := by decide

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI13N1)

def MemCI13N1 : IdealMemCertificate B I13N1
  ![![13, 0, 0, 0], ![0, 13, 0, 0], ![3, 6, 1, 0], ![8, 6, 0, 1]] ![39454, 37646, 11600, 1144] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI13N1
 g := ![-346, -2986, 11600, 1144]
 hmem := by decide

def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [3, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 12], [0, 1]]
 g := ![![[9, 9], [4], [12, 1]],![[0, 4], [4], [11, 12]]]
 h' := ![![[12, 12], [10, 10], [3, 11], [0, 1]],![[0, 1], [0, 3], [5, 2], [12, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [6, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal O 13 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I13N1
  hcard := NI13N1
  P := [3, 1, 1]
  f := ofList [3, 1, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P13P1
  hneq := by decide
  hlen := by decide
  c := ![39454, 37646, 11600, 1144]
  a := ![1, 1, -4, -1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI13N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI13N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal.isPrime PI13N1
def MulI13N0 : IdealMulEqCertificate timesTableO (I13N0) I13N1
  ![![13, 0, 0, 0], ![-136, -62, -4, 1]] ![![13, 0, 0, 0], ![-134, -70, -4, 1]]
  ![![13, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![169, 0, 0, 0], ![-1742, -910, -52, 13]], ![![-1768, -806, -52, 13], ![1755, 871, 39, -13]]]
 hmul := by decide
 f :=  ![![![![912140402450, -36885025536, -327327413894, -41893215806], ![-9105957361058, -3216851801375, 0, 0]], ![![13762303, -36, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![13, 0, 0, 0]], ![![-134, -70, -4, 1]]], ![![![-136, -62, -4, 1]], ![![135, 67, 3, -1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC13 : IsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI13N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0], ![-129, -67, -4, 1]] i)))

def SI17N0: IdealEqSpanCertificate timesTableO I17N0
 ![![17, 0, 0, 0], ![-129, -67, -4, 1]] 
 ![![17, 0, 0, 0], ![0, 17, 0, 0], ![13, 2, 1, 0], ![8, 9, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![17, 0, 0, 0], ![0, 17, 0, 0], ![0, 0, 17, 0], ![0, 0, 0, 17]], ![![-129, -67, -4, 1], ![383, 203, 13, -3], ![-1149, -613, -37, 10], ![3830, 2171, 187, -27]]]
  hmulB := by decide
  f := ![![![248, 271, 47, -3], ![-1734, -595, 0, 0]], ![![28, -13, -7, 0], ![357, 119, 0, 0]], ![![155, 186, 34, -2], ![-1289, -441, 0, 0]], ![![86, 97, 17, -1], ![-633, -217, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-13, -2, 17, 0], ![-8, -9, 0, 17]], ![![-5, -4, -4, 1], ![14, 12, 13, -3], ![-44, -37, -37, 10], ![95, 120, 187, -27]]]
  hle1 := by decide
  hle2 := by decide

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI17N0)

def MemCI17N0 : IdealMemCertificate B I17N0
  ![![17, 0, 0, 0], ![0, 17, 0, 0], ![13, 2, 1, 0], ![8, 9, 0, 1]] ![31415, 26836, 6617, 327] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI17N0
 g := ![-3366, 627, 6617, 327]
 hmem := by decide

def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [3, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 16], [0, 1]]
 g := ![![[6, 1], [8], [1], [1]],![[5, 16], [8], [1], [1]]]
 h' := ![![[16, 16], [12, 1], [6, 5], [14, 16], [0, 1]],![[0, 1], [11, 16], [1, 12], [15, 1], [16, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [14, 11]]
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
  P := [3, 1, 1]
  f := ofList [3, 1, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P17P0
  hneq := by decide
  hlen := by decide
  c := ![31415, 26836, 6617, 327]
  a := ![-3, 1, -1, 1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI17N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI17N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal.isPrime PI17N0
def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0], ![7, 1, 0, 0]] i)))

def SI17N1: IdealEqSpanCertificate timesTableO I17N1
 ![![17, 0, 0, 0], ![7, 1, 0, 0]] 
 ![![17, 0, 0, 0], ![7, 1, 0, 0], ![2, 0, 1, 0], ![3, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![17, 0, 0, 0], ![0, 17, 0, 0], ![0, 0, 17, 0], ![0, 0, 0, 17]], ![![7, 1, 0, 0], ![0, 7, 1, 0], ![0, 0, 7, 1], ![383, 332, 80, 8]]]
  hmulB := by decide
  f := ![![![50, -182, -34, -1], ![-119, 459, 17, 0]], ![![7, -83, -19, -1], ![-16, 204, 17, 0]], ![![-4, -8, 34, 5], ![10, 18, -85, 0]], ![![-6, -40, -13, -1], ![15, 95, 18, 0]]]
  g := ![![![1, 0, 0, 0], ![-7, 17, 0, 0], ![-2, 0, 17, 0], ![-3, 0, 0, 17]], ![![0, 1, 0, 0], ![-3, 7, 1, 0], ![-1, 0, 7, 1], ![-125, 332, 80, 8]]]
  hle1 := by decide
  hle2 := by decide

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulEqCertificate timesTableO (I17N0) I17N1
  ![![17, 0, 0, 0], ![-129, -67, -4, 1]] ![![17, 0, 0, 0], ![7, 1, 0, 0]]
  ![![17, 0, 0, 0], ![-554, -283, -15, 4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![289, 0, 0, 0], ![119, 17, 0, 0]], ![![-2193, -1139, -68, 17], ![-520, -266, -15, 4]]]
 hmul := by decide
 f :=  ![![![![51645246, -138565452, -23621805, -399927], ![-123361935, 355210311, 6686855, 0]], ![![111884, 0, 0, 0], ![85, 0, 0, 0]]], ![![![-1683312864, 4516368480, 769923326, 13035120], ![4020829578, -11577638191, -217949668, 0]], ![![-3646720, 0, 0, 0], ![-2770, 0, 0, 0]]]]
 g :=  ![![![![17, 0, 0, 0], ![0, 0, 0, 0]], ![![7, 1, 0, 0], ![0, 0, 0, 0]]], ![![![425, 216, 11, -3], ![17, 0, 0, 0]], ![![2, 1, 0, 0], ![1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulI17N1 : IdealMulEqCertificate timesTableO (I17N0*I17N1) I17N1
  ![![17, 0, 0, 0], ![-554, -283, -15, 4]] ![![17, 0, 0, 0], ![7, 1, 0, 0]]
  ![![17, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI17N0
 hI2 := rfl
 M :=  ![![![289, 0, 0, 0], ![119, 17, 0, 0]], ![![-9418, -4811, -255, 68], ![-2346, -1207, -68, 17]]]
 hmul := by decide
 f :=  ![![![![850015, -2283063, -389208, -6583], ![-2030374, 5852101, 110189, 0]], ![![0, 0, 0, 0], ![1722, 0, 0, 0]]]]
 g :=  ![![![![17, 0, 0, 0]], ![![7, 1, 0, 0]]], ![![![-554, -283, -15, 4]], ![![-138, -71, -4, 1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC17 : IsPrimesAboveP 17 ![I17N0, I17N1, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI17N1, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}
def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0], ![-131, -67, -4, 1]] i)))

def SI19N0: IdealEqSpanCertificate timesTableO I19N0
 ![![19, 0, 0, 0], ![-131, -67, -4, 1]] 
 ![![19, 0, 0, 0], ![0, 19, 0, 0], ![9, 0, 1, 0], ![0, 9, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![19, 0, 0, 0], ![0, 19, 0, 0], ![0, 0, 19, 0], ![0, 0, 0, 19]], ![![-131, -67, -4, 1], ![383, 201, 13, -3], ![-1149, -613, -39, 10], ![3830, 2171, 187, -29]]]
  hmulB := by decide
  f := ![![![688, 1139, 222, -17], ![-8455, -2926, 0, 0]], ![![-21, -66, -15, 1], ![608, 209, 0, 0]], ![![319, 536, 105, -8], ![-4006, -1386, 0, 0]], ![![59, 4, -5, 0], ![298, 99, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-9, 0, 19, 0], ![0, -9, 0, 19]], ![![-5, -4, -4, 1], ![14, 12, 13, -3], ![-42, -37, -39, 10], ![113, 128, 187, -29]]]
  hle1 := by decide
  hle2 := by decide

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI19N0)

def MemCI19N0 : IdealMemCertificate B I19N0
  ![![19, 0, 0, 0], ![0, 19, 0, 0], ![9, 0, 1, 0], ![0, 9, 0, 1]] ![493721, 412628, 96052, 3353] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI19N0
 g := ![-19513, 20129, 96052, 3353]
 hmem := by decide

def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [7, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 18], [0, 1]]
 g := ![![[9, 11], [6, 1], [17], [1]],![[0, 8], [0, 18], [17], [1]]]
 h' := ![![[13, 18], [15, 12], [6, 1], [12, 13], [0, 1]],![[0, 1], [0, 7], [0, 18], [10, 6], [13, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [4, 14]]
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
  P := [7, 6, 1]
  f := ofList [7, 6, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P19P0
  hneq := by decide
  hlen := by decide
  c := ![493721, 412628, 96052, 3353]
  a := ![3, 0, 7, -4]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI19N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI19N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal.isPrime PI19N0
def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0], ![-132, -67, -4, 1]] i)))

def SI19N1: IdealEqSpanCertificate timesTableO I19N1
 ![![19, 0, 0, 0], ![-132, -67, -4, 1]] 
 ![![19, 0, 0, 0], ![0, 19, 0, 0], ![6, 18, 1, 0], ![6, 5, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![19, 0, 0, 0], ![0, 19, 0, 0], ![0, 0, 19, 0], ![0, 0, 0, 19]], ![![-132, -67, -4, 1], ![383, 200, 13, -3], ![-1149, -613, -40, 10], ![3830, 2171, 187, -30]]]
  hmulB := by decide
  f := ![![![415, 714, 138, -12], ![-4902, -1710, 0, 0]], ![![-2, -56, -14, 1], ![551, 190, 0, 0]], ![![150, 183, 31, -3], ![-1023, -360, 0, 0]], ![![200, 246, 42, -4], ![-1393, -490, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-6, -18, 19, 0], ![-6, -5, 0, 19]], ![![-6, 0, -4, 1], ![17, -1, 13, -3], ![-51, 3, -40, 10], ![152, -55, 187, -30]]]
  hle1 := by decide
  hle2 := by decide

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI19N1)

def MemCI19N1 : IdealMemCertificate B I19N1
  ![![19, 0, 0, 0], ![0, 19, 0, 0], ![6, 18, 1, 0], ![6, 5, 0, 1]] ![29883, 25525, 6304, 320] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI19N1
 g := ![-519, -4713, 6304, 320]
 hmem := by decide

def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [9, 12, 1] where
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
 g := ![![[14, 17], [8, 7], [11], [1]],![[0, 2], [0, 12], [11], [1]]]
 h' := ![![[7, 18], [4, 13], [1, 8], [10, 7], [0, 1]],![[0, 1], [0, 6], [0, 11], [2, 12], [7, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [2, 13]]
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
  P := [9, 12, 1]
  f := ofList [9, 12, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P19P1
  hneq := by decide
  hlen := by decide
  c := ![29883, 25525, 6304, 320]
  a := ![0, 1, 1, -1]
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
  ![![19, 0, 0, 0], ![-131, -67, -4, 1]] ![![19, 0, 0, 0], ![-132, -67, -4, 1]]
  ![![19, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![361, 0, 0, 0], ![-2508, -1273, -76, 19]], ![![-2489, -1273, -76, 19], ![57, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![200967934, 387002360, 77049664, -6535944], ![-2777455151, -967211872, 0, 0]], ![![2471, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![19, 0, 0, 0]], ![![-132, -67, -4, 1]]], ![![![-131, -67, -4, 1]], ![![3, 0, 0, 0]]]]
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
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}
def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0], ![-131, -64, -4, 1]] i)))

def SI23N0: IdealEqSpanCertificate timesTableO I23N0
 ![![23, 0, 0, 0], ![-131, -64, -4, 1]] 
 ![![23, 0, 0, 0], ![0, 23, 0, 0], ![9, 8, 1, 0], ![20, 14, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![23, 0, 0, 0], ![0, 23, 0, 0], ![0, 0, 23, 0], ![0, 0, 0, 23]], ![![-131, -64, -4, 1], ![383, 201, 16, -3], ![-1149, -613, -39, 13], ![4979, 3167, 427, -26]]]
  hmulB := by decide
  f := ![![![205, 544, 144, -4], ![-2116, -736, 0, 0]], ![![80, -71, -32, 0], ![552, 184, 0, 0]], ![![165, 216, 47, -2], ![-626, -224, 0, 0]], ![![170, 402, 104, -3], ![-1514, -528, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-9, -8, 23, 0], ![-20, -14, 0, 23]], ![![-5, -2, -4, 1], ![13, 5, 16, -3], ![-46, -21, -39, 13], ![72, 5, 427, -26]]]
  hle1 := by decide
  hle2 := by decide

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI23N0)

def MemCI23N0 : IdealMemCertificate B I23N0
  ![![23, 0, 0, 0], ![0, 23, 0, 0], ![9, 8, 1, 0], ![20, 14, 0, 1]] ![6135, 5315, 1293, 40] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI23N0
 g := ![-274, -243, 1293, 40]
 hmem := by decide

def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [9, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 22], [0, 1]]
 g := ![![[8, 18], [18, 6], [4, 9], [1]],![[0, 5], [0, 17], [0, 14], [1]]]
 h' := ![![[20, 22], [22, 15], [10, 11], [14, 20], [0, 1]],![[0, 1], [0, 8], [0, 12], [0, 3], [20, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [18, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal O 23 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I23N0
  hcard := NI23N0
  P := [9, 3, 1]
  f := ofList [9, 3, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P23P0
  hneq := by decide
  hlen := by decide
  c := ![6135, 5315, 1293, 40]
  a := ![-1, 3, 4, 0]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI23N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI23N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal.isPrime PI23N0
def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0], ![-131, -62, -4, 1]] i)))

def SI23N1: IdealEqSpanCertificate timesTableO I23N1
 ![![23, 0, 0, 0], ![-131, -62, -4, 1]] 
 ![![23, 0, 0, 0], ![0, 23, 0, 0], ![6, 14, 1, 0], ![8, 17, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![23, 0, 0, 0], ![0, 23, 0, 0], ![0, 0, 23, 0], ![0, 0, 0, 23]], ![![-131, -62, -4, 1], ![383, 201, 18, -3], ![-1149, -613, -39, 15], ![5745, 3831, 587, -24]]]
  hmulB := by decide
  f := ![![![143, 304, 80, -2], ![-782, -276, 0, 0]], ![![-11, -241, -76, 1], ![805, 276, 0, 0]], ![![42, -62, -25, 0], ![288, 96, 0, 0]], ![![53, -67, -28, 0], ![325, 108, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-6, -14, 23, 0], ![-8, -17, 0, 23]], ![![-5, -1, -4, 1], ![13, 0, 18, -3], ![-45, -14, -39, 15], ![105, -173, 587, -24]]]
  hle1 := by decide
  hle2 := by decide

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI23N1)

def MemCI23N1 : IdealMemCertificate B I23N1
  ![![23, 0, 0, 0], ![0, 23, 0, 0], ![6, 14, 1, 0], ![8, 17, 0, 1]] ![1525499, 1341124, 353676, 24178] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI23N1
 g := ![-34347, -174842, 353676, 24178]
 hmem := by decide

def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [12, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 22], [0, 1]]
 g := ![![[6, 2], [7, 3], [22, 9], [1]],![[0, 21], [21, 20], [18, 14], [1]]]
 h' := ![![[20, 22], [8, 18], [12, 16], [11, 20], [0, 1]],![[0, 1], [0, 5], [10, 7], [20, 3], [20, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [16, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal O 23 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I23N1
  hcard := NI23N1
  P := [12, 3, 1]
  f := ofList [12, 3, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P23P1
  hneq := by decide
  hlen := by decide
  c := ![1525499, 1341124, 353676, 24178]
  a := ![-1, 1, 0, 7]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI23N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI23N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal.isPrime PI23N1
def MulI23N0 : IdealMulEqCertificate timesTableO (I23N0) I23N1
  ![![23, 0, 0, 0], ![-131, -64, -4, 1]] ![![23, 0, 0, 0], ![-131, -62, -4, 1]]
  ![![23, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![529, 0, 0, 0], ![-3013, -1426, -92, 23]], ![![-3013, -1472, -92, 23], ![2990, 1541, 115, -23]]]
 hmul := by decide
 f :=  ![![![![4256387162, 48397747145, 14951038476, -211923375], ![-157315787300, -54062822394, 0, 0]], ![![1557680, -21, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![23, 0, 0, 0]], ![![-131, -62, -4, 1]]], ![![![-131, -64, -4, 1]], ![![130, 67, 5, -1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC23 : IsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI23N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}
def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0], ![-136, -80, -4, 1]] i)))

def SI29N0: IdealEqSpanCertificate timesTableO I29N0
 ![![29, 0, 0, 0], ![-136, -80, -4, 1]] 
 ![![29, 0, 0, 0], ![0, 29, 0, 0], ![19, 23, 1, 0], ![27, 12, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![29, 0, 0, 0], ![0, 29, 0, 0], ![0, 0, 29, 0], ![0, 0, 0, 29]], ![![-136, -80, -4, 1], ![383, 196, 0, -3], ![-1149, -613, -44, -3], ![-1149, -2145, -853, -47]]]
  hmulB := by decide
  f := ![![![1457, -784, -588, -21], ![-4263, -1624, 0, 0]], ![![-330, 217, 148, 5], ![1073, 406, 0, 0]], ![![721, -325, -267, -10], ![-1936, -742, 0, 0]], ![![1295, -596, -484, -18], ![-3509, -1344, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-19, -23, 29, 0], ![-27, -12, 0, 29]], ![![-3, 0, -4, 1], ![16, 8, 0, -3], ![-8, 15, -44, -3], ![563, 622, -853, -47]]]
  hle1 := by decide
  hle2 := by decide

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI29N0)

def MemCI29N0 : IdealMemCertificate B I29N0
  ![![29, 0, 0, 0], ![0, 29, 0, 0], ![19, 23, 1, 0], ![27, 12, 0, 1]] ![11924, 10300, 3820, 458] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI29N0
 g := ![-2518, -2864, 3820, 458]
 hmem := by decide

def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [25, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 28], [0, 1]]
 g := ![![[19, 7], [23], [28, 23], [18, 1]],![[0, 22], [23], [7, 6], [7, 28]]]
 h' := ![![[18, 28], [21, 23], [25, 9], [14, 9], [0, 1]],![[0, 1], [0, 6], [13, 20], [2, 20], [18, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [5, 22]]
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
  P := [25, 11, 1]
  f := ofList [25, 11, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P29P0
  hneq := by decide
  hlen := by decide
  c := ![11924, 10300, 3820, 458]
  a := ![2, -25, 0, 1]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI29N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI29N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal.isPrime PI29N0
def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0], ![-133, -56, -4, 1]] i)))

def SI29N1: IdealEqSpanCertificate timesTableO I29N1
 ![![29, 0, 0, 0], ![-133, -56, -4, 1]] 
 ![![29, 0, 0, 0], ![0, 29, 0, 0], ![18, 5, 1, 0], ![26, 22, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![29, 0, 0, 0], ![0, 29, 0, 0], ![0, 0, 29, 0], ![0, 0, 0, 29]], ![![-133, -56, -4, 1], ![383, 199, 24, -3], ![-1149, -613, -41, 21], ![8043, 5823, 1067, -20]]]
  hmulB := by decide
  f := ![![![289, 4461, 1444, -16], ![-9541, -3335, 0, 0]], ![![-31, -880, -288, 3], ![1914, 667, 0, 0]], ![![119, 2594, 845, -9], ![-5604, -1955, 0, 0]], ![![231, 3330, 1076, -12], ![-7103, -2484, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-18, -5, 29, 0], ![-26, -22, 0, 29]], ![![-3, -2, -4, 1], ![1, 5, 24, -3], ![-33, -30, -41, 21], ![-367, 32, 1067, -20]]]
  hle1 := by decide
  hle2 := by decide

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 841 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI29N1)

def MemCI29N1 : IdealMemCertificate B I29N1
  ![![29, 0, 0, 0], ![0, 29, 0, 0], ![18, 5, 1, 0], ![26, 22, 0, 1]] ![47140, 45836, 14506, 1452] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI29N1
 g := ![-8680, -2022, 14506, 1452]
 hmem := by decide

def P29P1 : CertificateIrreducibleZModOfList' 29 2 2 4 [25, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 28], [0, 1]]
 g := ![![[6, 7], [7], [], [24, 1]],![[0, 22], [7], [], [19, 28]]]
 h' := ![![[24, 28], [28, 23], [0, 23], [9], [0, 1]],![[0, 1], [0, 6], [1, 6], [9], [24, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [2, 24]]
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
  P := [25, 5, 1]
  f := ofList [25, 5, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P29P1
  hneq := by decide
  hlen := by decide
  c := ![47140, 45836, 14506, 1452]
  a := ![1, 3, -6, -1]
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
  ![![29, 0, 0, 0], ![-136, -80, -4, 1]] ![![29, 0, 0, 0], ![-133, -56, -4, 1]]
  ![![29, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![841, 0, 0, 0], ![-3857, -1624, -116, 29]], ![![-3944, -2320, -116, 29], ![87, -29, -145, 0]]]
 hmul := by decide
 f :=  ![![![![39901652494398, 966385915163141, 315268498737048, -3327177109557], ![-2092721800101036, -729736159905575, 0, 0]], ![![1456511184, -16760, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![29, 0, 0, 0]], ![![-133, -56, -4, 1]]], ![![![-136, -80, -4, 1]], ![![3, -1, -5, 0]]]]
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
