
import IdealArithmetic.Examples.NF4_0_76176_2.RI4_0_76176_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic

set_option linter.all false

open Classical Polynomial

noncomputable section 
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}
def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0], ![7, 0, 1, -2]] i)))

def SI31N0: IdealEqSpanCertificate timesTableO I31N0
 ![![31, 0, 0, 0], ![7, 0, 1, -2]] 
 ![![31, 0, 0, 0], ![0, 31, 0, 0], ![30, 15, 1, 0], ![27, 23, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![31, 0, 0, 0], ![0, 31, 0, 0], ![0, 0, 31, 0], ![0, 0, 0, 31]], ![![7, 0, 1, -2], ![4, 8, 0, -1], ![-6, 12, 16, -18], ![0, 6, 4, -1]]]
  hmulB := by decide
  f := ![![![-6, 0, -1, 2], ![31, 0, 0, 0]], ![![-16, -31, 0, 4], ![0, 124, 0, 0]], ![![-7, -15, 0, 2], ![1, 60, 0, 0]], ![![-11, -23, 0, 3], ![0, 92, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-30, -15, 31, 0], ![-27, -23, 0, 31]], ![![1, 1, 1, -2], ![1, 1, 0, -1], ![0, 6, 16, -18], ![-3, -1, 4, -1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI31N0)

def MemCI31N0 : IdealMemCertificate B I31N0
  ![![31, 0, 0, 0], ![0, 31, 0, 0], ![30, 15, 1, 0], ![27, 23, 0, 1]] ![-740, 116, 351, -980] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI31N0
 g := ![490, 561, 351, -980]
 hmem := by decide

def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [20, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 30], [0, 1]]
 g := ![![[7, 14], [29, 28], [29, 20], [15, 1]],![[0, 17], [15, 3], [19, 11], [30, 30]]]
 h' := ![![[15, 30], [9, 18], [9, 11], [10, 19], [0, 1]],![[0, 1], [0, 13], [19, 20], [16, 12], [15, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [14, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal O 31 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I31N0
  hcard := NI31N0
  P := [20, 16, 1]
  f := ofList [20, 16, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P31P0
  hneq := by decide
  hlen := by decide
  c := ![-740, 116, 351, -980]
  a := ![-16, 14, 15, -35]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI31N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI31N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal.isPrime PI31N0
def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0], ![-8, 0, 1, -2]] i)))

def SI31N1: IdealEqSpanCertificate timesTableO I31N1
 ![![31, 0, 0, 0], ![-8, 0, 1, -2]] 
 ![![31, 0, 0, 0], ![0, 31, 0, 0], ![15, 14, 1, 0], ![27, 7, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![31, 0, 0, 0], ![0, 31, 0, 0], ![0, 0, 31, 0], ![0, 0, 0, 31]], ![![-8, 0, 1, -2], ![4, -7, 0, -1], ![-6, 12, 1, -18], ![0, 6, 4, -16]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0], ![0, 0, 0, 0]], ![![36, -62, 0, -9], ![0, -279, 0, 0]], ![![17, -28, 0, -4], ![1, -126, 0, 0]], ![![9, -14, 0, -2], ![0, -63, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-15, -14, 31, 0], ![-27, -7, 0, 31]], ![![1, 0, 1, -2], ![1, 0, 0, -1], ![15, 4, 1, -18], ![12, 2, 4, -16]]]
  hle1 := by decide
  hle2 := by decide

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI31N1)

def MemCI31N1 : IdealMemCertificate B I31N1
  ![![31, 0, 0, 0], ![0, 31, 0, 0], ![15, 14, 1, 0], ![27, 7, 0, 1]] ![-215179, -100356, -163778, 287547] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI31N1
 g := ![-178138, 5797, -163778, 287547]
 hmem := by decide

def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [21, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 30], [0, 1]]
 g := ![![[7, 9], [14, 7], [3, 20], [8, 1]],![[17, 22], [8, 24], [8, 11], [16, 30]]]
 h' := ![![[8, 30], [16, 28], [30, 21], [18, 12], [0, 1]],![[0, 1], [23, 3], [12, 10], [21, 19], [8, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [12, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : CertifiedPrimeIdeal O 31 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I31N1
  hcard := NI31N1
  P := [21, 23, 1]
  f := ofList [21, 23, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P31P1
  hneq := by decide
  hlen := by decide
  c := ![-215179, -100356, -163778, 287547]
  a := ![-6, 8, -60, -13]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI31N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI31N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := CertifiedPrimeIdeal.isPrime PI31N1
def MulI31N0 : IdealMulEqCertificate timesTableO (I31N0) I31N1
  ![![31, 0, 0, 0], ![7, 0, 1, -2]] ![![31, 0, 0, 0], ![-8, 0, 1, -2]]
  ![![31, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![961, 0, 0, 0], ![-248, 0, 31, -62]], ![![217, 0, 31, -62], ![-62, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![92, 0, 13, -26], ![2, 0, 0, 0]], ![![-405, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![31, 0, 0, 0]], ![![-8, 0, 1, -2]]], ![![![7, 0, 1, -2]], ![![-2, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC31 : IsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI31N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 2, 2, -4]] i)))

def SI37N0: IdealEqSpanCertificate timesTableO I37N0
 ![![5, 2, 2, -4]] 
 ![![37, 0, 0, 0], ![0, 37, 0, 0], ![24, 6, 1, 0], ![20, 21, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![5, 2, 2, -4], ![8, 7, 2, -2], ![20, -6, -9, 34], ![12, -4, -8, 25]]]
  hmulB := by decide
  f := ![![![9, -2, -2, 4]], ![![-8, 7, -2, 2]], ![![4, 0, -1, 2]], ![![0, 3, -2, 3]]]
  g := ![![![1, 2, 2, -4], ![0, 1, 2, -2], ![-12, -18, -9, 34], ![-8, -13, -8, 25]]]
  hle1 := by decide
  hle2 := by decide

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI37N0)

def MemCI37N0 : IdealMemCertificate B I37N0
  ![![37, 0, 0, 0], ![0, 37, 0, 0], ![24, 6, 1, 0], ![20, 21, 0, 1]] ![-73, 1120, 3156, -8155] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI37N0
 g := ![2359, 4147, 3156, -8155]
 hmem := by decide

def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [33, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 36], [0, 1]]
 g := ![![[7, 9], [10], [30, 21], [7], [1]],![[0, 28], [10], [26, 16], [7], [1]]]
 h' := ![![[28, 36], [10, 34], [9, 11], [7, 13], [4, 28], [0, 1]],![[0, 1], [0, 3], [21, 26], [1, 24], [11, 9], [28, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [35, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal O 37 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I37N0
  hcard := NI37N0
  P := [33, 9, 1]
  f := ofList [33, 9, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P37P0
  hneq := by decide
  hlen := by decide
  c := ![-73, 1120, 3156, -8155]
  a := ![-59, 56, 59, -129]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI37N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI37N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal.isPrime PI37N0
def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -2, -2, 4]] i)))

def SI37N1: IdealEqSpanCertificate timesTableO I37N1
 ![![9, -2, -2, 4]] 
 ![![37, 0, 0, 0], ![0, 37, 0, 0], ![31, 29, 1, 0], ![27, 14, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![9, -2, -2, 4], ![-8, 7, -2, 2], ![-20, 6, 23, -34], ![-12, 4, 8, -11]]]
  hmulB := by decide
  f := ![![![5, 2, 2, -4]], ![![8, 7, 2, -2]], ![![11, 7, 3, -4]], ![![7, 4, 2, -3]]]
  g := ![![![-1, 0, -2, 4], ![0, 1, -2, 2], ![5, -5, 23, -34], ![1, -2, 8, -11]]]
  hle1 := by decide
  hle2 := by decide

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 1369 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI37N1)

def MemCI37N1 : IdealMemCertificate B I37N1
  ![![37, 0, 0, 0], ![0, 37, 0, 0], ![31, 29, 1, 0], ![27, 14, 0, 1]] ![824, -248, -233, 420] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI37N1
 g := ![-89, 17, -233, 420]
 hmem := by decide

def P37P1 : CertificateIrreducibleZModOfList' 37 2 2 5 [8, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 36], [0, 1]]
 g := ![![[21, 12], [26], [15, 34], [30], [1]],![[3, 25], [26], [1, 3], [30], [1]]]
 h' := ![![[17, 36], [21, 30], [28, 27], [9, 16], [29, 17], [0, 1]],![[0, 1], [13, 7], [6, 10], [22, 21], [22, 20], [17, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [10, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N1 : CertifiedPrimeIdeal O 37 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I37N1
  hcard := NI37N1
  P := [8, 20, 1]
  f := ofList [8, 20, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P37P1
  hneq := by decide
  hlen := by decide
  c := ![824, -248, -233, 420]
  a := ![16, -16, -17, 35]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI37N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI37N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := CertifiedPrimeIdeal.isPrime PI37N1
def MulI37N0 : IdealMulEqCertificate timesTableO (I37N0) I37N1
  ![![5, 2, 2, -4]] ![![9, -2, -2, 4]]
  ![![37, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![37, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![1, 0, 0, 0]]]]
 g :=  ![![![![1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC37 : IsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI37N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}
def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0], ![15, 0, 1, -2]] i)))

def SI41N0: IdealEqSpanCertificate timesTableO I41N0
 ![![41, 0, 0, 0], ![15, 0, 1, -2]] 
 ![![41, 0, 0, 0], ![0, 41, 0, 0], ![7, 9, 1, 0], ![37, 25, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![41, 0, 0, 0], ![0, 41, 0, 0], ![0, 0, 41, 0], ![0, 0, 0, 41]], ![![15, 0, 1, -2], ![4, 16, 0, -1], ![-6, 12, 24, -18], ![0, 6, 4, 7]]]
  hmulB := by decide
  f := ![![![-14, 0, -1, 2], ![41, 0, 0, 0]], ![![-72, -287, 0, 18], ![0, 738, 0, 0]], ![![-16, -63, 0, 4], ![1, 162, 0, 0]], ![![-43, -175, 0, 11], ![0, 450, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-7, -9, 41, 0], ![-37, -25, 0, 41]], ![![2, 1, 1, -2], ![1, 1, 0, -1], ![12, 6, 24, -18], ![-7, -5, 4, 7]]]
  hle1 := by decide
  hle2 := by decide

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI41N0)

def MemCI41N0 : IdealMemCertificate B I41N0
  ![![41, 0, 0, 0], ![0, 41, 0, 0], ![7, 9, 1, 0], ![37, 25, 0, 1]] ![-125545, -23532, 39383, -128084] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI41N0
 g := ![105802, 68881, 39383, -128084]
 hmem := by decide

def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [24, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 40], [0, 1]]
 g := ![![[18, 23], [10], [32], [2, 33], [1]],![[4, 18], [10], [32], [14, 8], [1]]]
 h' := ![![[19, 40], [39, 33], [19, 25], [34, 27], [17, 19], [0, 1]],![[0, 1], [10, 8], [2, 16], [14, 14], [9, 22], [19, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [1, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal O 41 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I41N0
  hcard := NI41N0
  P := [24, 22, 1]
  f := ofList [24, 22, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P41P0
  hneq := by decide
  hlen := by decide
  c := ![-125545, -23532, 39383, -128084]
  a := ![257, -234, -239, 561]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI41N0
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI41N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal.isPrime PI41N0
def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0], ![-16, 0, 1, -2]] i)))

def SI41N1: IdealEqSpanCertificate timesTableO I41N1
 ![![41, 0, 0, 0], ![-16, 0, 1, -2]] 
 ![![41, 0, 0, 0], ![0, 41, 0, 0], ![17, 30, 1, 0], ![37, 15, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![41, 0, 0, 0], ![0, 41, 0, 0], ![0, 0, 41, 0], ![0, 0, 0, 41]], ![![-16, 0, 1, -2], ![4, -15, 0, -1], ![-6, 12, -7, -18], ![0, 6, 4, -24]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0], ![0, 0, 0, 0]], ![![44, -164, 0, -11], ![0, -451, 0, 0]], ![![33, -120, 0, -8], ![1, -330, 0, 0]], ![![17, -60, 0, -4], ![0, -165, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-17, -30, 41, 0], ![-37, -15, 0, 41]], ![![1, 0, 1, -2], ![1, 0, 0, -1], ![19, 12, -7, -18], ![20, 6, 4, -24]]]
  hle1 := by decide
  hle2 := by decide

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI41N1)

def MemCI41N1 : IdealMemCertificate B I41N1
  ![![41, 0, 0, 0], ![0, 41, 0, 0], ![17, 30, 1, 0], ![37, 15, 0, 1]] ![107, 40, 301, -818] where
 hieq := ideal_eq_of_IdealEqSpanCertificate SI41N1
 g := ![616, 80, 301, -818]
 hmem := by decide

def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [30, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 40], [0, 1]]
 g := ![![[11, 9], [37], [37], [30, 4], [1]],![[34, 32], [37], [37], [22, 37], [1]]]
 h' := ![![[39, 40], [39, 3], [1, 18], [2, 23], [11, 39], [0, 1]],![[0, 1], [33, 38], [6, 23], [38, 18], [15, 2], [39, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [29, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal O 41 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I41N1
  hcard := NI41N1
  P := [30, 2, 1]
  f := ofList [30, 2, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P41P1
  hneq := by decide
  hlen := by decide
  c := ![107, 40, 301, -818]
  a := ![21, -20, -21, 46]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate _ _ _ _ MemCI41N1
  hpmem := by 
    erw [← Submodule.mem_carrier (R := O), ideal_eq_of_IdealEqSpanCertificate SI41N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num

        
lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal.isPrime PI41N1
def MulI41N0 : IdealMulEqCertificate timesTableO (I41N0) I41N1
  ![![41, 0, 0, 0], ![15, 0, 1, -2]] ![![41, 0, 0, 0], ![-16, 0, 1, -2]]
  ![![41, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![1681, 0, 0, 0], ![-656, 0, 41, -82]], ![![615, 0, 41, -82], ![-246, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![12200, 0, 1045, -2090], ![-4596, 0, 0, 0]], ![![-38249, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![41, 0, 0, 0]], ![![-16, 0, 1, -2]]], ![![![15, 0, 1, -2]], ![![-6, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC41 : IsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI41N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl

