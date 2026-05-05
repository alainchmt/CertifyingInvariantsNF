
import IdealArithmetic.Examples.NF2_0_231_1.RI2_0_231_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import IdealArithmetic.IdealArithmetic.CertifyPrimeIdeal

open Classical Polynomial

noncomputable section 
instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0], ![0, 1]] i)))

def SI2N0: IdealEqSpanCertificate timesTableO I2N0
 ![![2, 0], ![0, 1]] 
 ![![2, 0], ![0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![2, 0], ![0, 2]], ![![0, 1], ![-58, 1]]]
  hmulB := by decide
  f := ![![![1, 0], ![0, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![0, 2]], ![![0, 1], ![-29, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0], ![1, 1]] i)))

def SI2N1: IdealEqSpanCertificate timesTableO I2N1
 ![![2, 0], ![1, 1]] 
 ![![2, 0], ![1, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![2, 0], ![0, 2]], ![![1, 1], ![-58, 2]]]
  hmulB := by decide
  f := ![![![0, -1], ![2, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-1, 2]], ![![0, 1], ![-30, 2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulEqCertificate timesTableO (I2N0) I2N1
  ![![2, 0], ![0, 1]] ![![2, 0], ![1, 1]]
  ![![2, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0], ![2, 2]], ![![0, 2], ![-58, 2]]]
 hmul := by decide
 f :=  ![![![![0, 0], ![1, 0]], ![![-1, 0], ![0, 0]]]]
 g :=  ![![![![2, 0]], ![![1, 1]]], ![![![0, 1]], ![![-29, 1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC2 : IsPrimesAboveP 2 ![I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI2N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0], ![1, 1]] i)))

def SI3N0: IdealEqSpanCertificate timesTableO I3N0
 ![![3, 0], ![1, 1]] 
 ![![3, 0], ![1, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, 0], ![0, 3]], ![![1, 1], ![-58, 2]]]
  hmulB := by decide
  f := ![![![0, -1], ![3, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-1, 3]], ![![0, 1], ![-20, 2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulEqCertificate timesTableO (I3N0) I3N0
  ![![3, 0], ![1, 1]] ![![3, 0], ![1, 1]]
  ![![3, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![9, 0], ![3, 3]], ![![3, 3], ![-57, 3]]]
 hmul := by decide
 f :=  ![![![![6, -1], ![2, 0]], ![![0, 0], ![1, 0]]]]
 g :=  ![![![![3, 0]], ![![1, 1]]], ![![![1, 1]], ![![-19, 1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC3 : IsPrimesAboveP 3 ![I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI3N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}
def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0], ![1, 1]] i)))

def SI5N0: IdealEqSpanCertificate timesTableO I5N0
 ![![5, 0], ![1, 1]] 
 ![![5, 0], ![1, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![5, 0], ![0, 5]], ![![1, 1], ![-58, 2]]]
  hmulB := by decide
  f := ![![![0, -1], ![5, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-1, 5]], ![![0, 1], ![-12, 2]]]
  hle1 := by decide
  hle2 := by decide

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0], ![3, 1]] i)))

def SI5N1: IdealEqSpanCertificate timesTableO I5N1
 ![![5, 0], ![3, 1]] 
 ![![5, 0], ![3, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![5, 0], ![0, 5]], ![![3, 1], ![-58, 4]]]
  hmulB := by decide
  f := ![![![-2, -1], ![5, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-3, 5]], ![![0, 1], ![-14, 4]]]
  hle1 := by decide
  hle2 := by decide

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulEqCertificate timesTableO (I5N0) I5N1
  ![![5, 0], ![1, 1]] ![![5, 0], ![3, 1]]
  ![![5, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![25, 0], ![15, 5]], ![![5, 5], ![-55, 5]]]
 hmul := by decide
 f :=  ![![![![1, 0], ![-2, 0]], ![![2, 0], ![0, 0]]]]
 g :=  ![![![![5, 0]], ![![3, 1]]], ![![![1, 1]], ![![-11, 1]]]]
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
def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0], ![3, 1]] i)))

def SI7N0: IdealEqSpanCertificate timesTableO I7N0
 ![![7, 0], ![3, 1]] 
 ![![7, 0], ![3, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![7, 0], ![0, 7]], ![![3, 1], ![-58, 4]]]
  hmulB := by decide
  f := ![![![-2, -1], ![7, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-3, 7]], ![![0, 1], ![-10, 4]]]
  hle1 := by decide
  hle2 := by decide

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0
def MulI7N0 : IdealMulEqCertificate timesTableO (I7N0) I7N0
  ![![7, 0], ![3, 1]] ![![7, 0], ![3, 1]]
  ![![7, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![49, 0], ![21, 7]], ![![21, 7], ![-49, 7]]]
 hmul := by decide
 f :=  ![![![![205, -46], ![82, 0]], ![![0, 0], ![240, 0]]]]
 g :=  ![![![![7, 0]], ![![3, 1]]], ![![![3, 1]], ![![-7, 1]]]]
 hle1 := by decide
 hle2 := by decide

def PBC7 : IsPrimesAboveP 7 ![I7N0, I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N0
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulI7N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
