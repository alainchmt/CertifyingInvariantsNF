
import IdealArithmetic.Examples.NF4_0_76176_2.PrimesBelow4_0_76176_2F0

open Classical Polynomial

noncomputable section 
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}
def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0], ![8, 0, -1, 2]] i)))

def SI31N0: IdealEqSpanCertificate O ℤ timesTableO I31N0
 ![![31, 0, 0, 0], ![8, 0, -1, 2]] 
 ![![31, 0, 0, 0], ![0, 31, 0, 0], ![15, 14, 1, 0], ![27, 7, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![31, 0, 0, 0], ![0, 31, 0, 0], ![0, 0, 31, 0], ![0, 0, 0, 31]], ![![8, 0, -1, 2], ![-4, 7, 0, 1], ![6, -12, -1, 18], ![0, -6, -4, 16]]]
  hmulB := by decide
  f := ![![![-7, 0, 1, -2], ![31, 0, 0, 0]], ![![28, -62, 1, -11], ![31, 279, 0, 0]], ![![9, -28, 1, -6], ![30, 126, 0, 0]], ![![1, -14, 1, -4], ![31, 63, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-15, -14, 31, 0], ![-27, -7, 0, 31]], ![![-1, 0, -1, 2], ![-1, 0, 0, 1], ![-15, -4, -1, 18], ![-12, -2, -4, 16]]]
  hle1 := by decide
  hle2 := by decide

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI31N0)

def MemCI31N0 : IdealMemCertificate O ℤ B I31N0
  ![![31, 0, 0, 0], ![0, 31, 0, 0], ![15, 14, 1, 0], ![27, 7, 0, 1]] ![-839, 200, 441, -1190] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI31N0
 g := ![796, 76, 441, -1190]
 hmem := by decide

def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [17, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 30], [0, 1]]
 g := ![![[25, 28], [26, 19], [13, 4], [9, 1]],![[29, 3], [11, 12], [18, 27], [18, 30]]]
 h' := ![![[9, 30], [23, 20], [27, 22], [2, 2], [0, 1]],![[0, 1], [17, 11], [8, 9], [20, 29], [9, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [15, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : PrimeIdeal O 31 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I31N0
  hcard := NI31N0
  P := [17, 22, 1]
  f := ofList [17, 22, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P31P0
  hneq := by decide
  hlen := by decide
  c := ![-839, 200, 441, -1190]
  a := ![-16, 14, 15, -35]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI31N0
  hpmem := by 
    show  _ ∈ I31N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI31N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := PrimeIdeal_isPrime PI31N0
def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0], ![-7, 0, -1, 2]] i)))

def SI31N1: IdealEqSpanCertificate O ℤ timesTableO I31N1
 ![![31, 0, 0, 0], ![-7, 0, -1, 2]] 
 ![![31, 0, 0, 0], ![0, 31, 0, 0], ![30, 15, 1, 0], ![27, 23, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![31, 0, 0, 0], ![0, 31, 0, 0], ![0, 0, 31, 0], ![0, 0, 0, 31]], ![![-7, 0, -1, 2], ![-4, -8, 0, 1], ![6, -12, -16, 18], ![0, -6, -4, 1]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0], ![0, 0, 0, 0]], ![![-9, -31, 1, 2], ![31, -124, 0, 0]], ![![0, -15, 1, 0], ![30, -60, 0, 0]], ![![-4, -23, 1, 1], ![31, -92, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-30, -15, 31, 0], ![-27, -23, 0, 31]], ![![-1, -1, -1, 2], ![-1, -1, 0, 1], ![0, -6, -16, 18], ![3, 1, -4, 1]]]
  hle1 := by decide
  hle2 := by decide

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 961 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI31N1)

def MemCI31N1 : IdealMemCertificate O ℤ B I31N1
  ![![31, 0, 0, 0], ![0, 31, 0, 0], ![30, 15, 1, 0], ![27, 23, 0, 1]] ![-215156, -100380, -163598, 287586] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI31N1
 g := ![-99098, -137448, -163598, 287586]
 hmem := by decide

def P31P1 : CertificateIrreducibleZModOfList' 31 2 2 4 [26, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 30], [0, 1]]
 g := ![![[27, 19], [22, 9], [16, 4], [11, 1]],![[19, 12], [28, 22], [29, 27], [22, 30]]]
 h' := ![![[11, 30], [17, 22], [18, 28], [24, 2], [0, 1]],![[0, 1], [11, 9], [16, 3], [15, 29], [11, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [28, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N1 : PrimeIdeal O 31 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I31N1
  hcard := NI31N1
  P := [26, 20, 1]
  f := ofList [26, 20, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P31P1
  hneq := by decide
  hlen := by decide
  c := ![-215156, -100380, -163598, 287586]
  a := ![-6, 8, -60, -13]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI31N1
  hpmem := by 
    show  _ ∈ I31N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI31N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := PrimeIdeal_isPrime PI31N1
def MulI31N0 : IdealMulEqCertificate O ℤ timesTableO (I31N0) I31N1
  ![![31, 0, 0, 0], ![8, 0, -1, 2]] ![![31, 0, 0, 0], ![-7, 0, -1, 2]]
  ![![31, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![961, 0, 0, 0], ![-217, 0, -31, 62]], ![![248, 0, -31, 62], ![-62, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![33, 0, -4, 8], ![2, 0, 0, 0]], ![![-126, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![31, 0, 0, 0]], ![![-7, 0, -1, 2]]], ![![![8, 0, -1, 2]], ![![-2, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC31 : PrimesBelowPCertificate 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI31N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -2, -2, 4]] i)))

def SI37N0: IdealEqSpanCertificate O ℤ timesTableO I37N0
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

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI37N0)

def MemCI37N0 : IdealMemCertificate O ℤ B I37N0
  ![![37, 0, 0, 0], ![0, 37, 0, 0], ![31, 29, 1, 0], ![27, 14, 0, 1]] ![151, 896, 2920, -7639] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI37N0
 g := ![3132, 626, 2920, -7639]
 hmem := by decide

def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [21, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 36], [0, 1]]
 g := ![![[2, 30], [28], [26, 10], [25], [1]],![[0, 7], [28], [13, 27], [25], [1]]]
 h' := ![![[32, 36], [11, 17], [9, 19], [27, 11], [16, 32], [0, 1]],![[0, 1], [0, 20], [25, 18], [9, 26], [4, 5], [32, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [12, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : PrimeIdeal O 37 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I37N0
  hcard := NI37N0
  P := [21, 5, 1]
  f := ofList [21, 5, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P37P0
  hneq := by decide
  hlen := by decide
  c := ![151, 896, 2920, -7639]
  a := ![-59, 56, 59, -129]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI37N0
  hpmem := by 
    show  _ ∈ I37N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI37N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := PrimeIdeal_isPrime PI37N0
def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 2, 2, -4]] i)))

def SI37N1: IdealEqSpanCertificate O ℤ timesTableO I37N1
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

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 1369 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI37N1)

def MemCI37N1 : IdealMemCertificate O ℤ B I37N1
  ![![37, 0, 0, 0], ![0, 37, 0, 0], ![24, 6, 1, 0], ![20, 21, 0, 1]] ![901, -328, -318, 595] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI37N1
 g := ![-91, -295, -318, 595]
 hmem := by decide

def P37P1 : CertificateIrreducibleZModOfList' 37 2 2 5 [5, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 36], [0, 1]]
 g := ![![[5, 21], [21], [3, 30], [33], [1]],![[35, 16], [21], [30, 7], [33], [1]]]
 h' := ![![[12, 36], [9, 13], [22, 24], [8, 17], [32, 12], [0, 1]],![[0, 1], [17, 24], [14, 13], [27, 20], [28, 25], [12, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [18, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N1 : PrimeIdeal O 37 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I37N1
  hcard := NI37N1
  P := [5, 25, 1]
  f := ofList [5, 25, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P37P1
  hneq := by decide
  hlen := by decide
  c := ![901, -328, -318, 595]
  a := ![16, -16, -17, 35]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI37N1
  hpmem := by 
    show  _ ∈ I37N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI37N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := PrimeIdeal_isPrime PI37N1
def MulI37N0 : IdealMulEqCertificate O ℤ timesTableO (I37N0) I37N1
  ![![9, -2, -2, 4]] ![![5, 2, 2, -4]]
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

def PBC37 : PrimesBelowPCertificate 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI37N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}
def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0], ![16, 0, -1, 2]] i)))

def SI41N0: IdealEqSpanCertificate O ℤ timesTableO I41N0
 ![![41, 0, 0, 0], ![16, 0, -1, 2]] 
 ![![41, 0, 0, 0], ![0, 41, 0, 0], ![17, 30, 1, 0], ![37, 15, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![41, 0, 0, 0], ![0, 41, 0, 0], ![0, 0, 41, 0], ![0, 0, 0, 41]], ![![16, 0, -1, 2], ![-4, 15, 0, 1], ![6, -12, 7, 18], ![0, -6, -4, 24]]]
  hmulB := by decide
  f := ![![![-15, 0, 1, -2], ![41, 0, 0, 0]], ![![28, -164, 1, -13], ![41, 451, 0, 0]], ![![17, -120, 1, -10], ![40, 330, 0, 0]], ![![1, -60, 1, -6], ![41, 165, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-17, -30, 41, 0], ![-37, -15, 0, 41]], ![![-1, 0, -1, 2], ![-1, 0, 0, 1], ![-19, -12, 7, 18], ![-20, -6, -4, 24]]]
  hle1 := by decide
  hle2 := by decide

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI41N0)

def MemCI41N0 : IdealMemCertificate O ℤ B I41N0
  ![![41, 0, 0, 0], ![0, 41, 0, 0], ![17, 30, 1, 0], ![37, 15, 0, 1]] ![-124761, -24234, 38666, -126401] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI41N0
 g := ![94994, 17361, 38666, -126401]
 hmem := by decide

def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [37, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 40], [0, 1]]
 g := ![![[4, 10], [9], [18], [1, 10], [1]],![[0, 31], [9], [18], [38, 31], [1]]]
 h' := ![![[16, 40], [31, 16], [6, 3], [4, 31], [4, 16], [0, 1]],![[0, 1], [0, 25], [13, 38], [8, 10], [14, 25], [16, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [29, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : PrimeIdeal O 41 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I41N0
  hcard := NI41N0
  P := [37, 25, 1]
  f := ofList [37, 25, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P41P0
  hneq := by decide
  hlen := by decide
  c := ![-124761, -24234, 38666, -126401]
  a := ![257, -234, -239, 561]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI41N0
  hpmem := by 
    show  _ ∈ I41N0.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI41N0]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := PrimeIdeal_isPrime PI41N0
def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0], ![-15, 0, -1, 2]] i)))

def SI41N1: IdealEqSpanCertificate O ℤ timesTableO I41N1
 ![![41, 0, 0, 0], ![-15, 0, -1, 2]] 
 ![![41, 0, 0, 0], ![0, 41, 0, 0], ![7, 9, 1, 0], ![37, 25, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![41, 0, 0, 0], ![0, 41, 0, 0], ![0, 0, 41, 0], ![0, 0, 0, 41]], ![![-15, 0, -1, 2], ![-4, -16, 0, 1], ![6, -12, -24, 18], ![0, -6, -4, -7]]]
  hmulB := by decide
  f := ![![![1, 0, 0, 0], ![0, 0, 0, 0]], ![![-57, -287, 1, 16], ![41, -738, 0, 0]], ![![-1, -63, 1, 2], ![40, -162, 0, 0]], ![![-28, -175, 1, 9], ![41, -450, 0, 0]]]
  g := ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![-7, -9, 41, 0], ![-37, -25, 0, 41]], ![![-2, -1, -1, 2], ![-1, -1, 0, 1], ![-12, -6, -24, 18], ![7, 5, -4, -7]]]
  hle1 := by decide
  hle2 := by decide

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ SI41N1)

def MemCI41N1 : IdealMemCertificate O ℤ B I41N1
  ![![41, 0, 0, 0], ![0, 41, 0, 0], ![7, 9, 1, 0], ![37, 25, 0, 1]] ![487, -320, -77, 10] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ SI41N1
 g := ![16, 3, -77, 10]
 hmem := by decide

def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [32, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1] 
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 40], [0, 1]]
 g := ![![[16, 9], [23], [8], [4, 31], [1]],![[0, 32], [23], [8], [40, 10], [1]]]
 h' := ![![[21, 40], [22, 38], [15, 33], [36, 34], [9, 21], [0, 1]],![[0, 1], [0, 3], [11, 8], [12, 7], [40, 20], [21, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [15, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : PrimeIdeal O 41 where 
  r := 4
  n := 2
  hpos := by decide
  TT := timesTableO
  T := Table
  heq := timesTableT_eq_Table
  I := I41N1
  hcard := NI41N1
  P := [32, 20, 1]
  f := ofList [32, 20, 1]
  hfeq := by decide
  hirr := irreducible_ofList_ofCertificateIrreducibleZModOfList' P41P1
  hneq := by decide
  hlen := by decide
  c := ![487, -320, -77, 10]
  a := ![21, -20, -21, 46]
  z := ![1, 0, 0, 0]
  hBz := B_one_repr
  hpol := by decide
  hcmem := mem_of_certificate O ℤ _ _ _ _ MemCI41N1
  hpmem := by 
    show  _ ∈ I41N1.carrier
    rw [ideal_eq_of_IdealEqSpanCertificate O ℤ SI41N1]
    apply Submodule.subset_span
    use 0 ; dsimp ; congr ; norm_num
        
        
lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := PrimeIdeal_isPrime PI41N1
def MulI41N0 : IdealMulEqCertificate O ℤ timesTableO (I41N0) I41N1
  ![![41, 0, 0, 0], ![16, 0, -1, 2]] ![![41, 0, 0, 0], ![-15, 0, -1, 2]]
  ![![41, 0, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![1681, 0, 0, 0], ![-615, 0, -41, 82]], ![![656, 0, -41, 82], ![-246, 0, 0, 0]]]
 hmul := by decide
 f :=  ![![![![6323, 0, -500, 1000], ![-2218, 0, 0, 0]], ![![-18282, 0, 0, 0], ![0, 0, 0, 0]]]]
 g :=  ![![![![41, 0, 0, 0]], ![![-15, 0, -1, 2]]], ![![![16, 0, -1, 2]], ![![-6, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def PBC41 : PrimesBelowPCertificate 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, ← Ideal.mul_assoc]
    dsimp
    rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulI41N0, Set.range_unique]
    dsimp ; congr 
    erw [B_int_repr]
    rfl

