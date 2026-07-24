
import IdealArithmetic.Examples.NF3_3_46965_1.RI3_3_46965_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, -1, 5]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-79, -1, 5]] 
 ![![2, 0, 0], ![0, 2, 0], ![1, 1, 1]] where
  M :=![![![-79, -1, 5], ![45, 1, -3], ![-9, -1, 1]]]
  hmulB := by decide  
  f := ![![![1, 2, 1]], ![![9, 17, 6]], ![![14, 27, 12]]]
  g := ![![![-42, -3, 5], ![24, 2, -3], ![-5, -1, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [0, 1]]
 g := ![![[1]], ![[1]]]
 h' := ![![[1, 1], [0, 1]], ![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], []]
 b := ![[], [1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-107, -163, 153]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-130, -158, 153]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -2, -1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-1, -2, -1]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-1, -2, -1], ![-9, -17, -6], ![-18, -35, -17]]]
  hmulB := by decide  
  f := ![![![79, 1, -5]], ![![17, 0, -1]], ![![44, 1, -3]]]
  g := ![![![1, -2, -1], ![7, -17, -6], ![17, -35, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-79, -1, 5]] ![![-1, -2, -1]]
  ![![2, 0, 0]] where
 M := ![![![-2, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![368, 4, -23]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![368, 4, -23]] 
 ![![3, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![368, 4, -23], ![-207, 0, 12], ![36, -5, 0]]]
  hmulB := by decide  
  f := ![![![60, 115, 48]], ![![144, 276, 115]], ![![385, 738, 308]]]
  g := ![![![138, 4, -23], ![-77, 0, 12], ![12, -5, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![69, 0, -4]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![69, 0, -4]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![69, 0, -4], ![-36, 5, 0], ![0, -12, 5]]]
  hmulB := by decide  
  f := ![![![-25, -48, -20]], ![![-60, -115, -48]], ![![-144, -276, -115]]]
  g := ![![![23, 0, -4], ![-12, 5, 0], ![0, -12, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![368, 4, -23]] ![![368, 4, -23]]
  ![![133768, 1587, -8416]] where
 M := ![![![133768, 1587, -8416]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![133768, 1587, -8416]] ![![69, 0, -4]]
  ![![3, 0, 0]] where
 M := ![![![9172860, 108927, -577152]]]
 hmul := by decide  
 g := ![![![![3057620, 36309, -192384]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, -13, 6]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-10, -13, 6]] 
 ![![5, 0, 0], ![1, 1, 0], ![3, 0, 1]] where
  M :=![![![-10, -13, 6], ![54, 86, -39], ![-117, -190, 86]]]
  hmulB := by decide  
  f := ![![![-14, -22, -9]], ![![-19, -36, -15]], ![![-48, -89, -37]]]
  g := ![![![-3, -13, 6], ![17, 86, -39], ![-37, -190, 86]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16, 31, -12]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-16, 31, -12]] 
 ![![5, 0, 0], ![3, 1, 0], ![2, 0, 1]] where
  M :=![![![-16, 31, -12], ![-108, -208, 93], ![279, 460, -208]]]
  hmulB := by decide  
  f := ![![![484, 928, 387]], ![![987, 1892, 789]], ![![1864, 3573, 1490]]]
  g := ![![![-17, 31, -12], ![66, -208, 93], ![-137, 460, -208]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-10, -13, 6]] ![![-10, -13, 6]]
  ![![-1304, -2128, 963]] where
 M := ![![![-1304, -2128, 963]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-1304, -2128, 963]] ![![-16, 31, -12]]
  ![![5, 0, 0]] where
 M := ![![![519365, 845180, -382560]]]
 hmul := by decide  
 g := ![![![![103873, 169036, -76512]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [6, 1, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 0, 5], [6, 6, 2], [0, 1]]
 g := ![![[1], [1]], ![[6, 5, 0, 6], [6, 6, 0, 6]], ![[4, 6, 2, 1], [3, 0, 2, 1]]]
 h' := ![![[1, 0, 5], [1, 6], [0, 1]], ![[6, 6, 2], [0, 0, 2], [1, 0, 5]], ![[0, 1], [2, 1, 5], [6, 6, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2], []]
 b := ![[], [3, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [6, 1, 0, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-258314, 18550, -16310]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-36902, 2650, -2330]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-553, -1060, -442]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-553, -1060, -442]] 
 ![![11, 0, 0], ![0, 11, 0], ![7, 2, 1]] where
  M :=![![![-553, -1060, -442], ![-3978, -7625, -3180], ![-9540, -18286, -7625]]]
  hmulB := by decide  
  f := ![![![805, 8, -50]], ![![-450, 5, 24]], ![![437, 4, -27]]]
  g := ![![![231, -16, -442], ![1662, -115, -3180], ![3985, -276, -7625]]]
  hle1 := by decide   
  hle2 := by decide  


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
 g := ![![[7, 4], [6, 4], [1]], ![[4, 7], [3, 7], [1]]]
 h' := ![![[2, 10], [8, 2], [5, 2], [0, 1]], ![[0, 1], [1, 9], [9, 9], [2, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [1, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [6, 9, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-38, -58, 114]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-76, -26, 114]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-805, -8, 50]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-805, -8, 50]] 
 ![![11, 0, 0], ![5, 1, 0], ![10, 0, 1]] where
  M :=![![![-805, -8, 50], ![450, -5, -24], ![-72, 22, -5]]]
  hmulB := by decide  
  f := ![![![553, 1060, 442]], ![![613, 1175, 490]], ![![1370, 2626, 1095]]]
  g := ![![![-115, -8, 50], ![65, -5, -24], ![-12, 22, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-553, -1060, -442]] ![![-805, -8, 50]]
  ![![11, 0, 0]] where
 M := ![![![-11, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [1, 12, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 9], [4, 3], [0, 1]]
 g := ![![[10], [6, 10], [1]], ![[10], [10, 12], [1]], ![[10], [7, 4], [1]]]
 h' := ![![[3, 9], [8, 7], [12, 1, 7], [0, 1]], ![[4, 3], [3, 11], [0, 10, 8], [3, 9]], ![[0, 1], [10, 8], [11, 2, 11], [4, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11], []]
 b := ![[], [1, 1, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [1, 12, 6, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-377, -741, -325]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-29, -57, -25]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22, 1, 2]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-22, 1, 2]] 
 ![![17, 0, 0], ![0, 17, 0], ![6, 9, 1]] where
  M :=![![![-22, 1, 2], ![18, 10, 3], ![9, 22, 10]]]
  hmulB := by decide  
  f := ![![![-2, -2, 1]], ![![9, 14, -6]], ![![3, 5, -2]]]
  g := ![![![-2, -1, 2], ![0, -1, 3], ![-3, -4, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [13, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 16], [0, 1]]
 g := ![![[15, 4], [4], [13], [1]], ![[0, 13], [4], [13], [1]]]
 h' := ![![[9, 16], [16, 2], [0, 2], [4, 9], [0, 1]], ![[0, 1], [0, 15], [1, 15], [0, 8], [9, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [5, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [13, 8, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![364, 801, 1109]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-370, -540, 1109]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -2, 1]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-2, -2, 1]] 
 ![![17, 0, 0], ![7, 1, 0], ![12, 0, 1]] where
  M :=![![![-2, -2, 1], ![9, 14, -6], ![-18, -29, 14]]]
  hmulB := by decide  
  f := ![![![-22, 1, 2]], ![![-8, 1, 1]], ![![-15, 2, 2]]]
  g := ![![![0, -2, 1], ![-1, 14, -6], ![1, -29, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-22, 1, 2]] ![![-2, -2, 1]]
  ![![17, 0, 0]] where
 M := ![![![17, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0]] 
 ![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [10, 10, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 3, 14], [17, 15, 5], [0, 1]]
 g := ![![[9, 14, 1], [18, 7, 1], [3, 1], []], ![[14, 2, 9, 12], [5, 11, 11, 8], [12, 16], [7, 6]], ![[8, 7, 8, 1], [9, 14, 6, 9], [0, 9], [16, 6]]]
 h' := ![![[5, 3, 14], [10, 4, 18], [8, 17, 18], [0, 0, 1], [0, 1]], ![[17, 15, 5], [18, 17, 3], [5, 18, 14], [12, 14, 15], [5, 3, 14]], ![[0, 1], [6, 17, 17], [16, 3, 6], [15, 5, 3], [17, 15, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 6], []]
 b := ![[], [13, 7, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [10, 10, 16, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1311, 1995, -893]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![69, 105, -47]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-265, 80, -18]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-265, 80, -18]] 
 ![![23, 0, 0], ![0, 23, 0], ![16, 16, 1]] where
  M :=![![![-265, 80, -18], ![-162, -553, 240], ![720, 1226, -553]]]
  hmulB := by decide  
  f := ![![![-503, -964, -402]], ![![-3618, -6935, -2892]], ![![-3244, -6218, -2593]]]
  g := ![![![1, 16, -18], ![-174, -191, 240], ![416, 438, -553]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [19, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 22], [0, 1]]
 g := ![![[11, 8], [15, 6], [22, 4], [1]], ![[18, 15], [3, 17], [14, 19], [1]]]
 h' := ![![[21, 22], [14, 10], [19, 11], [4, 21], [0, 1]], ![[0, 1], [17, 13], [20, 12], [8, 2], [21, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [16, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [19, 2, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![55, 78, 71]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-47, -46, 71]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![503, 964, 402]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![503, 964, 402]] 
 ![![23, 0, 0], ![21, 1, 0], ![14, 0, 1]] where
  M :=![![![503, 964, 402], ![3618, 6935, 2892], ![8676, 16630, 6935]]]
  hmulB := by decide  
  f := ![![![265, -80, 18]], ![![249, -49, 6]], ![![130, -102, 35]]]
  g := ![![![-1103, 964, 402], ![-7935, 6935, 2892], ![-19028, 16630, 6935]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-265, 80, -18]] ![![503, 964, 402]]
  ![![23, 0, 0]] where
 M := ![![![-23, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 3, -2]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![4, 3, -2]] 
 ![![29, 0, 0], ![0, 29, 0], ![27, 13, 1]] where
  M :=![![![4, 3, -2], ![-18, -28, 9], ![27, 42, -28]]]
  hmulB := by decide  
  f := ![![![14, 0, -1]], ![![-9, -2, 0]], ![![9, -1, -1]]]
  g := ![![![2, 1, -2], ![-9, -5, 9], ![27, 14, -28]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [17, 5, 1] where
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
 g := ![![[2, 20], [23], [25, 6], [24, 1]], ![[18, 9], [23], [24, 23], [19, 28]]]
 h' := ![![[24, 28], [28, 7], [10, 9], [27, 8], [0, 1]], ![[0, 1], [22, 22], [23, 20], [16, 21], [24, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [19, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [17, 5, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-329, -718, 382]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-367, -196, 382]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14, 0, 1]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-14, 0, 1]] 
 ![![29, 0, 0], ![19, 1, 0], ![15, 0, 1]] where
  M :=![![![-14, 0, 1], ![9, 2, 0], ![0, 3, 2]]]
  hmulB := by decide  
  f := ![![![-4, -3, 2]], ![![-2, -1, 1]], ![![-3, -3, 2]]]
  g := ![![![-1, 0, 1], ![-1, 2, 0], ![-3, 3, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![4, 3, -2]] ![![-14, 0, 1]]
  ![![29, 0, 0]] where
 M := ![![![-29, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1978, -20, 123]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-1978, -20, 123]] 
 ![![31, 0, 0], ![8, 1, 0], ![20, 0, 1]] where
  M :=![![![-1978, -20, 123], ![1107, -10, -60], ![-180, 49, -10]]]
  hmulB := by decide  
  f := ![![![-3040, -5827, -2430]], ![![-1490, -2856, -1191]], ![![-3653, -7002, -2920]]]
  g := ![![![-138, -20, 123], ![77, -10, -60], ![-12, 49, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -14, -6]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-5, -14, -6]] 
 ![![31, 0, 0], ![27, 1, 0], ![5, 0, 1]] where
  M :=![![![-5, -14, -6], ![-54, -101, -42], ![-126, -242, -101]]]
  hmulB := by decide  
  f := ![![![37, 38, -18]], ![![27, 25, -12]], ![![17, 24, -11]]]
  g := ![![![13, -14, -6], ![93, -101, -42], ![223, -242, -101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-1978, -20, 123]] ![![-5, -14, -6]]
  ![![-4528, -54, 285]] where
 M := ![![![-4528, -54, 285]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-4528, -54, 285]] ![![-5, -14, -6]]
  ![![31, 0, 0]] where
 M := ![![![-10354, -124, 651]]]
 hmul := by decide  
 g := ![![![![-334, -4, 21]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)


lemma PB49I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB49I0 : PrimesBelowBoundCertificateInterval O 1 31 49 where
  m := 11
  g := ![2, 3, 3, 1, 2, 1, 2, 1, 2, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB49I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N0, I3N1]
    · exact ![I5N0, I5N0, I5N1]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1, I31N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![4, 2]
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![343]
    · exact ![121, 11]
    · exact ![2197]
    · exact ![289, 17]
    · exact ![6859]
    · exact ![529, 23]
    · exact ![841, 29]
    · exact ![31, 31, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I11N1, I17N1, I23N1, I29N1, I31N0, I31N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N0, I3N1], [I5N0, I5N0, I5N1], [], [I11N1], [], [I17N1], [], [I23N1], [I29N1], [I31N0, I31N1, I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
