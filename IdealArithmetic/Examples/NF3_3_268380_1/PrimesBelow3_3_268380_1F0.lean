
import IdealArithmetic.Examples.NF3_3_268380_1.RI3_3_268380_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-69002, -4402, 1013]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-69002, -4402, 1013]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-69002, -4402, 1013], ![299848, 19129, -4402], ![-1302992, -83126, 19129]]]
  hmulB := by decide  
  f := ![![![2011, 780, 73]], ![![10804, 4181, 390]], ![![115440, 44734, 4181]]]
  g := ![![![-34501, -4402, 1013], ![149924, 19129, -4402], ![-651496, -83126, 19129]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1505, 95, -22]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![1505, 95, -22]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![1505, 95, -22], ![-6512, -409, 95], ![28120, 1753, -409]]]
  hmulB := by decide  
  f := ![![![746, 289, 27]], ![![4369, 1692, 158]], ![![43145, 16712, 1561]]]
  g := ![![![716, 95, -22], ![-3099, -409, 95], ![13388, 1753, -409]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-69002, -4402, 1013]] ![![1505, 95, -22]]
  ![![-46696626, -2978983, 685537]] where
 M := ![![![-46696626, -2978983, 685537]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-46696626, -2978983, 685537]] ![![1505, 95, -22]]
  ![![2, 0, 0]] where
 M := ![![![-31601984394, -2016029062, 463937754]]]
 hmul := by decide  
 g := ![![![![-15800992197, -1008014531, 231968877]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![281, 38, -6]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![281, 38, -6]] 
 ![![3, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![281, 38, -6], ![-1776, -241, 38], ![11248, 1530, -241]]]
  hmulB := by decide  
  f := ![![![59, 22, 2]], ![![217, 85, 8]], ![![2210, 850, 79]]]
  g := ![![![85, 38, -6], ![-537, -241, 38], ![3400, 1530, -241]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![281, 38, -6]] ![![281, 38, -6]]
  ![![-56015, -7660, 1204]] where
 M := ![![![-56015, -7660, 1204]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-56015, -7660, 1204]] ![![281, 38, -6]]
  ![![3, 0, 0]] where
 M := ![![![11406537, 1559610, -245154]]]
 hmul := by decide  
 g := ![![![![3802179, 519870, -81718]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16837, 6521, 609]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![16837, 6521, 609]] 
 ![![5, 0, 0], ![1, 1, 0], ![4, 0, 1]] where
  M :=![![![16837, 6521, 609], ![180264, 69820, 6521], ![1930216, 747591, 69820]]]
  hmulB := by decide  
  f := ![![![-208511, -13301, 3061]], ![![139509, 8899, -2048]], ![![-954228, -60867, 14008]]]
  g := ![![![1576, 6521, 609], ![16872, 69820, 6521], ![180669, 747591, 69820]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1163, -159, 25]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-1163, -159, 25]] 
 ![![5, 0, 0], ![2, 1, 0], ![1, 0, 1]] where
  M :=![![![-1163, -159, 25], ![7400, 1012, -159], ![-47064, -6433, 1012]]]
  hmulB := by decide  
  f := ![![![1297, 83, -19]], ![![-606, -38, 9]], ![![5173, 336, -75]]]
  g := ![![![-174, -159, 25], ![1107, 1012, -159], ![-7042, -6433, 1012]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![16837, 6521, 609]] ![![-1163, -159, 25]]
  ![![11993, 4472, 394]] where
 M := ![![![11993, 4472, 394]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![11993, 4472, 394]] ![![-1163, -159, 25]]
  ![![5, 0, 0]] where
 M := ![![![601725, 84175, -12495]]]
 hmul := by decide  
 g := ![![![![120345, 16835, -2499]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![85, 7, -1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![85, 7, -1]] 
 ![![7, 0, 0], ![1, 1, 0], ![6, 0, 1]] where
  M :=![![![85, 7, -1], ![-296, -2, 7], ![2072, 313, -2]]]
  hmulB := by decide  
  f := ![![![2187, 299, -47]], ![![-1675, -229, 36]], ![![14518, 1985, -312]]]
  g := ![![![12, 7, -1], ![-48, -2, 7], ![253, 313, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5861, 2270, 212]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![5861, 2270, 212]] 
 ![![7, 0, 0], ![5, 1, 0], ![3, 0, 1]] where
  M :=![![![5861, 2270, 212], ![62752, 24305, 2270], ![671920, 260242, 24305]]]
  hmulB := by decide  
  f := ![![![16315, 1046, -240]], ![![1505, 95, -22]], ![![51223, 3300, -755]]]
  g := ![![![-875, 2270, 212], ![-9369, 24305, 2270], ![-100315, 260242, 24305]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![85, 7, -1]] ![![85, 7, -1]]
  ![![3081, 268, -34]] where
 M := ![![![3081, 268, -34]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![3081, 268, -34]] ![![5861, 2270, 212]]
  ![![7, 0, 0]] where
 M := ![![![12029997, 4659382, 435162]]]
 hmul := by decide  
 g := ![![![![1718571, 665626, 62166]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-327, -23, 5]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-327, -23, 5]] 
 ![![11, 0, 0], ![0, 11, 0], ![5, 2, 1]] where
  M :=![![![-327, -23, 5], ![1480, 108, -23], ![-6808, -521, 108]]]
  hmulB := by decide  
  f := ![![![-29, -11, -1]], ![![-296, -116, -11]], ![![-363, -140, -13]]]
  g := ![![![-32, -3, 5], ![145, 14, -23], ![-668, -67, 108]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [9, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 10], [0, 1]]
 g := ![![[4, 5], [5, 9], [1]], ![[0, 6], [0, 2], [1]]]
 h' := ![![[8, 10], [10, 7], [2, 8], [0, 1]], ![[0, 1], [0, 4], [0, 3], [8, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [5, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [9, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![601, 467, 85]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16, 27, 85]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 11, 1]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![29, 11, 1]] 
 ![![11, 0, 0], ![9, 1, 0], ![7, 0, 1]] where
  M :=![![![29, 11, 1], ![296, 116, 11], ![3256, 1253, 116]]]
  hmulB := by decide  
  f := ![![![327, 23, -5]], ![![133, 9, -2]], ![![827, 62, -13]]]
  g := ![![![-7, 11, 1], ![-75, 116, 11], ![-803, 1253, 116]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-327, -23, 5]] ![![29, 11, 1]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5423, 500, -94]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![5423, 500, -94]] 
 ![![13, 0, 0], ![0, 13, 0], ![8, 11, 1]] where
  M :=![![![5423, 500, -94], ![-27824, -2755, 500], ![148000, 15676, -2755]]]
  hmulB := by decide  
  f := ![![![19075, 7388, 690]], ![![204240, 79105, 7388]], ![![352776, 136635, 12761]]]
  g := ![![![475, 118, -94], ![-2448, -635, 500], ![13080, 3537, -2755]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [7, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 12], [0, 1]]
 g := ![![[6, 10], [4], [10, 1]], ![[2, 3], [4], [7, 12]]]
 h' := ![![[10, 12], [10, 7], [8, 2], [0, 1]], ![[0, 1], [2, 6], [2, 11], [10, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [7, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [7, 3, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3547, 1618, 790]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-759, -544, 790]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19075, 7388, 690]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![19075, 7388, 690]] 
 ![![13, 0, 0], ![2, 1, 0], ![9, 0, 1]] where
  M :=![![![19075, 7388, 690], ![204240, 79105, 7388], ![2186848, 846996, 79105]]]
  hmulB := by decide  
  f := ![![![5423, 500, -94]], ![![-1306, -135, 24]], ![![15139, 1552, -277]]]
  g := ![![![-147, 7388, 690], ![-1574, 79105, 7388], ![-16853, 846996, 79105]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![5423, 500, -94]] ![![19075, 7388, 690]]
  ![![13, 0, 0]] where
 M := ![![![13, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [15, 5, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 4, 11], [10, 12, 6], [0, 1]]
 g := ![![[16], [6, 13], [8, 1], []], ![[13, 4, 4, 12], [15, 1], [12, 8], [2, 2]], ![[14, 12, 2, 5], [10, 13], [15, 16], [7, 2]]]
 h' := ![![[15, 4, 11], [13, 4], [16, 13, 8], [0, 0, 1], [0, 1]], ![[10, 12, 6], [5, 16, 10], [3, 12, 1], [8, 12, 12], [15, 4, 11]], ![[0, 1], [2, 14, 7], [4, 9, 8], [12, 5, 4], [10, 12, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 16], []]
 b := ![[], [0, 4, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [15, 5, 9, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-127313, -40783, -34187]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7489, -2399, -2011]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

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


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [3, 3, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 10, 13], [11, 8, 6], [0, 1]]
 g := ![![[12, 18, 4], [3, 4, 6], [13, 1], []], ![[18, 4, 5, 8], [5, 16, 16, 3], [7, 7], [6, 17]], ![[18, 11, 11, 9], [8, 17, 10, 5], [18, 5], [13, 17]]]
 h' := ![![[2, 10, 13], [10, 18, 17], [18, 15, 14], [0, 0, 1], [0, 1]], ![[11, 8, 6], [17, 10, 9], [4, 10, 3], [5, 9, 8], [2, 10, 13]], ![[0, 1], [6, 10, 12], [1, 13, 2], [6, 10, 10], [11, 8, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 3], []]
 b := ![[], [15, 9, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [3, 3, 6, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1686003, -1169526, -190152]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-88737, -61554, -10008]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [14, 16, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 5, 4], [22, 17, 19], [0, 1]]
 g := ![![[14, 12, 1], [14, 11, 1], [15, 10, 1], []], ![[13, 18, 17, 16], [7, 20, 14, 18], [7, 0, 14, 6], [16, 16]], ![[3, 15, 9, 19], [8, 10, 1, 10], [11, 9, 12, 15], [1, 16]]]
 h' := ![![[11, 5, 4], [11, 22, 22], [20, 11, 22], [0, 0, 1], [0, 1]], ![[22, 17, 19], [11, 20, 2], [14, 11, 4], [12, 21, 17], [11, 5, 4]], ![[0, 1], [2, 4, 22], [22, 1, 20], [10, 2, 5], [22, 17, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 8], []]
 b := ![[], [2, 8, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [14, 16, 13, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-157458, -69092, -7590]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6846, -3004, -330]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀

instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![396713, 25308, -5824]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![396713, 25308, -5824]] 
 ![![29, 0, 0], ![0, 29, 0], ![16, 4, 1]] where
  M :=![![![396713, 25308, -5824], ![-1723904, -109975, 25308], ![7491168, 477892, -109975]]]
  hmulB := by decide  
  f := ![![![341, 148, 16]], ![![4736, 1733, 148]], ![![2352, 928, 89]]]
  g := ![![![16893, 1676, -5824], ![-73408, -7283, 25308], ![318992, 31648, -109975]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [27, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 28], [0, 1]]
 g := ![![[13, 4], [7], [27, 5], [26, 1]], ![[1, 25], [7], [12, 24], [23, 28]]]
 h' := ![![[26, 28], [1, 27], [25, 23], [23, 11], [0, 1]], ![[0, 1], [7, 2], [14, 6], [19, 18], [26, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [22, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [27, 3, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11279, 3697, 453]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![139, 65, 453]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![341, 148, 16]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![341, 148, 16]] 
 ![![29, 0, 0], ![25, 1, 0], ![13, 0, 1]] where
  M :=![![![341, 148, 16], ![4736, 1733, 148], ![43808, 17612, 1733]]]
  hmulB := by decide  
  f := ![![![396713, 25308, -5824]], ![![282549, 18025, -4148]], ![![436153, 27824, -6403]]]
  g := ![![![-123, 148, 16], ![-1397, 1733, 148], ![-14449, 17612, 1733]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![396713, 25308, -5824]] ![![341, 148, 16]]
  ![![29, 0, 0]] where
 M := ![![![29, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-34867, -2215, 511]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-34867, -2215, 511]] 
 ![![31, 0, 0], ![0, 31, 0], ![15, 28, 1]] where
  M :=![![![-34867, -2215, 511], ![151256, 9590, -2215], ![-655640, -41449, 9590]]]
  hmulB := by decide  
  f := ![![![5115, 1981, 185]], ![![54760, 21210, 1981]], ![![70851, 27442, 2563]]]
  g := ![![![-1372, -533, 511], ![5951, 2310, -2215], ![-25790, -9999, 9590]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [13, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 30], [0, 1]]
 g := ![![[3, 2], [9, 14], [30, 28], [23, 1]], ![[18, 29], [21, 17], [23, 3], [15, 30]]]
 h' := ![![[23, 30], [7, 8], [13, 13], [11, 20], [0, 1]], ![[0, 1], [5, 23], [2, 18], [6, 11], [23, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [20, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [13, 8, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1197, 1540, 365]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-138, -280, 365]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5115, 1981, 185]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![5115, 1981, 185]] 
 ![![31, 0, 0], ![3, 1, 0], ![22, 0, 1]] where
  M :=![![![5115, 1981, 185], ![54760, 21210, 1981], ![586376, 227107, 21210]]]
  hmulB := by decide  
  f := ![![![-34867, -2215, 511]], ![![1505, 95, -22]], ![![-45894, -2909, 672]]]
  g := ![![![-158, 1981, 185], ![-1692, 21210, 1981], ![-18115, 227107, 21210]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-34867, -2215, 511]] ![![5115, 1981, 185]]
  ![![31, 0, 0]] where
 M := ![![![31, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)


lemma PB116I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB116I0 : PrimesBelowBoundCertificateInterval O 1 31 116 where
  m := 11
  g := ![3, 3, 3, 3, 2, 2, 1, 1, 1, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB116I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N1, I5N1]
    · exact ![I7N0, I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0]
    · exact ![I23N0]
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1]
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
    · exact ![2, 2, 2]
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![169, 13]
    · exact ![4913]
    · exact ![6859]
    · exact ![12167]
    · exact ![841, 29]
    · exact ![961, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I5N0, I5N1, I7N0, I7N1, I11N1, I13N1, I29N1, I31N1]
  Il := ![[I2N0, I2N1, I2N1], [I3N0, I3N0, I3N0], [I5N0, I5N1, I5N1], [I7N0, I7N0, I7N1], [I11N1], [I13N1], [], [], [], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
