
import IdealArithmetic.Examples.NF5_3_1215000000_2.RI5_3_1215000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![36, 14, 7, -13, -7]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![36, 14, 7, -13, -7]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![36, 14, 7, -13, -7], ![42, 21, -6, -34, -26], ![156, 4, -7, -208, -68], ![202, 64, -70, -293, -170], ![352, 4, -44, -528, -187]]]
  hmulB := by decide  
  f := ![![![629, -510, -441, 47, 165]], ![![-495, 759, -11, -143, 47]], ![![-282, -200, 627, 106, -286]], ![![313, -438, -35, 78, -9]], ![![-236, 820, -464, -204, 249]]]
  g := ![![![18, 14, 7, -13, -7], ![21, 21, -6, -34, -26], ![78, 4, -7, -208, -68], ![101, 64, -70, -293, -170], ![176, 4, -44, -528, -187]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, -42, -35, 4, 13]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![51, -42, -35, 4, 13]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![51, -42, -35, 4, 13], ![-78, 121, -3, -23, 8], ![-48, -28, 101, 16, -46], ![50, -70, -5, 12, -2], ![-34, 128, -76, -33, 40]]]
  hmulB := by decide  
  f := ![![![52, -18, 29, -41, 18]], ![![-54, 59, -44, 77, -41]], ![![246, -210, 180, -301, 154]], ![![-244, 226, -185, 313, -163]], ![![487, -418, 357, -598, 306]]]
  g := ![![![19, -42, -35, 4, 13], ![-43, 121, -3, -23, 8], ![-1, -28, 101, 16, -46], ![26, -70, -5, 12, -2], ![-37, 128, -76, -33, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![95, 53, 29, -5, -14]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![95, 53, 29, -5, -14]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![95, 53, 29, -5, -14], ![84, 29, 19, -2, -10], ![60, 37, 8, -5, -4], ![56, 37, 17, -4, -8], ![8, -13, 5, 3, -3]]]
  hmulB := by decide  
  f := ![![![-6, 7, -6, 7, -6]], ![![15, -9, 7, -20, 4]], ![![-45, 56, -49, 52, -50]], ![![83, -45, 34, -112, 16]], ![![-73, 106, -94, 80, -101]]]
  g := ![![![16, 53, 29, -5, -14], ![24, 29, 19, -2, -10], ![12, 37, 8, -5, -4], ![7, 37, 17, -4, -8], ![8, -13, 5, 3, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![36, 14, 7, -13, -7]] ![![51, -42, -35, 4, 13]]
  ![![-4, 0, 2, 9, 4]] where
 M := ![![![-4, 0, 2, 9, 4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-4, 0, 2, 9, 4]] ![![51, -42, -35, 4, 13]]
  ![![14, -6, -7, -8, -2]] where
 M := ![![![14, -6, -7, -8, -2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![14, -6, -7, -8, -2]] ![![95, 53, 29, -5, -14]]
  ![![-58, 39, 90, 3, -38]] where
 M := ![![![-58, 39, 90, 3, -38]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-58, 39, 90, 3, -38]] ![![95, 53, 29, -5, -14]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![3030, 1992, -360, -364, 152]]]
 hmul := by decide  
 g := ![![![![1515, 996, -180, -182, 76]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 5, -1, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-3, 5, -1, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 2, 1]] where
  M :=![![![-3, 5, -1, 0, 0], ![0, -2, 6, -3, 0], ![0, -3, -11, 15, -6], ![12, -9, 6, -14, 8], ![-30, 27, -9, 24, -15]]]
  hmulB := by decide  
  f := ![![![3, 3, 3, 6, 2]], ![![-4, 0, 2, 9, 4]], ![![-24, -3, 7, 39, 18]], ![![-136, -19, 38, 216, 100]], ![![-158, -23, 43, 248, 115]]]
  g := ![![![-1, 5, -1, 0, 0], ![0, -2, 6, -1, 0], ![0, -3, -11, 9, -6], ![4, -9, 6, -10, 8], ![-10, 27, -9, 18, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2], [0, 1]]
 g := ![![[1, 1]], ![[2, 2]]]
 h' := ![![[1, 2], [0, 1]], ![[0, 1], [1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [2, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8076, -6722, 7608, 13795, 13157]
  a := ![0, 7, -7, -5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2692, -6722, 7608, -4173, 13157]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, 21, 53, 2, -22]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-49, 21, 53, 2, -22]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-49, 21, 53, 2, -22], ![132, -170, -30, 29, 4], ![-24, 145, -111, -37, 58], ![-80, 91, 26, -10, -4], ![130, -257, 55, 60, -35]]]
  hmulB := by decide  
  f := ![![![-4623, -2389, -1211, 228, 600]], ![![-4282, -2206, -1124, 217, 552]], ![![-3994, -2085, -1039, 179, 530]], ![![-4046, -2067, -1068, 220, 512]], ![![2, -41, 15, -36, 23]]]
  g := ![![![-67, 21, 53, 2, -22], ![158, -170, -30, 29, 4], ![-6, 145, -111, -37, 58], ![-98, 91, 26, -10, -4], ![138, -257, 55, 60, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-3, 5, -1, 0, 0]] ![![-49, 21, 53, 2, -22]]
  ![![831, -1058, -198, 176, 28]] where
 M := ![![![831, -1058, -198, 176, 28]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![831, -1058, -198, 176, 28]] ![![-49, 21, 53, 2, -22]]
  ![![-186063, 177421, 103877, -21774, -35682]] where
 M := ![![![-186063, 177421, 103877, -21774, -35682]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-186063, 177421, 103877, -21774, -35682]] ![![-49, 21, 53, 2, -22]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![27146871, -11817888, -29242950, -993546, 12163902]]]
 hmul := by decide  
 g := ![![![![9048957, -3939296, -9747650, -331182, 4054634]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39, -6, 10, 60, 28]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-39, -6, 10, 60, 28]] 
 ![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-39, -6, 10, 60, 28], ![-168, -25, 44, 258, 120], ![-720, -110, 189, 1110, 516], ![-1328, -202, 348, 2047, 952], ![-1916, -290, 502, 2952, 1373]]]
  hmulB := by decide  
  f := ![![![-19, -2, -10, 12, -4]], ![![1, -7, 2, -6, 4]], ![![-44, 22, -27, 42, -20]], ![![18, -26, 16, -29, 16]], ![![-64, 42, -46, 72, -35]]]
  g := ![![![-61, -6, 10, 60, 28], ![-263, -25, 44, 258, 120], ![-1130, -110, 189, 1110, 516], ![-2084, -202, 348, 2047, 952], ![-3006, -290, 502, 2952, 1373]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-39, -6, 10, 60, 28]] ![![-39, -6, 10, 60, 28]]
  ![![-137999, -20956, 36172, 212688, 98912]] where
 M := ![![![-137999, -20956, 36172, 212688, 98912]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-137999, -20956, 36172, 212688, 98912]] ![![-39, -6, 10, 60, 28]]
  ![![-489106327, -74274482, 128203702, 753824892, 350571212]] where
 M := ![![![-489106327, -74274482, 128203702, 753824892, 350571212]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-489106327, -74274482, 128203702, 753824892, 350571212]] ![![-39, -6, 10, 60, 28]]
  ![![-1733527304479, -263249186872, 454389170040, 2671762684992, 1242520766496]] where
 M := ![![![-1733527304479, -263249186872, 454389170040, 2671762684992, 1242520766496]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-1733527304479, -263249186872, 454389170040, 2671762684992, 1242520766496]] ![![-39, -6, 10, 60, 28]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-6144097408435335, -933027499857950, 1610480155028610, 9469461569137500, 4403835233301980]]]
 hmul := by decide  
 g := ![![![![-1228819481687067, -186605499971590, 322096031005722, 1893892313827500, 880767046660396]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2 ⊙ MulI5N3)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-115, -37, -19, 2, 10]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-115, -37, -19, 2, 10]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![6, 4, 3, 3, 1]] where
  M :=![![![-115, -37, -19, 2, 10], ![-60, -68, -16, 5, 4], ![-24, -37, -47, -19, 10], ![-48, -11, -24, -38, -8], ![30, -15, 15, -48, -37]]]
  hmulB := by decide  
  f := ![![![-1009, 897, -751, 1264, -652]], ![![3912, -3478, 2912, -4901, 2528]], ![![-15168, 13485, -11291, 19003, -9802]], ![![15852, -14093, 11800, -19860, 10244]], ![![-2496, 2219, -1858, 3127, -1613]]]
  g := ![![![-25, -11, -7, -4, 10], ![-12, -12, -4, -1, 4], ![-12, -11, -11, -7, 10], ![0, 3, 0, -2, -8], ![36, 19, 18, 9, -37]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [5, 0, 1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 0, 4, 1], [4, 3, 2, 1], [0, 3, 1, 5], [0, 1]]
 g := ![![[1, 0, 6, 1], []], ![[1, 4, 2, 0, 2, 2], [6, 5, 2, 1, 4, 1]], ![[6, 1, 1, 0, 1, 2], [2, 6, 1, 1, 5, 1]], ![[0, 5, 3, 6], [6, 1, 4, 4, 6, 6]]]
 h' := ![![[2, 0, 4, 1], [0, 0, 0, 1], [0, 1]], ![[4, 3, 2, 1], [6, 3, 4, 3], [2, 0, 4, 1]], ![[0, 3, 1, 5], [5, 2, 1, 3], [4, 3, 2, 1]], ![[0, 1], [5, 2, 2], [0, 3, 1, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 2, 5], []]
 b := ![[], [], [0, 1, 3, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [5, 0, 1, 1, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-323365058256966, -191645152242958, 222582397539090, 537879984581703, 418417234829109]
  a := ![3, 62, -124, -1, -249]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-404838352461660, -266473441651342, -147524186706891, -102481674272232, 418417234829109]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1009, 897, -751, 1264, -652]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-1009, 897, -751, 1264, -652]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-1009, 897, -751, 1264, -652], ![3912, -3478, 2912, -4901, 2528], ![-15168, 13485, -11291, 19003, -9802], ![15852, -14093, 11800, -19860, 10244], ![-29118, 25887, -21675, 36480, -18817]]]
  hmulB := by decide  
  f := ![![![-115, -37, -19, 2, 10]], ![![-25, -15, -5, 1, 2]], ![![-102, -37, -23, -1, 10]], ![![-89, -28, -17, -4, 6]], ![![-45, -18, -6, -6, -1]]]
  g := ![![![-252, 897, -751, 1264, -652], ![977, -3478, 2912, -4901, 2528], ![-3788, 13485, -11291, 19003, -9802], ![3959, -14093, 11800, -19860, 10244], ![-7272, 25887, -21675, 36480, -18817]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-115, -37, -19, 2, 10]] ![![-1009, 897, -751, 1264, -652]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-191, 173, -66, -41, 42]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-191, 173, -66, -41, 42]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![2, 7, 0, 4, 1]] where
  M :=![![![-191, 173, -66, -41, 42], ![-252, 42, 198, 13, -82], ![492, -709, -143, 115, 26], ![28, -23, -132, -10, 58], ![-560, 559, 286, -75, -93]]]
  hmulB := by decide  
  f := ![![![-717, -109, 188, 1105, 514]], ![![-3084, -468, 808, 4753, 2210]], ![![-13260, -2015, 3477, 20437, 9506]], ![![-24460, -3713, 6410, 37698, 17530]], ![![-14194, -2155, 3720, 21876, 10173]]]
  g := ![![![-25, -11, -6, -19, 42], ![-8, 56, 18, 31, -82], ![40, -81, -13, 1, 26], ![-8, -39, -12, -22, 58], ![-34, 110, 26, 27, -93]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 4 2 3 [7, 5, 10, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 4, 7, 3], [3, 10, 1, 5], [10, 7, 3, 3], [0, 1]]
 g := ![![[1, 4, 5, 5], [6, 1], []], ![[0, 4, 9, 8, 2, 3], [0, 9, 2, 4, 1, 1], [9, 8, 9]], ![[7, 0, 5, 0, 3, 3], [6, 8, 5, 5, 1, 5], [8, 6, 3]], ![[9, 6, 3, 10, 1, 4], [7, 3, 5, 8, 0, 3], [8, 6, 9]]]
 h' := ![![[4, 4, 7, 3], [2, 7, 1, 4], [0, 0, 1], [0, 1]], ![[3, 10, 1, 5], [3, 1, 2, 10], [8, 8, 0, 9], [4, 4, 7, 3]], ![[10, 7, 3, 3], [7, 4, 5, 4], [8, 0, 8, 1], [3, 10, 1, 5]], ![[0, 1], [6, 10, 3, 4], [0, 3, 2, 1], [10, 7, 3, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 7, 8], []]
 b := ![[], [], [8, 6, 5, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 4
  hpos := by decide
  P := [7, 5, 10, 5, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13915089872, -4847838332, 6291640245, 22204167762, 13554602016]
  a := ![1, 6, -8, -3, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3729481264, -9066368404, 571967295, -2910385482, 13554602016]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 14641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![717, 109, -188, -1105, -514]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![717, 109, -188, -1105, -514]] 
 ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![717, 109, -188, -1105, -514], ![3084, 468, -808, -4753, -2210], ![13260, 2015, -3477, -20437, -9506], ![24460, 3713, -6410, -37698, -17530], ![35272, 5359, -9248, -54363, -25285]]]
  hmulB := by decide  
  f := ![![![191, -173, 66, 41, -42]], ![![75, -51, 0, 10, -4]], ![![-10, 33, 25, -3, -10]], ![![119, -108, 54, 27, -32]], ![![103, -98, -8, 18, -3]]]
  g := ![![![913, 109, -188, -1105, -514], ![3927, 468, -808, -4753, -2210], ![16886, 2015, -3477, -20437, -9506], ![31147, 3713, -6410, -37698, -17530], ![44917, 5359, -9248, -54363, -25285]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-191, 173, -66, -41, 42]] ![![717, 109, -188, -1105, -514]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![-11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32247, 16629, 8459, -1620, -4166]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![32247, 16629, 8459, -1620, -4166]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![1, 4, 5, 10, 1]] where
  M :=![![![32247, 16629, 8459, -1620, -4166], ![24996, 12910, 6550, -1239, -3240], ![19440, 9965, 5121, -1029, -2478], ![19768, 10263, 5162, -934, -2592], ![670, 223, 217, -138, -19]]]
  hmulB := by decide  
  f := ![![![-17, -3, 1, 30, 16]], ![![-96, 0, 26, 129, 60]], ![![-360, -71, 103, 567, 258]], ![![-668, -109, 174, 1040, 484]], ![![-759, -121, 201, 1175, 545]]]
  g := ![![![2801, 2561, 2253, 3080, -4166], ![2172, 1990, 1750, 2397, -3240], ![1686, 1529, 1347, 1827, -2478], ![1720, 1587, 1394, 1922, -2592], ![53, 23, 24, 4, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 4 2 3 [3, 6, 1, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 4, 9, 7], [8, 10, 11, 10], [6, 11, 6, 9], [0, 1]]
 g := ![![[2, 11, 0, 3], [11, 8, 1], []], ![[11, 5, 11, 11, 11, 2], [4, 11, 12], [10, 1, 1, 6, 11, 5]], ![[0, 6, 12, 11, 5, 3], [6, 6, 10], [3, 7, 4, 12, 3, 12]], ![[6, 7, 3, 3, 9, 9], [1, 11, 4], [1, 0, 5, 6, 10, 1]]]
 h' := ![![[7, 4, 9, 7], [6, 1, 3, 9], [0, 0, 0, 1], [0, 1]], ![[8, 10, 11, 10], [2, 5, 1, 11], [1, 5, 2, 8], [7, 4, 9, 7]], ![[6, 11, 6, 9], [11, 4, 2, 5], [9, 9, 9, 6], [8, 10, 11, 10]], ![[0, 1], [9, 3, 7, 1], [5, 12, 2, 11], [6, 11, 6, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 12, 4], []]
 b := ![[], [], [11, 0, 4, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 4
  hpos := by decide
  P := [3, 6, 1, 5, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6456117197786, -4142334045106, 4749565569561, 10826566258509, 8767724939783]
  a := ![1, -25, 48, -1, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1171064779813, -3016402600326, -3006850702258, -5911591010717, 8767724939783]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 28561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -3, 1, 30, 16]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-17, -3, 1, 30, 16]] 
 ![![13, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![-17, -3, 1, 30, 16], ![-96, 0, 26, 129, 60], ![-360, -71, 103, 567, 258], ![-668, -109, 174, 1040, 484], ![-986, -125, 253, 1494, 699]]]
  hmulB := by decide  
  f := ![![![32247, 16629, 8459, -1620, -4166]], ![![16806, 8668, 4408, -843, -2172]], ![![8937, 4604, 2346, -453, -1152]], ![![26326, 13581, 6904, -1318, -3404]], ![![29818, 15367, 7825, -1506, -3847]]]
  g := ![![![-38, -3, 1, 30, 16], ![-168, 0, 26, 129, 60], ![-693, -71, 103, 567, 258], ![-1288, -109, 174, 1040, 484], ![-1871, -125, 253, 1494, 699]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![32247, 16629, 8459, -1620, -4166]] ![![-17, -3, 1, 30, 16]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 51, 31, -4, -16]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![131, 51, 31, -4, -16]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![16, 16, 5, 1, 0], ![8, 13, 0, 0, 1]] where
  M :=![![![131, 51, 31, -4, -16], ![96, 56, 16, -7, -8], ![48, 63, 33, -7, -14], ![76, 33, 24, -2, -12], ![22, -11, -17, 0, 7]]]
  hmulB := by decide  
  f := ![![![-1, -1, 1, 2, 2]], ![![-12, 2, 0, 17, 4]], ![![-24, -17, 19, 41, 34]], ![![-24, -4, 7, 37, 18]], ![![-14, -1, 3, 21, 9]]]
  g := ![![![19, 19, 3, -4, -16], ![16, 16, 3, -7, -8], ![16, 21, 4, -7, -14], ![12, 13, 2, -2, -12], ![-2, -6, -1, 0, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [1, 5, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 7, 16], [6, 9, 1], [0, 1]]
 g := ![![[15, 2, 16], [9, 13], [8, 1], []], ![[9, 10, 13, 9], [11, 2], [8, 13], [11, 1]], ![[6, 12, 0, 13], [0, 4], [2, 15], [9, 1]]]
 h' := ![![[2, 7, 16], [4, 3, 13], [9, 10, 8], [0, 0, 1], [0, 1]], ![[6, 9, 1], [4, 14, 12], [7, 16, 11], [10, 6, 9], [2, 7, 16]], ![[0, 1], [16, 0, 9], [13, 8, 15], [10, 11, 7], [6, 9, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 6], []]
 b := ![[], [5, 13, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [1, 5, 9, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3103682, 36641173, -35038805, -5533436, -46332811]
  a := ![-1, 7, -17, 8, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![26829046, 42794276, -433625, -5533436, -46332811]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 3, 5, 0, -2]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-7, 3, 5, 0, -2]] 
 ![![17, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![12, 0, 0, 0, 1]] where
  M :=![![![-7, 3, 5, 0, -2], ![12, -18, -2, 3, 0], ![0, 11, -13, -3, 6], ![-8, 9, 2, -2, 0], ![10, -23, 7, 6, -5]]]
  hmulB := by decide  
  f := ![![![5, -1, -5, -18, -8]], ![![4, 0, -2, -9, -4]], ![![13, 2, -4, -21, -10]], ![![26, 3, -8, -44, -20]], ![![38, 5, -13, -66, -31]]]
  g := ![![![0, 3, 5, 0, -2], ![4, -18, -2, 3, 0], ![-5, 11, -13, -3, 6], ![-2, 9, 2, -2, 0], ![7, -23, 7, 6, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 20, -34, -196, -92]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![127, 20, -34, -196, -92]] 
 ![![17, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![127, 20, -34, -196, -92], ![552, 81, -142, -850, -392], ![2352, 368, -627, -3628, -1700], ![4368, 652, -1134, -6729, -3116], ![6264, 972, -1662, -9660, -4517]]]
  hmulB := by decide  
  f := ![![![-433, 148, 30, -28, 4]], ![![-358, 97, 30, -18, 0]], ![![-184, 48, -11, -12, 12]], ![![-116, 44, 2, -9, 4]], ![![-191, 56, 36, -8, -9]]]
  g := ![![![91, 20, -34, -196, -92], ![394, 81, -142, -850, -392], ![1684, 368, -627, -3628, -1700], ![3120, 652, -1134, -6729, -3116], ![4483, 972, -1662, -9660, -4517]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![131, 51, 31, -4, -16]] ![![-7, 3, 5, 0, -2]]
  ![![-433, 148, 30, -28, 4]] where
 M := ![![![-433, 148, 30, -28, 4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![-433, 148, 30, -28, 4]] ![![127, 20, -34, -196, -92]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-185, -91, -44, 9, 22]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-185, -91, -44, 9, 22]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![15, 10, 3, 1, 0], ![1, 3, 8, 0, 1]] where
  M :=![![![-185, -91, -44, 9, 22], ![-132, -84, -38, 9, 18], ![-108, -49, -37, 3, 18], ![-116, -51, -28, 4, 14], ![4, -17, 4, 3, -3]]]
  hmulB := by decide  
  f := ![![![-3, 3, -2, 3, -2]], ![![12, -10, 8, -15, 6]], ![![-36, 37, -33, 45, -30]], ![![1, 1, -1, -2, -2]], ![![-17, 18, -16, 21, -15]]]
  g := ![![![-18, -13, -13, 9, 22], ![-15, -12, -11, 9, 18], ![-9, -7, -10, 3, 18], ![-10, -7, -8, 4, 14], ![-2, -2, 1, 3, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [7, 9, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 11, 16], [12, 7, 3], [0, 1]]
 g := ![![[3, 4, 9], [14, 5, 16], [10, 1], []], ![[8, 6, 10, 5], [0, 7, 3, 11], [15, 11], [5, 9]], ![[18, 15, 11, 15], [2, 16, 9, 14], [13, 7], [18, 9]]]
 h' := ![![[17, 11, 16], [16, 8, 16], [6, 17, 15], [0, 0, 1], [0, 1]], ![[12, 7, 3], [17, 12, 12], [1, 16, 16], [7, 0, 7], [17, 11, 16]], ![[0, 1], [1, 18, 10], [5, 5, 7], [18, 0, 11], [12, 7, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 5], []]
 b := ![[], [6, 7, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [7, 9, 9, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20880943, -18571692, 15519912, -26128062, 13514346]
  a := ![0, 4, 16, -26, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![21015133, 10640310, -747930, -26128062, 13514346]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1789, 2469, 231, -436, 36]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-1789, 2469, 231, -436, 36]] 
 ![![19, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![-1789, 2469, 231, -436, 36], ![-216, -1476, 1802, 473, -872], ![5232, -5107, -2805, 647, 946], ![-220, 1215, -886, -324, 456], ![-3982, 2387, 3635, -48, -1461]]]
  hmulB := by decide  
  f := ![![![-219, 643, -601, 142, -734]], ![![105, 269, -275, -237, -410]], ![![-228, 929, -875, 79, -1102]], ![![1232, -89, -58, -1826, -524]], ![![-64, 1661, -1603, -372, -2147]]]
  g := ![![![-1520, 2469, 231, -436, 36], ![332, -1476, 1802, 473, -872], ![3835, -5107, -2805, 647, 946], ![-451, 1215, -886, -324, 456], ![-2483, 2387, 3635, -48, -1461]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![65, 24, 3, -43, -24]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![65, 24, 3, -43, -24]] 
 ![![19, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![65, 24, 3, -43, -24], ![144, 33, -22, -178, -86], ![516, 86, -123, -760, -356], ![932, 150, -232, -1401, -654], ![1310, 200, -343, -2019, -939]]]
  hmulB := by decide  
  f := ![![![879, -788, 653, -1091, 562]], ![![609, -547, 451, -753, 388]], ![![1383, -1234, 1030, -1727, 890]], ![![-352, 310, -262, 445, -230]], ![![1559, -1388, 1158, -1948, 1005]]]
  g := ![![![4, 24, 3, -43, -24], ![93, 33, -22, -178, -86], ![461, 86, -123, -760, -356], ![860, 150, -232, -1401, -654], ![1258, 200, -343, -2019, -939]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-185, -91, -44, 9, 22]] ![![-1789, 2469, 231, -436, 36]]
  ![![30829, -34292, -11301, 5177, 3030]] where
 M := ![![![30829, -34292, -11301, 5177, 3030]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![30829, -34292, -11301, 5177, 3030]] ![![65, 24, 3, -43, -24]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![28785, 18924, -3420, -3458, 1444]]]
 hmul := by decide  
 g := ![![![![1515, 996, -180, -182, 76]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 5 2 4 [1, 19, 13, 15, 7, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 16, 9, 14, 9], [16, 8, 20, 11, 11], [1, 22, 2, 4, 11], [8, 22, 15, 17, 15], [0, 1]]
 g := ![![[9, 6, 10, 22, 1], [20, 1, 5, 5, 3], [1], []], ![[5, 19, 5, 19, 14, 3, 10, 2], [16, 7, 8, 9, 8, 21, 20, 8], [1, 16, 11, 22, 17, 6, 9, 12], [20, 14, 7, 12]], ![[12, 19, 3, 7, 6, 1, 19, 10], [19, 4, 10, 20, 20, 15, 5, 17], [16, 15, 11, 22, 5, 4, 5, 14], [16, 14, 16, 6]], ![[4, 8, 7, 0, 20, 12, 6, 5], [14, 6, 6, 14, 7, 5, 13, 7], [8, 15, 22, 7, 4, 5, 3, 11], [11, 16, 0, 6]], ![[2, 17, 22, 9, 7, 8, 3, 17], [5, 1, 3, 21, 4, 12, 5, 17], [8, 22, 21, 1, 4, 21, 16, 11], [14, 12, 16, 18]]]
 h' := ![![[14, 16, 9, 14, 9], [3, 11, 7, 20, 22], [22, 4, 10, 8, 16], [0, 0, 1], [0, 1]], ![[16, 8, 20, 11, 11], [17, 9, 12, 16, 6], [21, 2, 4, 6, 11], [15, 8, 21, 7, 20], [14, 16, 9, 14, 9]], ![[1, 22, 2, 4, 11], [10, 1, 22, 8, 16], [20, 7, 5, 17, 14], [10, 7, 7, 9, 8], [16, 8, 20, 11, 11]], ![[8, 22, 15, 17, 15], [9, 4, 22, 2, 17], [0, 18, 4, 1, 20], [13, 3, 18, 16, 1], [1, 22, 2, 4, 11]], ![[0, 1], [11, 21, 6, 0, 8], [5, 15, 0, 14, 8], [4, 5, 22, 14, 17], [8, 22, 15, 17, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 13, 17, 3], [], [], []]
 b := ![[], [1, 14, 17, 21, 15], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 5
  hpos := by decide
  P := [1, 19, 13, 15, 7, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27826771962420, 34731185755179, -36791485045639, -51339412773879, -59890034329679]
  a := ![13, 7, -15, 5, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1209859650540, 1510051554573, -1599629784593, -2232148381473, -2603914536073]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 6436343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀



lemma PB1705I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1705I0 : PrimesBelowBoundCertificateInterval O 1 23 1705 where
  m := 9
  g := ![5, 4, 5, 2, 2, 2, 3, 3, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1705I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![9, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![2401, 7]
    · exact ![14641, 11]
    · exact ![28561, 13]
    · exact ![4913, 17, 17]
    · exact ![6859, 19, 19]
    · exact ![6436343]
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
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
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
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I11N1, I13N1, I17N1, I17N2, I19N1, I19N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [I11N1], [I13N1], [I17N1, I17N2], [I19N1, I19N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
