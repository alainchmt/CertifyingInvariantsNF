
import IdealArithmetic.Examples.NF5_3_5695312500_2.RI5_3_5695312500_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, 18, 8, 5, -15]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![0, 18, 8, 5, -15]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, 18, 8, 5, -15], ![-10, 5, -4, -4, 10], ![32, -4, 27, 24, -62], ![-100, 5, -79, -73, 190], ![-26, 10, -16, -16, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-5, 3, -2, -2, 5], ![0, -1, 0, 0, 0]], ![![36, -48, 6, 10, -21], ![4, 4, -1, 0, 0]], ![![2919, -2853, 908, 1102, -2574], ![210, 321, -79, 1, 0]], ![![-2919, 2826, -920, -1109, 2597], ![-207, -321, 79, -1, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, 18, 8, 5, -15], ![-5, 5, -4, -4, 10], ![16, -4, 27, 24, -62], ![-50, 5, -79, -73, 190], ![-13, 10, -16, -16, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-5, 10, 5, 3, -9]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![-5, 10, 5, 3, -9]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![-5, 10, 5, 3, -9], ![-6, -2, -3, -2, 6], ![4, -8, 7, 2, -4], ![-16, 2, -11, -6, 31], ![-10, 3, -1, -2, 11]]]
  hmulB := by decide  
  f := ![![![68, -20, 14, 9, -40], ![6, 12, 0, 2, 0]], ![![-645, 169, -157, -100, 439], ![-52, -114, 0, -21, -1]], ![![-3, -1, -1, -1, 3], ![0, -1, 0, 0, 0]], ![![34, -10, 7, 5, -20], ![3, 6, 0, 1, 0]], ![![-28, 6, -8, -5, 22], ![-2, -5, 0, -1, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![-4, 10, 5, 3, -9], ![-2, -2, -3, -2, 6], ![1, -8, 7, 2, -4], ![-5, 2, -11, -6, 31], ![-4, 3, -1, -2, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-1, -9, -1, 0, 1]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![-1, -9, -1, 0, 1]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![-1, -9, -1, 0, 1], ![-12, -6, -11, -10, 27], ![56, -7, 46, 42, -101], ![-220, -10, -142, -159, 430], ![-60, -11, -35, -42, 120]]]
  hmulB := by decide  
  f := ![![![-63, 35, -63, -68, 184], ![24, -22, -2, 0, 0]], ![![-4, 11, -4, -5, 12], ![3, -1, 0, 0, 0]], ![![-26, 16, -26, -29, 79], ![11, -10, -1, 0, 0]], ![![-5963, 2771, -5963, -6400, 17468], ![2230, -2178, -210, 1, 0]], ![![-31, 22, -31, -34, 92], ![13, -11, -1, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![4, -9, -1, 0, 1], ![-11, -6, -11, -10, 27], ![59, -7, 46, 42, -101], ![-249, -10, -142, -159, 430], ![-67, -11, -35, -42, 120]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2

def I2N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-1, -10, -1, 0, 1]] i)))

def SI2N3: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![-1, -10, -1, 0, 1]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![-1, -10, -1, 0, 1], ![-12, -6, -12, -10, 27], ![56, -7, 45, 40, -101], ![-182, 4, -133, -131, 347], ![-48, -6, -34, -34, 93]]]
  hmulB := by decide  
  f := ![![![13091, -5204, 12997, 11871, -30805], ![-2424, 2316, -8, 2, 0]], ![![12197, -4849, 12109, 11061, -28704], ![-2259, 2158, -7, 2, 0]], ![![6, -2, 6, 5, -13], ![-1, 1, 0, 0, 0]], ![![6546, -2597, 6499, 5936, -15403], ![-1211, 1158, -4, 1, 0]], ![![-5, 7, -5, -5, 13], ![2, -1, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![5, -10, -1, 0, 1], ![8, -6, -12, -10, 27], ![-11, -7, 45, 40, -101], ![39, 4, -133, -131, 347], ![13, -6, -34, -34, 93]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N3 : Nat.card (O ⧸ I2N3) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N3)

lemma isPrimeI2N3 : Ideal.IsPrime I2N3 := prime_ideal_of_norm_prime hp2.out _ NI2N3
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![0, 18, 8, 5, -15]] ![![2, 0, 0, 0, 0], ![-5, 10, 5, 3, -9]]
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![-10, 20, 10, 6, -18]], ![![0, 36, 16, 10, -30], ![-6, -135, -38, -20, 66]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![337, 108, 0, 255, -756], ![56, 172, 0, 18, 0]]], ![![![570, 182, 0, 425, -1260], ![92, 286, 0, 30, 0]], ![![-1257, -424, 0, -934, 2772], ![-211, -632, 0, -66, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![-5, 10, 5, 3, -9]]
  ![![2, 0, 0, 0, 0], ![-6, -8, -3, -2, 6]] where
 M := ![![![4, 0, 0, 0, 0], ![-10, 20, 10, 6, -18]], ![![0, 2, 0, 0, 0], ![-6, -2, -3, -2, 6]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-155, 960, -330, -427, 891], ![230, 0, 0, 20, 0]]], ![![![-12, 100, -32, -42, 87], ![24, 0, 0, 2, 0]], ![![18, -88, 35, 44, -93], ![-21, 0, 0, -2, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![-6, -8, -3, -2, 6]] ![![2, 0, 0, 0, 0], ![-1, -9, -1, 0, 1]]
  ![![2, 0, 0, 0, 0], ![-6, -17, -4, -2, 7]] where
 M := ![![![4, 0, 0, 0, 0], ![-2, -18, -2, 0, 2]], ![![-12, -16, -6, -4, 12], ![14, 77, 30, 20, -59]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![5, 8, 3, 2, -6], ![2, 0, 0, 0, 0]]], ![![![0, 9, 1, 0, -1], ![2, 0, 0, 0, 0]], ![![-2, 13, 9, 7, -19], ![-3, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![-6, -17, -4, -2, 7]] ![![2, 0, 0, 0, 0], ![-1, -10, -1, 0, 1]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![-2, -20, -2, 0, 2]], ![![-12, -34, -8, -4, 14], ![14, 140, 58, 34, -104]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0]], ![![-1, -10, -1, 0, 1]]], ![![![-6, -17, -4, -2, 7]], ![![7, 70, 29, 17, -52]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N2, I2N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 1, 2, 0], ![-38, -14, -9, -28, 83], ![-12, -5, -1, -8, 27]]]
  hmulB := by decide  
  f := ![![![39, 24, -43, -84, -83], ![-30, -12, 168, 3, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, 0, -1, -1, 0], ![0, 1, 2, 0, 0]], ![![26, 16, -29, -56, -55], ![-20, -7, 112, 2, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![-2, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 1, 2, 0], ![-68, -14, -9, -28, 83], ![-22, -5, -1, -8, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 3, 1, 2, -8]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-5, 3, 1, 2, -8]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-5, 3, 1, 2, -8], ![20, 7, -6, 10, -50], ![220, 130, -39, 108, -520], ![958, 589, -161, 475, -2278], ![460, 284, -78, 230, -1103]]]
  hmulB := by decide  
  f := ![![![169, -23, 149, 116, -310]], ![![-173, 24, -153, -118, 316]], ![![1034, -148, 919, 704, -1888]], ![![-2223, 336, -1996, -1503, 4046]], ![![-576, 86, -516, -390, 1049]]]
  g := ![![![-4, 3, 1, 2, -8], ![5, 7, -6, 10, -50], ![20, 130, -39, 108, -520], ![72, 589, -161, 475, -2278], ![34, 284, -78, 230, -1103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![909, -117, 793, 626, -1668]] where
 M := ![![![9, 0, 0, 0, 0], ![0, 3, 0, 0, 0]], ![![0, 3, 0, 0, 0], ![0, 0, 1, 0, 0]]]
 hmul := by decide  
 g := ![![![![549, -621, -285, -168, 510]], ![![88, 117, 32, 18, -58]]], ![![![88, 117, 32, 18, -58]], ![![4, 42, 15, 8, -24]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![909, -117, 793, 626, -1668]] ![![-5, 3, 1, 2, -8]]
  ![![3, 0, 2, 2, -6]] where
 M := ![![![3, 0, 2, 2, -6]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![3, 0, 2, 2, -6]] ![![-5, 3, 1, 2, -8]]
  ![![-419, -257, 71, -208, 998]] where
 M := ![![![-419, -257, 71, -208, 998]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![-419, -257, 71, -208, 998]] ![![-5, 3, 1, 2, -8]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![272391, 167094, -46002, 135000, -647688]]]
 hmul := by decide  
 g := ![![![![90797, 55698, -15334, 45000, -215896]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-581, 75, -507, -400, 1066]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-581, 75, -507, -400, 1066]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-581, 75, -507, -400, 1066], ![2408, -311, 2102, 1658, -4418], ![-9988, 1286, -8713, -6876, 18328], ![25670, -3325, 22421, 17677, -47090], ![6432, -836, 5622, 4430, -11797]]]
  hmulB := by decide  
  f := ![![![-1, -553, -197, -114, 356]], ![![12, -37, -16, -10, 30]], ![![20, 2, 7, 8, -20]], ![![-42, 3, -25, -29, 72]], ![![-8, -498, -184, -110, 339]]]
  g := ![![![-969, 75, -507, -400, 1066], ![4016, -311, 2102, 1658, -4418], ![-16660, 1286, -8713, -6876, 18328], ![42806, -3325, 22421, 17677, -47090], ![10724, -836, 5622, 4430, -11797]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-581, 75, -507, -400, 1066]] ![![-581, 75, -507, -400, 1066]]
  ![![2170589, -280078, 1894360, 1494462, -3982594]] where
 M := ![![![2170589, -280078, 1894360, 1494462, -3982594]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![2170589, -280078, 1894360, 1494462, -3982594]] ![![-581, 75, -507, -400, 1066]]
  ![![-8109612781, 1046407827, -7077582225, -5583510930, 14879508396]] where
 M := ![![![-8109612781, 1046407827, -7077582225, -5583510930, 14879508396]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-8109612781, 1046407827, -7077582225, -5583510930, 14879508396]] ![![-581, 75, -507, -400, 1066]]
  ![![30298598766449, -3909519710928, 26442794499528, 20860744153336, -55591834877944]] where
 M := ![![![30298598766449, -3909519710928, 26442794499528, 20860744153336, -55591834877944]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![30298598766449, -3909519710928, 26442794499528, 20860744153336, -55591834877944]] ![![-581, 75, -507, -400, 1066]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-113199620327307845, 14606488912094275, -98793819503202475, -77938532276824200, 207698535829776850]]]
 hmul := by decide  
 g := ![![![![-22639924065461569, 2921297782418855, -19758763900640495, -15587706455364840, 41539707165955370]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![11, 37, 14, 9, -27]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0], ![11, 37, 14, 9, -27]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![3, 1, 5, 1, 0], ![5, 0, 4, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![11, 37, 14, 9, -27], ![-18, 20, -3, -8, 18], ![88, 4, 71, 74, -178], ![-382, -31, -242, -290, 757], ![-94, 9, -49, -68, 183]]]
  hmulB := by decide  
  f := ![![![422, -517, 58, 183, -405], ![7, 168, 0, 0, 0]], ![![-108, 121, -18, -48, 108], ![0, -42, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![167, -199, 25, 73, -162], ![2, 66, 0, 0, 0]], ![![303, -364, 44, 132, -293], ![4, 120, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-3, -1, -5, 7, 0], ![-5, 0, -4, 0, 7]], ![![17, 4, 11, 9, -27], ![-12, 4, -5, -8, 18], ![108, -10, 59, 74, -178], ![-471, 37, -260, -290, 757], ![-115, 11, -63, -68, 183]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [6, 5, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 4], [2, 2], [0, 1]]
 g := ![![[6, 5, 1], [1]], ![[2, 5, 2], [1]], ![[6, 4, 4], [1]]]
 h' := ![![[6, 4], [1, 2, 1], [0, 1]], ![[2, 2], [0, 0, 2], [6, 4]], ![[0, 1], [2, 5, 4], [2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3], []]
 b := ![[], [3, 3, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [6, 5, 6, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![76507635630, 44022196972, -8627783856, 39325071266, -179731386204]
  a := ![228, 83, 50, 161, -498]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![122455621836, 671017958, 73381772090, 39325071266, -179731386204]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 0, 2, 2, 0], ![-38, -14, -9, -27, 83], ![-12, -5, -1, -8, 28]]]
  hmulB := by decide  
  f := ![![![111, -15, -98, 21, -83], ![-504, 707, 21, 7, 0]], ![![108, -14, -95, 21, -83], ![-489, 686, 21, 7, 0]], ![![111, -13, -96, 21, -83], ![-505, 694, 21, 7, 0]], ![![0, -2, -3, -1, 0], ![1, 13, 4, 0, 0]], ![![96, -12, -84, 18, -71], ![-438, 606, 18, 6, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 7, 0, 0, 0], ![-6, 0, 7, 0, 0], ![-1, 0, 0, 7, 0], ![-6, 0, 0, 0, 7]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-2, 0, 2, 2, 0], ![-63, -14, -9, -27, 83], ![-23, -5, -1, -8, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-3, 1, 0, 0, 0], ![0, -3, 1, 0, 0], ![0, 0, -2, 2, 0], ![-38, -14, -9, -31, 83], ![-12, -5, -1, -8, 24]]]
  hmulB := by decide  
  f := ![![![19609, -19408, 4911, 113, -1245], ![44422, -30968, 1232, 105, 0]], ![![13068, -12930, 3271, 76, -830], ![29604, -20629, 819, 70, 0]], ![![19595, -19394, 4906, 115, -1245], ![44390, -30946, 1225, 105, 0]], ![![13075, -12938, 3274, 75, -830], ![29620, -20642, 823, 70, 0]], ![![16809, -16635, 4208, 98, -1067], ![38079, -26542, 1052, 90, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-4, 7, 0, 0, 0], ![-5, 0, 7, 0, 0], ![-5, 0, 0, 7, 0], ![-6, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![1, -3, 1, 0, 0], ![0, 0, -2, 2, 0], ![-40, -14, -9, -31, 83], ![-13, -5, -1, -8, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0, 0, 0], ![11, 37, 14, 9, -27]] ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![7, 0, 0, 0, 0], ![-21, -34, -10, -6, 19]] where
 M := ![![![49, 0, 0, 0, 0], ![7, 7, 0, 0, 0]], ![![77, 259, 98, 63, -189], ![-7, 57, 11, 1, -9]]]
 hmul := by decide  
 g := ![![![![7, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![1, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![-10, 3, 4, 3, -8], ![-7, 0, 0, 0, 0]], ![![2, 13, 3, 1, -4], ![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0, 0, 0], ![-21, -34, -10, -6, 19]] ![![7, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![49, 0, 0, 0, 0], ![-21, 7, 0, 0, 0]], ![![-147, -238, -70, -42, 133], ![63, 70, 21, 14, -42]]]
 hmul := by decide  
 g := ![![![![7, 0, 0, 0, 0]], ![![-3, 1, 0, 0, 0]]], ![![![-21, -34, -10, -6, 19]], ![![9, 10, 3, 2, -6]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-9, -12, -3, -2, 6]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![-9, -12, -3, -2, 6]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![3, 8, 1, 0, 0], ![3, 4, 0, 1, 0], ![1, 7, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-9, -12, -3, -2, 6], ![4, -11, -3, 2, -4], ![-28, -4, -28, -30, 58], ![236, 53, 104, 175, -491], ![64, 13, 19, 46, -142]]]
  hmulB := by decide  
  f := ![![![94293, -141994, -39046, 39596, -85448], ![34628, -179850, 220, 0, 0]], ![![329362, -496045, -136400, 138316, -298480], ![120934, -628254, 770, 0, 0]], ![![260975, -393042, -108077, 109596, -236504], ![95826, -497802, 610, 0, 0]], ![![145481, -219110, -60250, 61095, -131840], ![53416, -277506, 340, 0, 0]], ![![218162, -328579, -90351, 91618, -197707], ![80101, -416148, 510, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-3, -8, 11, 0, 0], ![-3, -4, 0, 11, 0], ![-1, -7, 0, 0, 11]], ![![0, -2, -3, -2, 6], ![1, 3, -3, 2, -4], ![8, -6, -28, -30, 58], ![-10, 178, 104, 175, -491], ![1, 61, 19, 46, -142]]]
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
  c := ![-5227557, -2211285, -594975, -3111900, 11679420]
  a := ![-271, -161, -59, -193, 592]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-526032, -6069075, -594975, -3111900, 11679420]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![3, 1, 0, 0, 0], ![0, 3, 1, 0, 0], ![0, 0, 4, 2, 0], ![-38, -14, -9, -25, 83], ![-12, -5, -1, -8, 30]]]
  hmulB := by decide  
  f := ![![![26492, -48415, -20896, -244, -2656], ![-92675, 210056, 5742, 352, 0]], ![![9930, -18154, -7836, -92, -996], ![-34737, 78760, 2156, 132, 0]], ![![6617, -12103, -5225, -62, -664], ![-23147, 52504, 1441, 88, 0]], ![![16554, -30263, -13062, -153, -1660], ![-57909, 131294, 3592, 220, 0]], ![![21681, -39612, -17098, -200, -2173], ![-75846, 171870, 4700, 288, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-3, 11, 0, 0, 0], ![-2, 0, 11, 0, 0], ![-7, 0, 0, 11, 0], ![-9, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-1, 3, 1, 0, 0], ![-2, 0, 4, 2, 0], ![-50, -14, -9, -25, 83], ![-19, -5, -1, -8, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![5, 1, 0, 0, 0]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![5, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![5, 1, 0, 0, 0], ![0, 5, 1, 0, 0], ![0, 0, 6, 2, 0], ![-38, -14, -9, -23, 83], ![-12, -5, -1, -8, 32]]]
  hmulB := by decide  
  f := ![![![10966, 774, 68856, 23353, -1245], ![-22869, 3333, -126544, 165, 0]], ![![6572, 462, 41311, 14011, -747], ![-13705, 2002, -75922, 99, 0]], ![![8764, 614, 55077, 18680, -996], ![-18276, 2674, -101222, 132, 0]], ![![8770, 617, 55086, 18683, -996], ![-18289, 2670, -101238, 132, 0]], ![![5976, 417, 37557, 12738, -679], ![-12462, 1827, -69024, 90, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-5, 11, 0, 0, 0], ![-8, 0, 11, 0, 0], ![-9, 0, 0, 11, 0], ![-6, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-3, 5, 1, 0, 0], ![-6, 0, 6, 2, 0], ![-17, -14, -9, -23, 83], ![-9, -5, -1, -8, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2

def I11N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] i)))

def SI11N3: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-5, 1, 0, 0, 0], ![0, -5, 1, 0, 0], ![0, 0, -4, 2, 0], ![-38, -14, -9, -33, 83], ![-12, -5, -1, -8, 22]]]
  hmulB := by decide  
  f := ![![![34720, -5540, 61603, -30228, -1494], ![74877, 2233, 169521, 198, 0]], ![![19296, -3078, 34225, -16794, -830], ![41614, 1243, 94182, 110, 0]], ![![27000, -4307, 47908, -23508, -1162], ![58228, 1739, 131835, 154, 0]], ![![15434, -2463, 27380, -13435, -664], ![33285, 992, 75345, 88, 0]], ![![15790, -2518, 28001, -13740, -679], ![34053, 1019, 77055, 90, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 11, 0, 0, 0], ![-8, 0, 11, 0, 0], ![-5, 0, 0, 11, 0], ![-5, 0, 0, 0, 11]], ![![-1, 1, 0, 0, 0], ![2, -5, 1, 0, 0], ![2, 0, -4, 2, 0], ![-12, -14, -9, -33, 83], ![-4, -5, -1, -8, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N3 : Nat.card (O ⧸ I11N3) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N3)

lemma isPrimeI11N3 : Ideal.IsPrime I11N3 := prime_ideal_of_norm_prime hp11.out _ NI11N3
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0, 0, 0], ![-9, -12, -3, -2, 6]] ![![11, 0, 0, 0, 0], ![3, 1, 0, 0, 0]]
  ![![35, -5, 31, 24, -64]] where
 M := ![![![121, 0, 0, 0, 0], ![33, 11, 0, 0, 0]], ![![-99, -132, -33, -22, 66], ![-23, -47, -12, -4, 14]]]
 hmul := by decide  
 g := ![![![![-1221, 2651, 1089, 638, -1958]], ![![-401, 690, 293, 172, -526]]], ![![![1487, -955, -512, -304, 910]], ![![463, -152, -107, -64, 188]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![35, -5, 31, 24, -64]] ![![11, 0, 0, 0, 0], ![5, 1, 0, 0, 0]]
  ![![11, 0, 0, 0, 0], ![-20, -49, -18, -11, 34]] where
 M := ![![![385, -55, 341, 264, -704], ![31, -6, 29, 22, -56]]]
 hmul := by decide  
 g := ![![![![35, -5, 31, 24, -64], ![0, 0, 0, 0, 0]], ![![21, 44, 19, 12, -36], ![10, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N2 : IdealMulLeCertificate' Table 
  ![![11, 0, 0, 0, 0], ![-20, -49, -18, -11, 34]] ![![11, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![121, 0, 0, 0, 0], ![-55, 11, 0, 0, 0]], ![![-220, -539, -198, -121, 374], ![110, 209, 88, 55, -165]]]
 hmul := by decide  
 g := ![![![![11, 0, 0, 0, 0]], ![![-5, 1, 0, 0, 0]]], ![![![-20, -49, -18, -11, 34]], ![![10, 19, 8, 5, -15]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N2, I11N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N2
    exact isPrimeI11N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1 ⊙ MulI11N2)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![1, 22, 11, 7, -21]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![1, 22, 11, 7, -21]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![10, 9, 11, 1, 0], ![7, 10, 5, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![1, 22, 11, 7, -21], ![-14, 8, -9, -6, 14], ![60, 0, 39, 38, -120], ![-32, 64, -111, -32, 17], ![6, 37, -27, 2, -41]]]
  hmulB := by decide  
  f := ![![![373, -348, 177, 120, -252], ![78, 351, 0, 0, 0]], ![![-42, 25, -27, -18, 42], ![0, -39, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![258, -247, 120, 81, -168], ![58, 243, 0, 0, 0]], ![![169, -158, 80, 54, -113], ![36, 159, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-10, -9, -11, 13, 0], ![-7, -10, -5, 0, 13]], ![![6, 13, 3, 7, -21], ![-4, -6, -1, -6, 14], ![40, 66, 17, 38, -120], ![13, 14, 12, -32, 17], ![21, 33, 12, 2, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [9, 8, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 9, 11], [11, 3, 2], [0, 1]]
 g := ![![[1], [2, 4], [1]], ![[2, 2, 1, 5], [10, 3], [7, 5, 1, 5]], ![[8, 2, 0, 8], [3, 4], [10, 5, 0, 8]]]
 h' := ![![[4, 9, 11], [11, 1], [4, 5, 2], [0, 1]], ![[11, 3, 2], [2, 9, 11], [1, 6, 9], [4, 9, 11]], ![[0, 1], [9, 3, 2], [6, 2, 2], [11, 3, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 4], []]
 b := ![[], [7, 9, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [9, 8, 11, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![832663533, 490532853, -110760745, 422427198, -1964662036]
  a := ![49, 16, 11, 34, -107]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![797001985, 1256562187, 389680789, 422427198, -1964662036]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![0, -2, -3, -2, 6]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![0, -2, -3, -2, 6]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![10, 5, 1, 0, 0], ![9, 3, 0, 1, 0], ![8, 1, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![0, -2, -3, -2, 6], ![4, -2, 7, 2, -4], ![-28, -4, -9, -10, 58], ![-144, -87, 14, -96, 339], ![-56, -37, 9, -34, 137]]]
  hmulB := by decide  
  f := ![![![-59007, 36414, -96517, -23782, 39574], ![38597, 196690, 702, 0, 0]], ![![-52416, 32349, -85734, -21124, 35148], ![34294, 174720, 624, 0, 0]], ![![-65046, 40141, -106395, -26216, 43624], ![42546, 216820, 774, 0, 0]], ![![-52947, 32675, -86604, -21339, 35508], ![34636, 176490, 630, 0, 0]], ![![-40344, 24897, -65990, -16260, 27057], ![26390, 134480, 480, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-10, -5, 13, 0, 0], ![-9, -3, 0, 13, 0], ![-8, -1, 0, 0, 13]], ![![0, 1, -3, -2, 6], ![-4, -3, 7, 2, -4], ![-24, 1, -9, -10, 58], ![-164, -16, 14, -96, 339], ![-72, -9, 9, -34, 137]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [7, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 12], [0, 1]]
 g := ![![[1, 9], [9], [6, 1]], ![[3, 4], [9], [12, 12]]]
 h' := ![![[6, 12], [11, 10], [10, 3], [0, 1]], ![[0, 1], [6, 3], [2, 10], [6, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [4, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [7, 7, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6007561, -2643656, -529450, -3506272, 13500866]
  a := ![-293, -88, -65, -209, 640]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5935657, -229112, -529450, -3506272, 13500866]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0, 0, 0], ![1, 22, 11, 7, -21]] ![![13, 0, 0, 0, 0], ![0, -2, -3, -2, 6]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![169, 0, 0, 0, 0], ![0, -26, -39, -26, 78]], ![![13, 286, 143, 91, -273], ![-52, 78, -39, -26, 52]]]
 hmul := by decide  
 g := ![![![![13, 0, 0, 0, 0]], ![![0, -2, -3, -2, 6]]], ![![![1, 22, 11, 7, -21]], ![![-4, 6, -3, -2, 4]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![47, 75, 29, 19, -57]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![47, 75, 29, 19, -57]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![14, 8, 11, 1, 0], ![11, 10, 13, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![47, 75, 29, 19, -57], ![-38, 66, -10, -18, 38], ![228, 24, 180, 180, -468], ![-726, 12, -564, -558, 1386], ![-150, 54, -122, -122, 290]]]
  hmulB := by decide  
  f := ![![![837, -1452, 220, 396, -836], ![0, 374, 0, 0, 0]], ![![-123, 58, -49, -55, 133], ![17, -34, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![648, -1142, 169, 307, -646], ![2, 292, 0, 0, 0]], ![![472, -901, 116, 225, -466], ![9, 222, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-14, -8, -11, 17, 0], ![-11, -10, -13, 0, 17]], ![![24, 29, 33, 19, -57], ![-12, -10, -18, -18, 38], ![168, 192, 252, 180, -468], ![-480, -552, -732, -558, 1386], ![-96, -110, -150, -122, 290]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [8, 6, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 16, 16], [3, 0, 1], [0, 1]]
 g := ![![[3, 9, 16], [5, 15], [13, 1], []], ![[16, 9, 3, 2], [1, 1], [], [15, 1]], ![[6, 1, 8, 9], [8, 2], [15, 1], [13, 1]]]
 h' := ![![[10, 16, 16], [15, 7, 4], [15, 16, 10], [0, 0, 1], [0, 1]], ![[3, 0, 1], [5, 14, 10], [9, 11, 1], [14, 1], [10, 16, 16]], ![[0, 1], [13, 13, 3], [14, 7, 6], [7, 16, 16], [3, 0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 6], []]
 b := ![[], [0, 10, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [8, 6, 4, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![211782603889, 119401998119, -20256792079, 110050227017, -495674907375]
  a := ![331, 121, 75, 237, -723]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![242559023928, 246808779749, 306644970977, 110050227017, -495674907375]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![-10, -6, -3, -2, 6]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![-10, -6, -3, -2, 6]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![10, 13, 1, 0, 0], ![15, 16, 0, 1, 0], ![14, 8, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![-10, -6, -3, -2, 6], ![4, -12, 3, 2, -4], ![-28, -4, -23, -18, 58], ![8, -31, 50, 6, 7], ![-8, -17, 13, -2, 19]]]
  hmulB := by decide  
  f := ![![![56105, -172360, 43156, 28888, -58304], ![-3740, -242556, 748, 0, 0]], ![![10180, -31275, 7831, 5242, -10580], ![-680, -44013, 136, 0, 0]], ![![40492, -124381, 31145, 20848, -42078], ![-2693, -175041, 540, 0, 0]], ![![59085, -181518, 45449, 30423, -61402], ![-3941, -255444, 788, 0, 0]], ![![50990, -156664, 39224, 26256, -52991], ![-3408, -220464, 680, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-10, -13, 17, 0, 0], ![-15, -16, 0, 17, 0], ![-14, -8, 0, 0, 17]], ![![-2, 1, -3, -2, 6], ![0, -3, 3, 2, -4], ![-20, 7, -23, -18, 58], ![-40, -49, 50, 6, 7], ![-22, -18, 13, -2, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [13, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 16], [0, 1]]
 g := ![![[8, 4], [15], [4], [1]], ![[0, 13], [15], [4], [1]]]
 h' := ![![[15, 16], [13, 15], [15, 10], [4, 15], [0, 1]], ![[0, 1], [0, 2], [12, 7], [8, 2], [15, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [5, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [13, 2, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1950459, -1093456, 177208, -1017128, 4560352]
  a := ![152, 56, 30, 98, -332]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3077091, -1388584, 177208, -1017128, 4560352]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0, 0, 0], ![47, 75, 29, 19, -57]] ![![17, 0, 0, 0, 0], ![-10, -6, -3, -2, 6]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![289, 0, 0, 0, 0], ![-170, -102, -51, -34, 102]], ![![799, 1275, 493, 323, -969], ![-374, -918, -374, -238, 714]]]
 hmul := by decide  
 g := ![![![![17, 0, 0, 0, 0]], ![![-10, -6, -3, -2, 6]]], ![![![47, 75, 29, 19, -57]], ![![-22, -54, -22, -14, 42]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![-44, -9, 5, 3, -8]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0], ![-44, -9, 5, 3, -8]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![15, 13, 16, 2, 1]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![-44, -9, 5, 3, -8], ![-18, -46, -23, -10, 33], ![-16, -43, -12, -30, 61], ![212, 71, 83, 179, -452], ![30, 7, 13, 42, -112]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![17, 4, -1, -1, 3], ![7, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-15, -13, -16, -2, 19]], ![![4, 5, 7, 1, -8], ![-27, -25, -29, -4, 33], ![-49, -44, -52, -8, 61], ![368, 313, 385, 57, -452], ![90, 77, 95, 14, -112]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [3, 6, 4, 4, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 14, 18, 10], [3, 4, 5, 9], [7, 0, 15], [0, 1]]
 g := ![![[11, 1, 7, 17], [10, 14, 6, 16], [1], []], ![[7, 14, 13, 12, 17, 8], [8, 3, 15, 18], [], [3, 17, 5]], ![[8, 0, 9, 16, 3, 9], [14, 5, 5, 6, 11, 11], [18, 7, 11], [6, 13, 5]], ![[0, 6, 17, 2, 18], [13, 6, 12, 11, 10], [17, 2, 11], [16]]]
 h' := ![![[5, 14, 18, 10], [8, 2, 8, 13], [16, 13, 15, 15], [0, 0, 1], [0, 1]], ![[3, 4, 5, 9], [1, 15, 17, 15], [9, 11, 6], [16, 14], [5, 14, 18, 10]], ![[7, 0, 15], [17, 10, 4, 1], [8, 10, 8, 15], [10, 6, 5, 7], [3, 4, 5, 9]], ![[0, 1], [0, 11, 9, 9], [7, 4, 9, 8], [1, 18, 13, 12], [7, 0, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [14, 8, 10], []]
 b := ![[], [], [18, 3, 11, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [3, 6, 4, 4, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-110463356645027100, -67049947001354974, 17606108750451908, -55086766402406805, 262118639205439558]
  a := ![-617, -216, -130, -435, 1348]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-212749628669822130, -182873276666951012, -219804848344030580, -30490739200699259, 262118639205439558]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![-3, 1, 0, 0, 0], ![0, -3, 1, 0, 0], ![0, 0, -2, 2, 0], ![-38, -14, -9, -31, 83], ![-12, -5, -1, -8, 24]]]
  hmulB := by decide  
  f := ![![![9964, -3086, 18189, -17974, -498], ![61655, 475, 172520, 114, 0]], ![![9958, -3084, 18189, -17974, -498], ![61618, 475, 172520, 114, 0]], ![![9946, -3080, 18169, -17954, -498], ![61544, 476, 172330, 114, 0]], ![![4984, -1542, 9095, -8988, -249], ![30840, 248, 86270, 57, 0]], ![![2624, -811, 4786, -4730, -131], ![16237, 136, 45400, 30, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-16, 19, 0, 0, 0], ![-10, 0, 19, 0, 0], ![-10, 0, 0, 19, 0], ![-5, 0, 0, 0, 19]], ![![-1, 1, 0, 0, 0], ![2, -3, 1, 0, 0], ![0, 0, -2, 2, 0], ![9, -14, -9, -31, 83], ![2, -5, -1, -8, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0, 0, 0], ![-44, -9, 5, 3, -8]] ![![19, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![361, 0, 0, 0, 0], ![-57, 19, 0, 0, 0]], ![![-836, -171, 95, 57, -152], ![114, -19, -38, -19, 57]]]
 hmul := by decide  
 g := ![![![![19, 0, 0, 0, 0]], ![![-3, 1, 0, 0, 0]]], ![![![-44, -9, 5, 3, -8]], ![![6, -1, -2, -1, 3]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-5, 28, 8, 5, -15]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![-5, 28, 8, 5, -15]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![20, 18, 6, 1, 0], ![7, 21, 3, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-5, 28, 8, 5, -15], ![-10, 0, 6, -4, 10], ![32, -4, 32, 44, -62], ![-480, -135, -169, -358, 1020], ![-146, -40, -26, -96, 306]]]
  hmulB := by decide  
  f := ![![![1576, -196, -980, 581, -1435], ![161, 3542, 0, 0, 0]], ![![-70, 1, 42, -28, 70], ![0, -161, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![1315, -166, -818, 484, -1195], ![137, 2954, 0, 0, 0]], ![![414, -49, -257, 153, -378], ![41, 931, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-20, -18, -6, 23, 0], ![-7, -21, -3, 0, 23]], ![![0, 11, 1, 5, -15], ![0, -6, 0, -4, 10], ![-18, 22, -2, 44, -62], ![-20, -657, -47, -358, 1020], ![-16, -206, -16, -96, 306]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [5, 21, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 17, 14], [4, 5, 9], [0, 1]]
 g := ![![[11, 18, 18], [10, 6, 6], [4, 18, 1], []], ![[16, 14, 13, 22], [1, 9, 12, 15], [15, 12, 21, 5], [2, 12]], ![[15, 13, 5, 4], [5, 13, 17, 9], [0, 13, 13, 2], [7, 12]]]
 h' := ![![[14, 17, 14], [19, 22, 15], [3, 10, 11], [0, 0, 1], [0, 1]], ![[4, 5, 9], [12, 4, 15], [4, 6, 11], [2, 6, 5], [14, 17, 14]], ![[0, 1], [6, 20, 16], [18, 7, 1], [4, 17, 17], [4, 5, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 16], []]
 b := ![[], [16, 13, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [5, 21, 5, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4618510, -891908, -2089659, -3246325, 9523500]
  a := ![-11, -8, -3, -9, 24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-276370, -6193546, -486183, -3246325, 9523500]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-10, 1, 0, 0, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![-10, 1, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-10, 1, 0, 0, 0], ![0, -10, 1, 0, 0], ![0, 0, -9, 2, 0], ![-38, -14, -9, -38, 83], ![-12, -5, -1, -8, 17]]]
  hmulB := by decide  
  f := ![![![820107, -4186317, 473081, -9398, -9296], ![1876455, -9444490, 157021, 2576, 0]], ![![468633, -2392154, 270337, -5372, -5312], ![1072261, -5396789, 89746, 1472, 0]], ![![585795, -2990165, 337914, -6714, -6640], ![1340335, -6745922, 112171, 1840, 0]], ![![351474, -1794126, 202754, -4029, -3984], ![804194, -4047616, 67310, 1104, 0]], ![![213954, -1092084, 123414, -2452, -2425], ![489540, -2463780, 40966, 672, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-13, 23, 0, 0, 0], ![-15, 0, 23, 0, 0], ![-10, 0, 0, 23, 0], ![-6, 0, 0, 0, 23]], ![![-1, 1, 0, 0, 0], ![5, -10, 1, 0, 0], ![5, 0, -9, 2, 0], ![7, -14, -9, -38, 83], ![2, -5, -1, -8, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-127, 98, 54, 34, -100]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![-127, 98, 54, 34, -100]] 
 ![![23, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-127, 98, 54, 34, -100], ![-92, -103, -54, -44, 122], ![208, -86, 117, 148, -358], ![-768, 6, -530, -597, 1488], ![-252, 22, -110, -132, 325]]]
  hmulB := by decide  
  f := ![![![-2017, 250, -1746, -1386, 3708]], ![![-1574, 189, -1354, -1080, 2898]], ![![-3482, 398, -2967, -2384, 6426]], ![![3608, -646, 3402, 2531, -6488]], ![![-643, -12, -428, -418, 1249]]]
  g := ![![![-77, 98, 54, 34, -100], ![56, -103, -54, -44, 122], ![244, -86, 117, 148, -358], ![-632, 6, -530, -597, 1488], ![-167, 22, -110, -132, 325]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0, 0, 0], ![-5, 28, 8, 5, -15]] ![![23, 0, 0, 0, 0], ![-10, 1, 0, 0, 0]]
  ![![2017, -250, 1746, 1386, -3708]] where
 M := ![![![529, 0, 0, 0, 0], ![-230, 23, 0, 0, 0]], ![![-115, 644, 184, 115, -345], ![40, -280, -74, -54, 160]]]
 hmul := by decide  
 g := ![![![![2921, -2254, -1242, -782, 2300]], ![![-1178, 1083, 594, 384, -1122]]], ![![![337, 4362, 1846, 1223, -3617]], ![![-280, -1840, -854, -602, 1740]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![2017, -250, 1746, 1386, -3708]] ![![-127, 98, 54, 34, -100]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![-23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)


lemma PB3690I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB3690I0 : PrimesBelowBoundCertificateInterval O 1 23 3690 where
  m := 9
  g := ![5, 5, 5, 3, 4, 2, 2, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB3690I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N3]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1, I11N2, I11N3]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1, I23N2]
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
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![343, 7, 7]
    · exact ![121, 11, 11, 11]
    · exact ![2197, 169]
    · exact ![4913, 289]
    · exact ![130321, 19]
    · exact ![12167, 23, 23]
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
      exact NI2N3
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
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
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N2
      exact NI11N3
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
  β := ![I2N0, I2N1, I2N2, I2N3, I3N0, I3N1, I5N0, I7N0, I7N1, I7N2, I11N0, I11N1, I11N2, I11N3, I13N0, I13N1, I17N1, I19N1, I23N1, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N3], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [I11N0, I11N1, I11N2, I11N3], [I13N0, I13N1], [I17N1], [I19N1], [I23N1, I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
