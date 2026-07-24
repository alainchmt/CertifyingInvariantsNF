
import IdealArithmetic.Examples.NF5_1_3037500000_7.RI5_1_3037500000_7
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![13, -4, 3, 4, 13]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![13, -4, 3, 4, 13]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![13, -4, 3, 4, 13], ![-24, -3, 3, 1, 4], ![-30, -10, -14, -5, -50], ![222, -164, 111, 138, 458], ![-80, 53, -31, -43, -134]]]
  hmulB := by decide  
  f := ![![![49323, 23792, -13727, -12868, -34026], ![5528, 6368, 604, 2, 0]], ![![24743, 11938, -6888, -6457, -17075], ![2774, 3195, 303, 1, 0]], ![![-24674, -11892, 6861, 6430, 17000], ![-2762, -3184, -302, -1, 0]], ![![-83, -36, 20, 19, 47], ![-8, -10, -1, 0, 0]], ![![24655, 11898, -6865, -6436, -17019], ![2765, 3184, 302, 1, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![0, -4, 3, 4, 13], ![-14, -3, 3, 1, 4], ![10, -10, -14, -5, -50], ![-118, -164, 111, 138, 458], ![27, 53, -31, -43, -134]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![2, 2, -1, -1, -3]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![2, 2, -1, -1, -3]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![2, 2, -1, -1, -3], ![-2, 12, -4, -7, -18], ![-110, 140, -81, -100, -330], ![152, 34, 10, 11, 48], ![-22, -41, 16, 19, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![1311, 730, -1498, -595, -3794], ![-2887, 888, -45, 0, 1]], ![![29, 14, -32, -12, -81], ![-64, 20, -1, 0, 0]], ![![5, -2, 0, 2, 3], ![-4, 1, 0, 0, 0]], ![![-27, -19, 34, 15, 89], ![63, -19, 1, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![1, 2, -1, -1, -3], ![-1, 12, -4, -7, -18], ![-55, 140, -81, -100, -330], ![76, 34, 10, 11, 48], ![-11, -41, 16, 19, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 0, 1, 5, 0], ![98, -82, 57, 69, 222], ![-32, 24, -17, -22, -67]]]
  hmulB := by decide  
  f := ![![![44, -5, 17, -18, 67], ![-22, -16, 16, 0, 2]], ![![42, -7, 16, -18, 67], ![-19, -14, 16, 0, 2]], ![![42, -7, 16, -23, 67], ![-19, -15, 18, 0, 2]], ![![0, 0, 1, 3, 0], ![1, -1, -1, 0, 0]], ![![22, -3, 8, -9, 34], ![-11, -7, 8, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-3, 0, 1, 5, 0], ![-84, -82, 57, 69, 222], ![25, 24, -17, -22, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![13, -4, 3, 4, 13]] ![![2, 0, 0, 0, 0], ![2, 2, -1, -1, -3]]
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![4, 4, -2, -2, -6]], ![![26, -8, 6, 8, 26], ![26, 1, 8, 6, 28]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![2, 3, -2, -1, -3], ![-2, 2, 0, 0, 0]]], ![![![13, -12, 4, -1, 13], ![16, -2, 2, 0, 0]], ![![13, 0, 6, -2, 14], ![1, -4, 2, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![2, 2, -1, -1, -3]]
  ![![2, 0, 0, 0, 0], ![14, -2, 2, 3, 10]] where
 M := ![![![4, 0, 0, 0, 0], ![4, 4, -2, -2, -6]], ![![0, 2, 0, 0, 0], ![-2, 12, -4, -7, -18]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, -2, -4, -1, -9], ![4, 2, 0, 0, 0]]], ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![2, -3, -7, -2, -16], ![7, 4, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![14, -2, 2, 3, 10]] ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![2, 0, 0, 0, 0], ![6, 0, 1, 1, 4]] where
 M := ![![![4, 0, 0, 0, 0], ![2, 2, 0, 0, 0]], ![![28, -4, 4, 6, 20], ![-12, 6, 1, -3, -4]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![1, 1, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![2, -2, 0, 1, 2], ![4, 0, 0, 0, 0]], ![![-3, 3, 1, -1, 0], ![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![6, 0, 1, 1, 4]] ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![2, 2, 0, 0, 0]], ![![12, 0, 2, 2, 8], ![-24, 20, -10, -14, -46]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0]], ![![1, 1, 0, 0, 0]]], ![![![6, 0, 1, 1, 4]], ![![-12, 10, -5, -7, -23]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 0, 1, 5, 0], ![98, -82, 57, 69, 222], ![-32, 24, -17, -22, -67]]]
  hmulB := by decide  
  f := ![![![210, -10, 167, 558, 268], ![-243, -15, -282, 0, 12]], ![![104, -6, 83, 279, 134], ![-119, -6, -141, 0, 6]], ![![210, -9, 167, 553, 268], ![-244, -17, -279, 0, 12]], ![![104, -6, 84, 281, 134], ![-118, -8, -142, 0, 6]], ![![140, -7, 111, 372, 179], ![-162, -9, -188, 0, 8]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![-2, 0, 0, 3, 0], ![-2, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-4, 0, 1, 5, 0], ![-172, -82, 57, 69, 222], ![52, 24, -17, -22, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![7, -1, 1, 1, 4]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![7, -1, 1, 1, 4]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![7, -1, 1, 1, 4], ![-30, 21, -12, -15, -50], ![130, 0, 16, 20, 70], ![-56, 34, -10, -20, -64], ![-30, -2, -6, -5, -19]]]
  hmulB := by decide  
  f := ![![![210521, 269923, -106642, -158321, -460006], ![-300402, -52875, -882, 6, 0]], ![![140106, 179643, -70974, -105368, -306150], ![-199926, -35190, -587, 4, 0]], ![![70656, 90592, -35791, -53136, -154388], ![-100822, -17746, -296, 2, 0]], ![![70169, 89975, -35548, -52774, -153338], ![-100132, -17625, -294, 2, 0]], ![![-4, -5, 2, 3, 9], ![6, 1, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![-1, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![2, -1, 1, 1, 4], ![-11, 21, -12, -15, -50], ![26, 0, 16, 20, 70], ![-28, 34, -10, -20, -64], ![-3, -2, -6, -5, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![13, -5, 3, 4, 13]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![13, -5, 3, 4, 13]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![13, -5, 3, 4, 13], ![-24, -3, 2, 1, 4], ![-30, -10, -14, -10, -50], ![124, -82, 54, 70, 236], ![-48, 29, -14, -21, -66]]]
  hmulB := by decide  
  f := ![![![70861, 29830, -15684, -14924, -49092], ![9090, 13188, 465, 0, 6]], ![![47089, 19824, -10423, -9918, -32625], ![6041, 8764, 309, 0, 4]], ![![94189, 39651, -20848, -19838, -65257], ![12083, 17530, 618, 0, 8]], ![![139, 68, -36, -35, -116], ![22, 28, 1, 0, 0]], ![![23616, 9945, -5229, -4976, -16368], ![3031, 4396, 155, 0, 2]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![-1, 0, 0, 3, 0], ![-1, 0, 0, 0, 3]], ![![0, -5, 3, 4, 13], ![-9, -3, 2, 1, 4], ![26, -10, -14, -10, -50], ![-42, -82, 54, 70, 236], ![3, 29, -14, -21, -66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] ![![3, 0, 0, 0, 0], ![7, -1, 1, 1, 4]]
  ![![3, 0, 0, 0, 0], ![6, 0, 1, 1, 4]] where
 M := ![![![9, 0, 0, 0, 0], ![21, -3, 3, 3, 12]], ![![3, 3, 0, 0, 0], ![-23, 20, -11, -14, -46]]]
 hmul := by decide  
 g := ![![![![147, 0, -16, 44, -4], ![318, 0, -18, 0, 0]], ![![-543, 19, -90, -104, -376], ![195, -3, 3, 0, 0]]], ![![![57, 21, -10, 6, -26], ![87, -3, -6, 0, 0]], ![![-245, -180, 15, 48, 112], ![237, 28, 1, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![6, 0, 1, 1, 4]] ![![3, 0, 0, 0, 0], ![13, -5, 3, 4, 13]]
  ![![3, 0, 0, 0, 0], ![7, -3, 2, 3, 9]] where
 M := ![![![9, 0, 0, 0, 0], ![39, -15, 9, 12, 39]], ![![18, 0, 3, 3, 12], ![-20, -6, 2, 0, 0]]]
 hmul := by decide  
 g := ![![![![-4, 3, -2, -3, -9], ![3, 0, 0, 0, 0]], ![![-118, -51, 32, 15, 76], ![69, -15, 0, 0, 0]]], ![![![-1, 3, -1, -2, -5], ![3, 0, 0, 0, 0]], ![![-53, -23, 14, 7, 33], ![25, -6, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![7, -3, 2, 3, 9]] ![![3, 0, 0, 0, 0], ![13, -5, 3, 4, 13]]
  ![![3, 0, 0, 0, 0], ![1, 2, -1, -1, -3]] where
 M := ![![![9, 0, 0, 0, 0], ![39, -15, 9, 12, 39]], ![![21, -9, 6, 9, 27], ![43, -31, 23, 26, 93]]]
 hmul := by decide  
 g := ![![![![2, -2, 1, 1, 3], ![3, 0, 0, 0, 0]], ![![14, -3, 2, 3, 10], ![-3, 0, 0, 0, 0]]], ![![![8, -1, 1, 2, 6], ![-3, 0, 0, 0, 0]], ![![18, -3, 4, 5, 20], ![-11, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![1, 2, -1, -1, -3]] ![![3, 0, 0, 0, 0], ![13, -5, 3, 4, 13]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![9, 0, 0, 0, 0], ![39, -15, 9, 12, 39]], ![![3, 6, -3, -3, -9], ![15, -6, 9, 9, 33]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0]], ![![13, -5, 3, 4, 13]]], ![![![1, 2, -1, -1, -3]], ![![5, -2, 3, 3, 11]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N2, I3N2, I3N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N2
    exact isPrimeI3N2
    exact isPrimeI3N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0, 0], ![12, -5, 3, 4, 13]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0, 0, 0], ![12, -5, 3, 4, 13]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![5, 0, 0, 0, 0], ![0, 5, 0, 0, 0], ![0, 0, 5, 0, 0], ![0, 0, 0, 5, 0], ![0, 0, 0, 0, 5]], ![![12, -5, 3, 4, 13], ![-24, -4, 2, 1, 4], ![-30, -10, -15, -10, -50], ![124, -82, 54, 69, 236], ![-48, 29, -14, -21, -67]]]
  hmulB := by decide  
  f := ![![![18911585, 7151715, -3842930, -3332395, -11602229], ![3098640, 5404100, 0, -16460, 45]], ![![1268400, 479674, -257750, -223509, -778179], ![207832, 362456, 0, -1104, 3]], ![![1250056, 472731, -254019, -220273, -766913], ![204822, 357212, 0, -1088, 3]], ![![-1254660, -474462, 254949, 221078, 769716], ![-205569, -358524, 0, 1092, -3]], ![![15129268, 5721372, -3074344, -2665916, -9281783], ![2478912, 4323280, 0, -13168, 36]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 5, 0, 0, 0], ![0, 0, 5, 0, 0], ![0, 0, 0, 5, 0], ![-4, 0, 0, 0, 5]], ![![-8, -5, 3, 4, 13], ![-8, -4, 2, 1, 4], ![34, -10, -15, -10, -50], ![-164, -82, 54, 69, 236], ![44, 29, -14, -21, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![12, -5, 3, 4, 13]] ![![5, 0, 0, 0, 0], ![12, -5, 3, 4, 13]]
  ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] where
 M := ![![![25, 0, 0, 0, 0], ![60, -25, 15, 20, 65]], ![![60, -25, 15, 20, 65], ![46, -21, 15, 16, 59]]]
 hmul := by decide  
 g := ![![![![1475, -1183, 0, 1020, 3330], ![-235, 4275, 0, -75, 0]], ![![3540, -2844, 0, 2452, 8005], ![-565, 10275, 0, -180, 0]]], ![![![3540, -2844, 0, 2452, 8005], ![-565, 10275, 0, -180, 0]], ![![2714, -2181, 0, 1880, 6139], ![-432, 7881, 0, -138, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![5, 0, 0, 0, 0], ![12, -5, 3, 4, 13]]
  ![![5, 0, 0, 0, 0], ![6, 1, 1, 1, 4]] where
 M := ![![![25, 0, 0, 0, 0], ![60, -25, 15, 20, 65]], ![![0, 5, 0, 0, 0], ![-24, -4, 2, 1, 4]]]
 hmul := by decide  
 g := ![![![![-873, -3213, 1467, 1687, 5148], ![3065, 0, 0, -100, 0]], ![![-1572, -5789, 2643, 3040, 9277], ![5520, 0, 0, -180, 0]]], ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![904, 3340, -1526, -1755, -5356], ![-3184, 0, 0, 104, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![6, 1, 1, 1, 4]] ![![5, 0, 0, 0, 0], ![12, -5, 3, 4, 13]]
  ![![5, 0, 0, 0, 0], ![15, -5, 3, 5, 15]] where
 M := ![![![25, 0, 0, 0, 0], ![60, -25, 15, 20, 65]], ![![30, 5, 5, 5, 20], ![-50, -10, 3, 0, 0]]]
 hmul := by decide  
 g := ![![![![5, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-3, 0, 0, -1, -2], ![5, 0, 0, 0, 0]]], ![![![-9, 6, -2, -4, -11], ![5, 0, 0, 0, 0]], ![![-13, -1, 0, -1, -3], ![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![15, -5, 3, 5, 15]] ![![5, 0, 0, 0, 0], ![12, -5, 3, 4, 13]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![25, 0, 0, 0, 0], ![60, -25, 15, 20, 65]], ![![75, -25, 15, 25, 75], ![110, -60, 50, 55, 200]]]
 hmul := by decide  
 g := ![![![![5, 0, 0, 0, 0]], ![![12, -5, 3, 4, 13]]], ![![![15, -5, 3, 5, 15]], ![![22, -12, 10, 11, 40]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1348985, -455224, 261647, 321917, 1090956]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![1348985, -455224, 261647, 321917, 1090956]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![6, 0, 6, 6, 1]] where
  M :=![![![1348985, -455224, 261647, 321917, 1090956], ![-3362726, 1134735, -652207, -802441, -2719434], ![8382670, -2828980, 1625976, 2000525, 6779610], ![-4179214, 1410052, -810485, -997168, -3379386], ![-2662846, 898702, -516527, -635513, -2153693]]]
  hmulB := by decide  
  f := ![![![-1473, 352, -275, -431, -1380]], ![![1922, 749, -755, -323, -1842]], ![![27290, -15800, 13652, 14785, 53550]], ![![-52934, 20024, -16681, -20892, -71826]], ![![-21572, 3602, -2593, -5173, -15521]]]
  g := ![![![-742393, -65032, -897727, -889117, 1090956], ![1850554, 162105, 2237771, 2216309, -2719434], ![-4613570, -404140, -5578812, -5525305, 6779610], ![2299586, 201436, 2780833, 2754164, -3379386], ![1465616, 128386, 1772233, 1755235, -2153693]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [6, 1, 0, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 4, 5, 6], [1, 6], [1, 3, 2, 1], [0, 1]]
 g := ![![[0, 4, 2, 1], []], ![[1, 6, 3, 4, 4, 3], [4, 4, 2, 5, 6, 6]], ![[0, 3, 5, 6], []], ![[0, 1, 6, 6, 5, 4], [6, 0, 1, 2, 1, 1]]]
 h' := ![![[0, 4, 5, 6], [0, 0, 0, 1], [0, 1]], ![[1, 6], [4, 0, 5, 5], [0, 4, 5, 6]], ![[1, 3, 2, 1], [1, 4, 3, 6], [1, 6]], ![[0, 1], [0, 3, 6, 2], [1, 3, 2, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3], []]
 b := ![[], [], [4, 5, 3, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [6, 1, 0, 5, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5789637479, 22458938439, -9882907779, -12765836856, -42371073735]
  a := ![-245, 204, -143, -171, -555]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![35490972133, 3208419777, 34906219233, 34494372222, -42371073735]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1473, -352, 275, 431, 1380]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![1473, -352, 275, 431, 1380]] 
 ![![7, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![1473, -352, 275, 431, 1380], ![-1922, -749, 755, 323, 1842], ![-27290, 15800, -13652, -14785, -53550], ![52934, -20024, 16681, 20892, 71826], ![-11698, 2242, -1673, -3017, -9289]]]
  hmulB := by decide  
  f := ![![![-1348985, 455224, -261647, -321917, -1090956]], ![![-97747, 32991, -18962, -23330, -79062]], ![![-2161085, 729300, -419173, -515730, -1747770]], ![![-173818, 58692, -33729, -41500, -140634]], ![![-390442, 131742, -75723, -93165, -315733]]]
  g := ![![![-870, -352, 275, 431, 1380], ![-1730, -749, 755, 323, 1842], ![38130, 15800, -13652, -14785, -53550], ![-48753, -20024, 16681, 20892, 71826], ![5595, 2242, -1673, -3017, -9289]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![1348985, -455224, 261647, 321917, 1090956]] ![![1473, -352, 275, 431, 1380]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![-7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![30, -15, 7, 10, 32]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![30, -15, 7, 10, 32]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![3, 4, 4, 1, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![30, -15, 7, 10, 32], ![-44, -22, 11, 11, 44], ![-330, 110, -143, -165, -550], ![286, 0, 11, 33, 154], ![-40, -24, 31, 27, 82]]]
  hmulB := by decide  
  f := ![![![-29, 15, -7, -10, -32], ![11, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![-27, 14, -6, -9, -29], ![10, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-3, -4, -4, -1, 11]], ![![-6, -13, -11, -2, 32], ![-16, -18, -15, -3, 44], ![120, 210, 187, 35, -550], ![-16, -56, -55, -11, 154], ![-26, -32, -27, -5, 82]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 4 2 3 [4, 5, 10, 4, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 10, 7, 10], [2, 9, 7, 1], [9, 2, 8], [0, 1]]
 g := ![![[1, 8, 1, 3], [7, 1], []], ![[2, 9, 7, 0, 5, 8], [10, 2, 3, 9, 5, 2], [3, 4, 1]], ![[8, 6, 9, 7, 3, 1], [7, 9, 1, 2, 4, 1], [6, 10, 1]], ![[4, 6, 6], [1, 2, 7, 10, 7], [9]]]
 h' := ![![[7, 10, 7, 10], [5, 5, 2, 6], [0, 0, 1], [0, 1]], ![[2, 9, 7, 1], [6, 2, 6, 6], [4, 10, 1, 3], [7, 10, 7, 10]], ![[9, 2, 8], [2, 1, 0, 10], [2, 10, 6, 1], [2, 9, 7, 1]], ![[0, 1], [5, 3, 3], [1, 2, 3, 7], [9, 2, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [8, 0, 5], []]
 b := ![[], [], [1, 9, 4, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 4
  hpos := by decide
  P := [4, 5, 10, 4, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![422488532, -21160568123, 8972104414, 11538336661, 36497009136]
  a := ![249, -271, 146, 173, 564]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9915321716, -15195327697, -12455993830, -2268970225, 36497009136]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 14641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 5, 0], ![98, -82, 57, 68, 222], ![-32, 24, -17, -22, -68]]]
  hmulB := by decide  
  f := ![![![99, -246, 112, 53, 222], ![1804, -605, 33, -11, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, 0, 0, -4, 0], ![0, 0, 9, 0, 0]], ![![45, -111, 50, 25, 101], ![811, -265, 13, -5, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![-5, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 5, 0], ![-92, -82, 57, 68, 222], ![28, 24, -17, -22, -68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0, 0, 0], ![30, -15, 7, 10, 32]] ![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![121, 0, 0, 0, 0], ![0, 11, 0, 0, 0]], ![![330, -165, 77, 110, 352], ![-44, -22, 11, 11, 44]]]
 hmul := by decide  
 g := ![![![![11, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]]], ![![![30, -15, 7, 10, 32]], ![![-4, -2, 1, 1, 4]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![30, 0, 4, 5, 18]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![30, 0, 4, 5, 18]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![6, 0, 6, 1, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![30, 0, 4, 5, 18], ![-86, 52, -21, -36, -114], ![120, 130, -62, -45, -240], ![654, -390, 329, 382, 1266], ![-290, 104, -95, -122, -382]]]
  hmulB := by decide  
  f := ![![![-29, 0, -4, -5, -18], ![13, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![-18, 0, -2, -3, -11], ![8, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-6, 0, -6, -1, 13]], ![![-6, 0, -8, -1, 18], ![46, 4, 51, 6, -114], ![120, 10, 106, 15, -240], ![-534, -30, -559, -68, 1266], ![154, 8, 169, 20, -382]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 4 2 3 [3, 11, 0, 10, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 12, 9, 12], [1, 12, 10, 6], [6, 1, 7, 8], [0, 1]]
 g := ![![[10, 3, 6, 9], [9, 3, 1], []], ![[5, 1, 7, 10, 3, 4], [10], [0, 8, 0, 8, 11, 12]], ![[1, 11, 4, 8, 10, 2], [0, 3, 12], [7, 8, 7, 12, 12, 8]], ![[0, 4, 1, 1, 0, 7], [0, 2, 3], [7, 8, 2, 11, 7, 5]]]
 h' := ![![[9, 12, 9, 12], [12, 9, 3, 3], [0, 0, 0, 1], [0, 1]], ![[1, 12, 10, 6], [10, 6, 11, 10], [1, 6, 7], [9, 12, 9, 12]], ![[6, 1, 7, 8], [10, 4, 7, 3], [6, 0, 2, 8], [1, 12, 10, 6]], ![[0, 1], [0, 7, 5, 10], [0, 7, 4, 4], [6, 1, 7, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 6, 1], []]
 b := ![[], [], [5, 11, 7, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 4
  hpos := by decide
  P := [3, 11, 0, 10, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-75819425, 146680300, -66658949, -90564475, -291349800]
  a := ![-64, 51, -37, -45, -145]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![128636875, 11283100, 129341527, 15445025, -291349800]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 28561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![2, 1, 0, 0, 0], ![0, 2, 1, 0, 0], ![0, 0, 2, 5, 0], ![98, -82, 57, 70, 222], ![-32, 24, -17, -22, -66]]]
  hmulB := by decide  
  f := ![![![14655, 6609, -55463, -140595, 2664], ![-87607, -5551, 367731, -156, 0]], ![![2442, 1101, -9237, -23415, 444], ![-14598, -923, 61243, -26, 0]], ![![10989, 4955, -41601, -105455, 1998], ![-65691, -4159, 275821, -117, 0]], ![![13434, 6058, -50841, -128878, 2442], ![-80308, -5086, 337085, -143, 0]], ![![1127, 507, -4267, -10815, 205], ![-6737, -419, 28287, -12, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 13, 0, 0, 0], ![-9, 0, 13, 0, 0], ![-12, 0, 0, 13, 0], ![-1, 0, 0, 0, 13]], ![![0, 1, 0, 0, 0], ![-1, 2, 1, 0, 0], ![-6, 0, 2, 5, 0], ![-101, -82, 57, 70, 222], ![31, 24, -17, -22, -66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0, 0, 0], ![30, 0, 4, 5, 18]] ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![169, 0, 0, 0, 0], ![26, 13, 0, 0, 0]], ![![390, 0, 52, 65, 234], ![-26, 52, -13, -26, -78]]]
 hmul := by decide  
 g := ![![![![13, 0, 0, 0, 0]], ![![2, 1, 0, 0, 0]]], ![![![30, 0, 4, 5, 18]], ![![-2, 4, -1, -2, -6]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![-14, -7, -1, 0, -3]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![-14, -7, -1, 0, -3]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![13, 5, 1, 1, 0], ![16, 8, 6, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![-14, -7, -1, 0, -3], ![96, -86, 44, 61, 204], ![-550, -10, -77, -120, -330], ![-240, 274, -248, -257, -840], ![264, -107, 112, 131, 419]]]
  hmulB := by decide  
  f := ![![![4865, -8422, 3356, 4941, 15900], ![-3536, -1377, 0, 0, 0]], ![![-528, 943, -372, -549, -1764], ![408, 153, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![3565, -6163, 2457, 3617, 11640], ![-2584, -1008, 0, 0, 0]], ![![4332, -7482, 2984, 4392, 14135], ![-3134, -1224, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-13, -5, -1, 17, 0], ![-16, -8, -6, 0, 17]], ![![2, 1, 1, 0, -3], ![-233, -119, -73, 61, 204], ![370, 190, 119, -120, -330], ![973, 487, 297, -257, -840], ![-479, -242, -149, 131, 419]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [9, 3, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 0, 6], [13, 16, 11], [0, 1]]
 g := ![![[14, 16, 16], [9, 1], [6, 1], []], ![[8, 5, 0, 11], [13, 13], [12, 1], [12, 2]], ![[9, 15, 16, 7], [0, 13], [], [7, 2]]]
 h' := ![![[10, 0, 6], [13, 7, 4], [14, 7, 16], [0, 0, 1], [0, 1]], ![[13, 16, 11], [0, 5, 4], [7, 3, 9], [9, 14, 16], [10, 0, 6]], ![[0, 1], [1, 5, 9], [16, 7, 9], [4, 3], [13, 16, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 11], []]
 b := ![[], [3, 1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [9, 3, 11, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![93952892, 2178782, 10176726, 7178683, 65614652]
  a := ![377, -296, 220, 261, 854]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-61717907, -32860697, -22981757, 7178683, 65614652]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![10, 4, 1, 1, 4]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![10, 4, 1, 1, 4]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![9, 12, 1, 0, 0], ![9, 7, 0, 1, 0], ![15, 9, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![10, 4, 1, 1, 4], ![-30, 24, -7, -15, -50], ![130, 0, 19, 45, 70], ![434, -376, 275, 323, 1046], ![-190, 118, -91, -115, -356]]]
  hmulB := by decide  
  f := ![![![22642391, -31835612, 6807875, 15896239, 52218456], ![19450567, 19308464, -1326, 0, 0]], ![![56600250, -79580951, 17017963, 39736569, 130532906], ![48621462, 48266264, -3315, 0, 0]], ![![51718297, -72716856, 15550111, 36309168, 119274042], ![44427729, 44103152, -3029, 0, 0]], ![![35293127, -49622777, 10611565, 24777772, 81393906], ![30317972, 30096472, -2067, 0, 0]], ![![49943415, -70221339, 15016458, 35063100, 115180763], ![42903045, 42589608, -2925, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-9, -12, 17, 0, 0], ![-9, -7, 0, 17, 0], ![-15, -9, 0, 0, 17]], ![![-4, -3, 1, 1, 4], ![54, 39, -7, -15, -50], ![-88, -69, 19, 45, 70], ![-1214, -903, 275, 323, 1046], ![412, 307, -91, -115, -356]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [12, 2, 1] where
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
 g := ![![[3, 13], [2], [4], [1]], ![[11, 4], [2], [4], [1]]]
 h' := ![![[15, 16], [12, 9], [11, 6], [5, 15], [0, 1]], ![[0, 1], [11, 8], [16, 11], [9, 2], [15, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [7, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [12, 2, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-269073, -31892, -62607, -51704, -212736]
  a := ![-475, 397, -276, -328, -1076]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![232398, 176232, -62607, -51704, -212736]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0, 0, 0], ![-14, -7, -1, 0, -3]] ![![17, 0, 0, 0, 0], ![10, 4, 1, 1, 4]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![289, 0, 0, 0, 0], ![170, 68, 17, 17, 68]], ![![-238, -119, -17, 0, -51], ![510, -578, 289, 391, 1292]]]
 hmul := by decide  
 g := ![![![![17, 0, 0, 0, 0]], ![![10, 4, 1, 1, 4]]], ![![![-14, -7, -1, 0, -3]], ![![30, -34, 17, 23, 76]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![0, -1, 1, 1, 4]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0], ![0, -1, 1, 1, 4]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![16, 0, 1, 0, 0], ![0, 7, 0, 1, 0], ![15, 17, 0, 0, 1]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![0, -1, 1, 1, 4], ![-30, 14, -12, -15, -50], ![130, 0, 9, 20, 70], ![-56, 34, -10, -27, -64], ![-30, -2, -6, -5, -26]]]
  hmulB := by decide  
  f := ![![![938961, -417156, 354912, 448768, 1482752], ![376428, 593028, -380, 0, 0]], ![![3378960, -1501185, 1277194, 1614946, 5335864], ![1354586, 2134080, -1368, 0, 0]], ![![780824, -346900, 295139, 373188, 1233032], ![313028, 493152, -316, 0, 0]], ![![1244880, -553068, 470545, 594980, 1965844], ![499061, 786240, -504, 0, 0]], ![![3764565, -1672500, 1422947, 1799243, 5944791], ![1509163, 2377620, -1524, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-16, 0, 19, 0, 0], ![0, -7, 0, 19, 0], ![-15, -17, 0, 0, 19]], ![![-4, -4, 1, 1, 4], ![48, 51, -12, -15, -50], ![-56, -70, 9, 20, 70], ![56, 69, -10, -27, -64], ![24, 25, -6, -5, -26]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [15, 6, 1] where
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
 g := ![![[8, 17], [8, 4], [17], [1]], ![[1, 2], [3, 15], [17], [1]]]
 h' := ![![[13, 18], [13, 13], [8, 2], [4, 13], [0, 1]], ![[0, 1], [11, 6], [15, 17], [2, 6], [13, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [5, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [15, 6, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12081, 51424, -51028, -42556, -166944]
  a := ![294, -246, 172, 194, 666]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![174133, 167756, -51028, -42556, -166944]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![0, -4, 1, 1, 4]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0], ![0, -4, 1, 1, 4]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![13, 15, 1, 0, 0], ![18, 7, 0, 1, 0], ![16, 3, 0, 0, 1]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![0, -4, 1, 1, 4], ![-30, 14, -15, -15, -50], ![130, 0, 9, 5, 70], ![-350, 280, -181, -231, -730], ![66, -74, 45, 61, 178]]]
  hmulB := by decide  
  f := ![![![1971421, -727528, 935878, 935710, 3089620], ![902120, 1245108, -798, 0, 0]], ![![1971060, -727391, 935706, 935538, 3089052], ![901968, 1244880, -798, 0, 0]], ![![2897557, -1069307, 1375536, 1375289, 4541066], ![1325914, 1830036, -1173, 0, 0]], ![![2593842, -957223, 1231355, 1231134, 4065080], ![1186945, 1638216, -1050, 0, 0]], ![![1971364, -727507, 935851, 935683, 3089531], ![902093, 1245072, -798, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-13, -15, 19, 0, 0], ![-18, -7, 0, 19, 0], ![-16, -3, 0, 0, 19]], ![![-5, -2, 1, 1, 4], ![65, 26, -15, -15, -50], ![-63, -20, 9, 5, 70], ![939, 358, -181, -231, -730], ![-235, -90, 45, 61, 178]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [3, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 18], [0, 1]]
 g := ![![[3, 7], [18, 5], [5], [1]], ![[16, 12], [11, 14], [5], [1]]]
 h' := ![![[10, 18], [3, 11], [13, 9], [16, 10], [0, 1]], ![[0, 1], [18, 8], [8, 10], [2, 9], [10, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [4, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [3, 9, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11683, -90634, 40999, 53859, 164916]
  a := ![99, -78, 61, 75, 224]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-217338, -83020, 40999, 53859, 164916]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![4, 1, 0, 0, 0], ![0, 4, 1, 0, 0], ![0, 0, 4, 5, 0], ![98, -82, 57, 72, 222], ![-32, 24, -17, -22, -64]]]
  hmulB := by decide  
  f := ![![![495753, -1486526, -407523, -10558, 30192], ![-2291514, 7580905, 77330, -2584, 0]], ![![116644, -349771, -95889, -2486, 7104], ![-539162, 1783739, 18202, -608, 0]], ![![87477, -262335, -71920, -1867, 5328], ![-404343, 1337829, 13661, -456, 0]], ![![233287, -699551, -191777, -4968, 14208], ![-1078319, 3567519, 36389, -1216, 0]], ![![469662, -1408290, -386074, -10001, 28603], ![-2170914, 7181922, 73255, -2448, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-4, 19, 0, 0, 0], ![-3, 0, 19, 0, 0], ![-9, 0, 0, 19, 0], ![-18, 0, 0, 0, 19]], ![![0, 1, 0, 0, 0], ![-1, 4, 1, 0, 0], ![-3, 0, 4, 5, 0], ![-231, -82, 57, 72, 222], ![67, 24, -17, -22, -64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0, 0, 0], ![0, -1, 1, 1, 4]] ![![19, 0, 0, 0, 0], ![0, -4, 1, 1, 4]]
  ![![19, 0, 0, 0, 0], ![34, -3, 8, 9, 33]] where
 M := ![![![361, 0, 0, 0, 0], ![0, -76, 19, 19, 76]], ![![0, -19, 19, 19, 76], ![74, -30, 23, 33, 102]]]
 hmul := by decide  
 g := ![![![![-15, 3, -8, -9, -33], ![19, 0, 0, 0, 0]], ![![0, -4, 1, 1, 4], ![0, 0, 0, 0, 0]]], ![![![0, -1, 1, 1, 4], ![0, 0, 0, 0, 0]], ![![-14, 0, -3, -3, -12], ![10, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![19, 0, 0, 0, 0], ![34, -3, 8, 9, 33]] ![![19, 0, 0, 0, 0], ![4, 1, 0, 0, 0]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![361, 0, 0, 0, 0], ![76, 19, 0, 0, 0]], ![![646, -57, 152, 171, 627], ![-38, 76, -19, -38, -114]]]
 hmul := by decide  
 g := ![![![![19, 0, 0, 0, 0]], ![![4, 1, 0, 0, 0]]], ![![![34, -3, 8, 9, 33]], ![![-2, 4, -1, -2, -6]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![13, -6, 1, 1, 4]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![13, -6, 1, 1, 4]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![2, 15, 1, 0, 0], ![17, 6, 0, 1, 0], ![10, 22, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![13, -6, 1, 1, 4], ![-30, 27, -17, -15, -50], ![130, 0, 22, -5, 70], ![-546, 444, -295, -354, -1174], ![130, -122, 79, 105, 327]]]
  hmulB := by decide  
  f := ![![![488942, -615075, 473514, 413872, 1359978], ![711919, 682157, -276, 0, 0]], ![![2443138, -3073388, 2366039, 2068021, 6795494], ![3557272, 3408577, -1380, 0, 0]], ![![1630550, -2051184, 1579100, 1380202, 4535328], ![2374144, 2274893, -921, 0, 0]], ![![998730, -1256373, 967216, 845389, 2777938], ![1454189, 1393397, -564, 0, 0]], ![![2549493, -3207184, 2469043, 2158051, 7091331], ![3712147, 3556968, -1440, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-2, -15, 23, 0, 0], ![-17, -6, 0, 23, 0], ![-10, -22, 0, 0, 23]], ![![-2, -5, 1, 1, 4], ![33, 64, -17, -15, -50], ![-23, -80, 22, -5, 70], ![774, 1427, -295, -354, -1174], ![-221, -397, 79, 105, 327]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [6, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 22], [0, 1]]
 g := ![![[16, 4], [14, 16], [7, 16], [1]], ![[0, 19], [19, 7], [12, 7], [1]]]
 h' := ![![[19, 22], [8, 2], [4, 4], [17, 19], [0, 1]], ![[0, 1], [0, 21], [11, 19], [10, 4], [19, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [12, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [6, 4, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6395, 1146, -4137, -3262, -12922]
  a := ![113, -98, 66, 77, 256]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8111, 15959, -4137, -3262, -12922]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![5, 1, 1, 1, 4]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![5, 1, 1, 1, 4]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![10, 13, 1, 0, 0], ![20, 5, 0, 1, 0], ![11, 13, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![5, 1, 1, 1, 4], ![-30, 19, -10, -15, -50], ![130, 0, 14, 30, 70], ![140, -130, 104, 114, 380], ![-94, 46, -40, -49, -157]]]
  hmulB := by decide  
  f := ![![![143253181, -104493130, 49949340, 76580966, 253055824], ![76109852, 122485902, -6118, 0, 0]], ![![158327590, -115488850, 55205466, 84639515, 279684670], ![84118820, 135374987, -6762, 0, 0]], ![![151445695, -110468995, 52805896, 80960560, 267527850], ![80462515, 129490757, -6468, 0, 0]], ![![158987025, -115969863, 55435397, 84992039, 280849558], ![84469179, 135938825, -6790, 0, 0]], ![![158001897, -115251282, 55091904, 84465405, 279109337], ![83945790, 135096511, -6748, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-10, -13, 23, 0, 0], ![-20, -5, 0, 23, 0], ![-11, -13, 0, 0, 23]], ![![-3, -3, 1, 1, 4], ![40, 38, -10, -15, -50], ![-60, -54, 14, 30, 70], ![-320, -304, 104, 114, 380], ![131, 124, -40, -49, -157]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [20, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 22], [0, 1]]
 g := ![![[17, 12], [9, 18], [17, 2], [1]], ![[8, 11], [7, 5], [4, 21], [1]]]
 h' := ![![[5, 22], [4, 9], [5, 8], [3, 5], [0, 1]], ![[0, 1], [3, 14], [22, 15], [5, 18], [5, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [2, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [20, 18, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-108191, -115254, -5878, 25062, 30054]
  a := ![445, -371, 263, 306, 1008]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-38315, -24124, -5878, 25062, 30054]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-5, 1, 0, 0, 0], ![0, -5, 1, 0, 0], ![0, 0, -5, 5, 0], ![98, -82, 57, 63, 222], ![-32, 24, -17, -22, -73]]]
  hmulB := by decide  
  f := ![![![628677, -121225, 1528666, -1521289, 17094], ![2857198, 42849, 7020244, -1771, 0]], ![![514370, -99180, 1250726, -1244691, 13986], ![2337698, 35075, 5743836, -1449, 0]], ![![628673, -121224, 1528596, -1521219, 17094], ![2857180, 42850, 7019922, -1771, 0]], ![![571527, -110203, 1389699, -1382993, 15540], ![2597464, 38963, 6382054, -1610, 0]], ![![246011, -47434, 598173, -595287, 6689], ![1118066, 16782, 2747052, -693, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-18, 23, 0, 0, 0], ![-21, 0, 23, 0, 0], ![-21, 0, 0, 23, 0], ![-9, 0, 0, 0, 23]], ![![-1, 1, 0, 0, 0], ![3, -5, 1, 0, 0], ![0, 0, -5, 5, 0], ![-128, -82, 57, 63, 222], ![44, 24, -17, -22, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0, 0, 0], ![13, -6, 1, 1, 4]] ![![23, 0, 0, 0, 0], ![5, 1, 1, 1, 4]]
  ![![23, 0, 0, 0, 0], ![-36, 36, -12, -19, -54]] where
 M := ![![![529, 0, 0, 0, 0], ![115, 23, 23, 23, 92]], ![![299, -138, 23, 23, 92], ![139, -47, 31, 51, 174]]]
 hmul := by decide  
 g := ![![![![23, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![5, 1, 1, 1, 4], ![0, 0, 0, 0, 0]]], ![![![13, -6, 1, 1, 4], ![0, 0, 0, 0, 0]], ![![17, -13, 5, 8, 24], ![7, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![23, 0, 0, 0, 0], ![-36, 36, -12, -19, -54]] ![![23, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![529, 0, 0, 0, 0], ![-115, 23, 0, 0, 0]], ![![-828, 828, -276, -437, -1242], ![46, 46, -69, -69, -276]]]
 hmul := by decide  
 g := ![![![![23, 0, 0, 0, 0]], ![![-5, 1, 0, 0, 0]]], ![![![-36, 36, -12, -19, -54]], ![![2, 2, -3, -3, -12]]]]
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


lemma PB3431I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB3431I0 : PrimesBelowBoundCertificateInterval O 1 23 3431 where
  m := 9
  g := ![5, 5, 5, 2, 2, 2, 2, 3, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB3431I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N2, I3N2, I3N2]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N2]
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
    · exact ![2401, 7]
    · exact ![14641, 11]
    · exact ![28561, 13]
    · exact ![4913, 289]
    · exact ![361, 361, 19]
    · exact ![529, 529, 23]
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
      exact NI3N2
      exact NI3N2
      exact NI3N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I3N2, I5N0, I7N0, I7N1, I11N1, I13N1, I17N1, I19N0, I19N1, I19N2, I23N0, I23N1, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N2, I3N2, I3N2], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1], [I11N1], [I13N1], [I17N1], [I19N0, I19N1, I19N2], [I23N0, I23N1, I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
