
import IdealArithmetic.Examples.NF5_1_607500000_5.RI5_1_607500000_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![7, -5, 2, 0, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![7, -5, 2, 0, 1]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![7, -5, 2, 0, 1], ![6, 0, 0, 1, 0], ![0, 5, -1, 3, 2], ![6, -1, 4, -2, 2], ![0, 1, -1, 3, -4]]]
  hmulB := by decide  
  f := ![![![-41, -29, 14, 0, 22], ![-24, 40, -12, 2, 0]], ![![-25, -19, 10, 0, 15], ![-16, 26, -8, 1, 0]], ![![16, 22, -10, 0, -14], ![16, -23, 7, -1, 0]], ![![-3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![-24, -12, 6, 0, 11], ![-11, 20, -6, 1, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![3, -5, 2, 0, 1], ![3, 0, 0, 1, 0], ![-1, 5, -1, 3, 2], ![2, -1, 4, -2, 2], ![2, 1, -1, 3, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![8, -1, -1, -2, -1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![8, -1, -1, -2, -1]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![8, -1, -1, -2, -1], ![-8, 16, -7, 0, -4], ![-26, 19, -7, 3, 0], ![-8, 7, 1, -5, 0], ![-6, 5, -4, 5, -7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-56, 1099, -581, -133, -355], ![-143, -140, -5, 0, -1]], ![![-4, -7, 5, 2, 3], ![2, 1, 0, 0, 0]], ![![-65, 1295, -685, -157, -418], ![-169, -165, -6, 0, -1]], ![![48, -1090, 578, 134, 354], ![144, 139, 5, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![4, -1, -1, -2, -1], ![-4, 16, -7, 0, -4], ![-13, 19, -7, 3, 0], ![-4, 7, 1, -5, 0], ![-3, 5, -4, 5, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![-2, -1, -2, 7, 0], ![0, -1, -1, 4, 2], ![10, -5, 11, -13, 1]]]
  hmulB := by decide  
  f := ![![![28, 7, 21, -48, 1], ![-14, 0, 10, 0, -2]], ![![26, 5, 20, -48, 1], ![-11, 2, 10, 0, -2]], ![![30, 8, 23, -55, 1], ![-15, 1, 12, 0, -2]], ![![0, 0, -1, 4, 0], ![-1, 0, -1, 0, 0]], ![![14, 3, 10, -24, 1], ![-7, 1, 5, 0, -1]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![-1, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-3, -1, -2, 7, 0], ![-2, -1, -1, 4, 2], ![8, -5, 11, -13, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![7, -5, 2, 0, 1]] ![![2, 0, 0, 0, 0], ![8, -1, -1, -2, -1]]
  ![![-1358, 649, -1514, 1870, 16]] where
 M := ![![![4, 0, 0, 0, 0], ![16, -2, -2, -4, -2]], ![![14, -10, 4, 0, 2], ![38, -44, 10, -3, 6]]]
 hmul := by decide  
 g := ![![![![19028, -11356, 8548, 4178, 5038]], ![![-21414, 8062, -7673, -4056, -4435]]], ![![![45064, -25770, 20591, 10523, 12164]], ![![-62931, 34163, -23472, -10075, -13566]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-1358, 649, -1514, 1870, 16]] ![![2, 0, 0, 0, 0], ![8, -1, -1, -2, -1]]
  ![![2, 0, 0, 0, 0], ![0, 4, -3, -2, -2]] where
 M := ![![![-2716, 1298, -3028, 3740, 32], ![8252, -3854, 9219, -11096, -1350]]]
 hmul := by decide  
 g := ![![![![-10444, 3632, -993, 4597, 796], ![3376, -1298, 0, 0, 0]], ![![31104, -10894, 3145, -13590, -2936], ![-9969, 3854, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![0, 4, -3, -2, -2]] ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![2, 0, 0, 0, 0], ![-2, 5, 0, 1, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![2, 2, 0, 0, 0]], ![![0, 8, -6, -4, -4], ![-14, 19, -10, -3, -6]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![3, -4, 0, -1, 0], ![2, 0, 0, 0, 0]]], ![![![2, -1, -3, -3, -2], ![2, 0, 0, 0, 0]], ![![-2, -3, -5, -4, -3], ![5, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![-2, 5, 0, 1, 0]] ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![2, 2, 0, 0, 0]], ![![-4, 10, 0, 2, 0], ![-2, 2, 4, 4, 2]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0]], ![![1, 1, 0, 0, 0]]], ![![![-2, 5, 0, 1, 0]], ![![-1, 1, 2, 2, 1]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![512457, -285153, 224594, 112503, 132164]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![512457, -285153, 224594, 112503, 132164]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![512457, -285153, 224594, 112503, 132164], ![872452, -485460, 382366, 191535, 225006], ![1485328, -826479, 650973, 326089, 383070], ![1268872, -706041, 556108, 278568, 327246], ![355704, -197925, 155894, 78091, 91737]]]
  hmulB := by decide  
  f := ![![![63, -23, 72, -67, -96]], ![![-1104, 538, -1228, 1551, -134]], ![![393, -260, 423, -756, 1002]], ![![1497, -730, 1666, -2105, 186]], ![![-2722, 1445, -3004, 4177, -1979]]]
  g := ![![![-29656, -95051, 224594, 112503, 132164], ![-50487, -161820, 382366, 191535, 225006], ![-85958, -275493, 650973, 326089, 383070], ![-73432, -235347, 556108, 278568, 327246], ![-20585, -65975, 155894, 78091, 91737]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2], [0, 1]]
 g := ![![[2, 1]], ![[1, 2]]]
 h' := ![![[2, 2], [0, 1]], ![[0, 1], [2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![80614, -42627, 88795, -122512, 56084]
  a := ![-12, 17, 2, -12, -36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![721, -14209, 88795, -122512, 56084]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![-2, -1, -4, 7, 0], ![0, -1, -1, 2, 2], ![10, -5, 11, -13, -1]]]
  hmulB := by decide  
  f := ![![![-14, 3, -16, 28, 0], ![-21, 0, -12, 0, 0]], ![![-16, 5, -16, 28, 0], ![-26, 0, -12, 0, 0]], ![![-6, 1, -8, 14, 0], ![-8, 1, -6, 0, 0]], ![![-10, 3, -11, 19, 0], ![-16, 1, -8, 0, 0]], ![![-4, 1, -5, 8, -1], ![-4, 1, -4, 2, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![-2, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![-2, -1, -4, 7, 0], ![0, -1, -1, 2, 2], ![8, -5, 11, -13, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![512457, -285153, 224594, 112503, 132164]] ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0], ![7, -6, 2, 0, 1]] where
 M := ![![![1537371, -855459, 673782, 337509, 396492], ![359995, -200307, 157772, 79032, 92842]]]
 hmul := by decide  
 g := ![![![![5173513, 3951519, -2788270, 1713143, -573948], ![2118336, -4801920, 0, 0, 0]], ![![1211446, 925309, -652914, 401156, -134399], ![496039, -1124436, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![7, -6, 2, 0, 1]] ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0], ![-2, 9, -3, -1, -2]] where
 M := ![![![9, 0, 0, 0, 0], ![-3, 3, 0, 0, 0]], ![![21, -18, 6, 0, 3], ![-1, 6, -3, 1, -1]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![1, -8, 3, 1, 2], ![3, 0, 0, 0, 0]]], ![![![7, -6, 2, 0, 1], ![0, 0, 0, 0, 0]], ![![1, -4, 1, 1, 1], ![2, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![-2, 9, -3, -1, -2]] ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![9, 0, 0, 0, 0], ![-3, 3, 0, 0, 0]], ![![-6, 27, -9, -3, -6], ![-12, 3, 0, 3, 0]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0]], ![![-1, 1, 0, 0, 0]]], ![![![-2, 9, -3, -1, -2]], ![![-4, 1, 0, 1, 0]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1303, 725, -571, -286, -336]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-1303, 725, -571, -286, -336]] 
 ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-1303, 725, -571, -286, -336], ![-2218, 1234, -972, -487, -572], ![-3776, 2101, -1655, -829, -974], ![-3226, 1795, -1414, -708, -832], ![-904, 503, -396, -199, -233]]]
  hmulB := by decide  
  f := ![![![-1, -23, 9, 4, 6]], ![![8, -18, 6, 1, 4]], ![![11, -6, 4, -5, 0]], ![![3, -14, 5, 2, 2]], ![![-4, -17, 2, 9, 7]]]
  g := ![![![4, 725, -571, -286, -336], ![7, 1234, -972, -487, -572], ![12, 2101, -1655, -829, -974], ![10, 1795, -1414, -708, -832], ![3, 503, -396, -199, -233]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-1303, 725, -571, -286, -336]] ![![-1303, 725, -571, -286, -336]]
  ![![3472235, -1932074, 1521778, 762294, 895502]] where
 M := ![![![3472235, -1932074, 1521778, 762294, 895502]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![3472235, -1932074, 1521778, 762294, 895502]] ![![-1303, 725, -571, -286, -336]]
  ![![-9253910053, 5149201873, -4055715355, -2031602184, -2386616978]] where
 M := ![![![-9253910053, 5149201873, -4055715355, -2031602184, -2386616978]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-9253910053, 5149201873, -4055715355, -2031602184, -2386616978]] ![![-1303, 725, -571, -286, -336]]
  ![![24662746618921, -13723221898212, 10808953143696, 5414456117196, 6360611835184]] where
 M := ![![![24662746618921, -13723221898212, 10808953143696, 5414456117196, 6360611835184]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![24662746618921, -13723221898212, 10808953143696, 5414456117196, 6360611835184]] ![![-1303, 725, -571, -286, -336]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-65729088277896575, 36573982514693785, -28807117323606715, -14430155310882530, -16951770347245040]]]
 hmul := by decide  
 g := ![![![![-13145817655579315, 7314796502938757, -5761423464721343, -2886031062176506, -3390354069449008]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![9, -7, 2, 0, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0], ![9, -7, 2, 0, 1]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![5, 4, 1, 0, 0], ![2, 3, 0, 1, 0], ![6, 6, 0, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![9, -7, 2, 0, 1], ![6, 2, -2, 1, 0], ![4, 7, 7, -11, 2], ![6, 1, 6, -6, -2], ![-20, 11, -23, 29, -2]]]
  hmulB := by decide  
  f := ![![![-576, -434, 369, -195, 37], ![-189, 980, -35, 0, 0]], ![![-1746, -1316, 1117, -589, 112], ![-574, 2968, -105, 0, 0]], ![![-1328, -999, 849, -448, 85], ![-435, 2256, -80, 0, 0]], ![![-918, -684, 583, -308, 58], ![-296, 1552, -55, 0, 0]], ![![-1989, -1501, 1274, -672, 128], ![-655, 3384, -120, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-5, -4, 7, 0, 0], ![-2, -3, 0, 7, 0], ![-6, -6, 0, 0, 7]], ![![-1, -3, 2, 0, 1], ![2, 1, -2, 1, 0], ![-3, 0, 7, -11, 2], ![0, 1, 6, -6, -2], ![7, 4, -23, 29, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [4, 6, 1] where
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
 g := ![![[5, 2], [1, 1]], ![[0, 5], [2, 6]]]
 h' := ![![[1, 6], [3, 4], [0, 1]], ![[0, 1], [0, 3], [1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [6, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [4, 6, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-757538, 412708, -856397, 1217164, -598117]
  a := ![84, 41, 130, -312, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![668403, 539358, -856397, 1217164, -598117]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -2, 1, -1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![3, -2, 1, -1, 0]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![5, 4, 1, 0, 0], ![2, 6, 0, 1, 0], ![2, 6, 0, 0, 1]] where
  M :=![![![3, -2, 1, -1, 0], ![-2, 3, -4, 4, -2], ![-12, 8, -11, 10, 8], ![10, -4, 12, -17, 6], ![-4, 4, -4, 10, -23]]]
  hmulB := by decide  
  f := ![![![195, -106, 85, 43, 50]], ![![330, -183, 146, 74, 86]], ![![409, -226, 180, 91, 106]], ![![408, -226, 180, 91, 106]], ![![358, -198, 158, 80, 93]]]
  g := ![![![0, 0, 1, -1, 0], ![2, 1, -4, 4, -2], ![1, -8, -11, 10, 8], ![-4, 2, 12, -17, 6], ![6, 14, -4, 10, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [6, 6, 1] where
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
 g := ![![[1, 4], [1, 1]], ![[5, 3], [2, 6]]]
 h' := ![![[1, 6], [1, 2], [0, 1]], ![[0, 1], [3, 5], [1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [3, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [6, 6, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4574, 2084, -5173, 5908, 2249]
  a := ![2, 5, 7, -17, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![711, -3738, -5173, 5908, 2249]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![-2, -1, -4, 7, 0], ![0, -1, -1, 2, 2], ![10, -5, 11, -13, -1]]]
  hmulB := by decide  
  f := ![![![662, -2235, -1402, 3066, 3426], ![2527, 28, 0, -12096, -210]], ![![662, -2235, -1402, 3066, 3426], ![2528, 28, 0, -12096, -210]], ![![662, -2232, -1399, 3060, 3420], ![2528, 29, 0, -12075, -210]], ![![364, -1226, -768, 1680, 1877], ![1394, 14, 0, -6627, -115]], ![![190, -639, -401, 876, 979], ![728, 11, 0, -3456, -60]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 7, 0, 0, 0], ![-6, 0, 7, 0, 0], ![-4, 0, 0, 7, 0], ![-2, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, -1, -4, 7, 0], ![0, -1, -1, 2, 2], ![4, -5, 11, -13, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0, 0, 0], ![9, -7, 2, 0, 1]] ![![3, -2, 1, -1, 0]]
  ![![7, 0, 0, 0, 0], ![12, 4, 1, 0, 0]] where
 M := ![![![21, -14, 7, -7, 0]], ![![13, -19, 11, -7, 7]]]
 hmul := by decide  
 g := ![![![![-9, -6, 0, -1, 0], ![7, 0, 0, 0, 0]]], ![![![-5, -5, 1, -1, 1], ![4, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0, 0, 0], ![12, 4, 1, 0, 0]] ![![7, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![49, 0, 0, 0, 0], ![-7, 7, 0, 0, 0]], ![![84, 28, 7, 0, 0], ![-14, 7, 0, 7, 0]]]
 hmul := by decide  
 g := ![![![![7, 0, 0, 0, 0]], ![![-1, 1, 0, 0, 0]]], ![![![12, 4, 1, 0, 0]], ![![-2, 1, 0, 1, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-2, -1, -3, 7, 0], ![0, -1, -1, 3, 2], ![10, -5, 11, -13, 0]]]
  hmulB := by decide  
  f := ![![![-11, -28, -26, 66, 16], ![154, 0, -66, -88, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![-6, -16, -14, 35, 8], ![96, 2, -36, -44, 0]], ![![-2, -6, -5, 12, 3], ![38, 3, -12, -16, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![-6, 0, 0, 11, 0], ![-2, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-4, -1, -3, 7, 0], ![-2, -1, -1, 3, 2], ![8, -5, 11, -13, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, -8, 19, -23, -2]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![17, -8, 19, -23, -2]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![9, 7, 1, 0, 0], ![4, 5, 0, 1, 0], ![9, 2, 0, 0, 1]] where
  M :=![![![17, -8, 19, -23, -2], ![-58, 31, -64, 90, -46], ![-332, 146, -373, 420, 180], ![218, -118, 240, -341, 190], ![188, -50, 218, -140, -559]]]
  hmulB := by decide  
  f := ![![![77, -208, 91, 29, 56]], ![![378, -323, 106, -4, 58]], ![![337, -377, 142, 19, 82]], ![![220, -227, 84, 9, 48]], ![![139, -232, 95, 23, 57]]]
  g := ![![![-4, -2, 19, -23, -2], ![52, 11, -64, 90, -46], ![-25, 27, -373, 420, 180], ![-208, -43, 240, -341, 190], ![347, 22, 218, -140, -559]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [5, 0, 1] where
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
 g := ![![[0, 9], [], [1]], ![[0, 2], [], [1]]]
 h' := ![![[0, 10], [0, 3], [6], [0, 1]], ![[0, 1], [0, 8], [6], [0, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [0, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [5, 0, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![35186, -38334, 30583, -103804, 307988]
  a := ![7, -44, -32, 93, 78]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-236067, -31761, 30583, -103804, 307988]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-5, 1, 0, 0, 0], ![0, -5, 1, 0, 0], ![-2, -1, -8, 7, 0], ![0, -1, -1, -2, 2], ![10, -5, 11, -13, -5]]]
  hmulB := by decide  
  f := ![![![14216, -3084, 1175, -1034, 54], ![30657, -902, 1540, -297, 0]], ![![7820, -1696, 646, -569, 30], ![16864, -495, 847, -165, 0]], ![![11372, -2468, 941, -826, 42], ![24524, -725, 1232, -231, 0]], ![![6268, -1360, 518, -456, 24], ![13517, -398, 679, -132, 0]], ![![1296, -277, 106, -94, 5], ![2795, -73, 140, -27, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 11, 0, 0, 0], ![-8, 0, 11, 0, 0], ![-5, 0, 0, 11, 0], ![-1, 0, 0, 0, 11]], ![![-1, 1, 0, 0, 0], ![2, -5, 1, 0, 0], ![3, -1, -8, 7, 0], ![2, -1, -1, -2, 2], ![2, -5, 11, -13, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2

def I11N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1193, 956, -714, -370, -430]] i)))

def SI11N3: IdealEqSpanCertificate' Table ![![-1193, 956, -714, -370, -430]] 
 ![![11, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-1193, 956, -714, -370, -430], ![-2872, 2041, -1262, -518, -740], ![-4876, 2608, -1795, -768, -1036], ![-3808, 2092, -1530, -709, -892], ![-1092, 632, -444, -200, -259]]]
  hmulB := by decide  
  f := ![![![909, -356, 1030, -1018, -1106]], ![![-449, 293, -484, 852, -1090]], ![![1381, -852, 1499, -2474, 2666]], ![![5266, -2540, 5866, -7321, 264]], ![![-7905, 4284, -8706, 12394, -6977]]]
  g := ![![![-39, 956, -714, -370, -430], ![-509, 2041, -1262, -518, -740], ![-545, 2608, -1795, -768, -1036], ![-292, 2092, -1530, -709, -892], ![-107, 632, -444, -200, -259]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N3 : Nat.card (O ⧸ I11N3) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N3)

lemma isPrimeI11N3 : Ideal.IsPrime I11N3 := prime_ideal_of_norm_prime hp11.out _ NI11N3
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![17, -8, 19, -23, -2]]
  ![![11, 0, 0, 0, 0], ![-22, 23, -6, 1, -3]] where
 M := ![![![187, -88, 209, -253, -22]], ![![-58, 31, -64, 90, -46]]]
 hmul := by decide  
 g := ![![![![649, 393, -416, -10, -143], ![-143, 561, 0, 0, 0]]], ![![![-176, -148, 136, 3, 43], ![57, -174, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![11, 0, 0, 0, 0], ![-22, 23, -6, 1, -3]] ![![11, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]]
  ![![909, -356, 1030, -1018, -1106]] where
 M := ![![![121, 0, 0, 0, 0], ![-55, 11, 0, 0, 0]], ![![-242, 253, -66, 11, -33], ![92, -117, 37, -5, 17]]]
 hmul := by decide  
 g := ![![![![-13123, 10516, -7854, -4070, -4730]], ![![3093, -2739, 2308, 1332, 1410]]], ![![![-11086, 10459, -2746, 725, -1459]], ![![4212, -4915, 1423, -155, 795]]]]
 hle2 := by decide  

def MulI11N2 : IdealMulLeCertificate' Table 
  ![![909, -356, 1030, -1018, -1106]] ![![-1193, 956, -714, -370, -430]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![-2, 8, 0, 1, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![-2, 8, 0, 1, 0]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![11, 8, 0, 1, 0], ![3, 6, 10, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![-2, 8, 0, 1, 0], ![0, -3, 7, 3, 2], ![6, -20, -5, 32, 6], ![12, -14, 3, 12, 12], ![42, -22, 45, -50, -2]]]
  hmulB := by decide  
  f := ![![![47, -184, 0, -23, 0], ![299, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![37, -144, 0, -18, 0], ![235, 0, 0, 0, 0]], ![![9, -33, -3, -6, -1], ![57, 7, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-11, -8, 0, 13, 0], ![-3, -6, -10, 0, 13]], ![![-1, 0, 0, 1, 0], ![-3, -3, -1, 3, 2], ![-28, -24, -5, 32, 6], ![-12, -14, -9, 12, 12], ![46, 30, 5, -50, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [2, 6, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 7, 11], [8, 5, 2], [0, 1]]
 g := ![![[4, 12, 9], [], [1]], ![[6, 7, 5, 5], [6, 1], [7, 9, 6, 5]], ![[1, 5, 8, 2], [5, 1], [8, 3, 8, 8]]]
 h' := ![![[5, 7, 11], [4, 11, 10], [11, 7], [0, 1]], ![[8, 5, 2], [11, 11, 2], [7, 10, 12], [5, 7, 11]], ![[0, 1], [7, 4, 1], [2, 9, 1], [8, 5, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 4], []]
 b := ![[], [0, 3, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [2, 6, 0, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2100037556, 975478872, -2347230692, 2807876198, 417947279]
  a := ![-34, 30, -9, 9, -73]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2633885967, -1845785722, -502054114, 2807876198, 417947279]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![2, 1, 0, 0, 0], ![0, 2, 1, 0, 0], ![-2, -1, -1, 7, 0], ![0, -1, -1, 5, 2], ![10, -5, 11, -13, 2]]]
  hmulB := by decide  
  f := ![![![-119325, -60937, -5249, 32188, -128], ![715247, 8697, -60372, 832, 0]], ![![-29910, -15275, -1316, 8068, -32], ![179284, 2184, -15132, 208, 0]], ![![-89417, -45663, -3933, 24120, -96], ![535975, 6514, -45240, 624, 0]], ![![-44757, -22857, -1969, 12073, -48], ![268279, 3265, -22644, 312, 0]], ![![-55074, -28126, -2423, 14856, -59], ![330120, 4019, -27864, 384, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 13, 0, 0, 0], ![-9, 0, 13, 0, 0], ![-5, 0, 0, 13, 0], ![-6, 0, 0, 0, 13]], ![![0, 1, 0, 0, 0], ![-1, 2, 1, 0, 0], ![-2, -1, -1, 7, 0], ![-2, -1, -1, 5, 2], ![-2, -5, 11, -13, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1551, -2521, 807, 30, 472]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![1551, -2521, 807, 30, 472]] 
 ![![13, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![1551, -2521, 807, 30, 472], ![3106, -1646, 220, -397, 60], ![160, 2983, -1249, -431, -794], ![178, 1153, -498, -192, -320], ![264, 173, -108, -77, -79]]]
  hmulB := by decide  
  f := ![![![24334369, -13540501, 10665035, 5342364, 6275922]], ![![18161854, -10105896, 7959804, 3987251, 4684008]], ![![7297485, -4060578, 3198272, 1602089, 1882048]], ![![8378680, -4662193, 3672128, 1839454, 2160892]], ![![1299312, -722983, 569450, 285251, 335097]]]
  g := ![![![1604, -2521, 807, 30, 472], ![1296, -1646, 220, -397, 60], ![-1661, 2983, -1249, -431, -794], ![-628, 1153, -498, -192, -320], ![-66, 173, -108, -77, -79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0, 0, 0], ![-2, 8, 0, 1, 0]] ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
  ![![24334369, -13540501, 10665035, 5342364, 6275922]] where
 M := ![![![169, 0, 0, 0, 0], ![26, 13, 0, 0, 0]], ![![-26, 104, 0, 13, 0], ![-4, 13, 7, 5, 2]]]
 hmul := by decide  
 g := ![![![![20163, -32773, 10491, 390, 6136]], ![![6208, -6688, 1834, -337, 1004]]], ![![![21924, -6973, -352, -3428, -784]], ![![2824, 1206, -909, -724, -648]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![24334369, -13540501, 10665035, 5342364, 6275922]] ![![1551, -2521, 807, 30, 472]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![10, 2, 2, 0, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![10, 2, 2, 0, 1]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![7, 2, 1, 0, 0], ![8, 6, 0, 1, 0], ![13, 15, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![10, 2, 2, 0, 1], ![6, 3, 7, 1, 0], ![-14, -2, -19, 52, 2], ![6, -8, -3, 22, 16], ![70, -34, 76, -88, -1]]]
  hmulB := by decide  
  f := ![![![276739, 179832, 457816, 65446, -14085], ![236997, -1176230, 1224, 0, 0]], ![![214984, 139703, 355654, 50838, -10942], ![184110, -913750, 952, 0, 0]], ![![137437, 89310, 227365, 32502, -6995], ![117699, -584150, 608, 0, 0]], ![![206108, 133934, 340968, 48741, -10490], ![176506, -876020, 912, 0, 0]], ![![401321, 260787, 663908, 94904, -20425], ![343674, -1705720, 1776, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-7, -2, 17, 0, 0], ![-8, -6, 0, 17, 0], ![-13, -15, 0, 0, 17]], ![![-1, -1, 2, 0, 1], ![-3, -1, 7, 1, 0], ![-19, -18, -19, 52, 2], ![-21, -22, -3, 22, 16], ![15, 21, 76, -88, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [7, 4, 1] where
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
 g := ![![[3, 16], [13], [16], [1]], ![[7, 1], [13], [16], [1]]]
 h' := ![![[13, 16], [2, 4], [5, 9], [10, 13], [0, 1]], ![[0, 1], [3, 13], [3, 8], [9, 4], [13, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [6, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [7, 4, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![283411, -133312, 315896, -384496, -28308]
  a := ![38, -8, 34, -70, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![89183, 115676, 315896, -384496, -28308]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![-1, -11, 2, 0, 1]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0], ![-1, -11, 2, 0, 1]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![3, 3, 1, 0, 0], ![7, 10, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![-1, -11, 2, 0, 1], ![6, -8, -6, 1, 0], ![12, 11, 9, -39, 2], ![6, 5, 10, -28, -10], ![-60, 31, -67, 81, -12]]]
  hmulB := by decide  
  f := ![![![1036568, -1031382, -1062707, 163999, -28021], ![479723, -2853620, -1683, 0, 0]], ![![1841011, -1831794, -1887434, 291266, -49767], ![852023, -5068210, -2992, 0, 0]], ![![501040, -498524, -513675, 79270, -13545], ![231893, -1379336, -814, 0, 0]], ![![1509770, -1502210, -1547841, 238862, -40813], ![698727, -4156320, -2453, 0, 0]], ![![609746, -606694, -625122, 96470, -16483], ![282192, -1678600, -990, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-3, -3, 17, 0, 0], ![-7, -10, 0, 17, 0], ![-10, 0, 0, 0, 17]], ![![-1, -1, 2, 0, 1], ![1, 0, -6, 1, 0], ![14, 22, 9, -39, 2], ![16, 15, 10, -28, -10], ![-18, -34, -67, 81, -12]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [3, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 16], [0, 1]]
 g := ![![[8, 13], [8], [15], [1]], ![[2, 4], [8], [15], [1]]]
 h' := ![![[10, 16], [14, 9], [15, 5], [14, 10], [0, 1]], ![[0, 1], [2, 8], [14, 12], [12, 7], [10, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [9, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [3, 7, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13765, -6006, 15335, -17385, -6924]
  a := ![11, 0, 12, -27, 8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9335, 7167, 15335, -17385, -6924]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5359, -2960, 2336, 1170, 1374]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![5359, -2960, 2336, 1170, 1374]] 
 ![![17, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![5359, -2960, 2336, 1170, 1374], ![9068, -5017, 3976, 2000, 2340], ![15448, -8608, 6795, 3412, 4000], ![13220, -7360, 5804, 2911, 3416], ![3704, -2060, 1626, 816, 957]]]
  hmulB := by decide  
  f := ![![![391, -184, 436, -530, -42]], ![![200, -89, 224, -256, -92]], ![![-249, 104, -281, 298, 214]], ![![330, -176, 364, -509, 252]], ![![372, -124, 426, -352, -755]]]
  g := ![![![707, -2960, 2336, 1170, 1374], ![1184, -5017, 3976, 2000, 2340], ![2045, -8608, 6795, 3412, 4000], ![1754, -7360, 5804, 2911, 3416], ![490, -2060, 1626, 816, 957]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0, 0, 0], ![10, 2, 2, 0, 1]] ![![17, 0, 0, 0, 0], ![-1, -11, 2, 0, 1]]
  ![![391, -184, 436, -530, -42]] where
 M := ![![![289, 0, 0, 0, 0], ![-17, -187, 34, 0, 17]], ![![170, 34, 34, 0, 17], ![-34, -73, -41, 5, 2]]]
 hmul := by decide  
 g := ![![![![91103, -50320, 39712, 19890, 23358]], ![![-70507, 38871, -30856, -15530, -18157]]], ![![![106326, -58910, 46528, 23340, 27377]], ![![-82590, 45817, -36235, -18205, -21326]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![391, -184, 436, -530, -42]] ![![5359, -2960, 2336, 1170, 1374]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [12, 11, 10, 14, 13, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 16, 5, 4, 3], [3, 1, 12, 4, 14], [13, 8, 13, 6, 6], [14, 12, 8, 5, 15], [0, 1]]
 g := ![![[2, 12, 1, 3, 11], [1, 0, 3, 6, 1], [], []], ![[6, 14, 7, 12, 2, 10, 18, 13], [4, 15, 4, 6, 2, 13, 17, 12], [7, 0, 12, 9], [9, 8, 2, 9]], ![[11, 1, 1, 3, 11, 18, 4, 2], [13, 5, 5, 0, 9, 2, 15, 13], [1, 15, 2, 5], [7, 16, 15, 6]], ![[3, 1, 6, 2, 13, 2, 12, 17], [14, 5, 0, 11, 16, 10, 9, 1], [9, 18, 16, 1], [5, 10, 3, 17]], ![[6, 4, 7, 5, 2, 8, 14, 10], [18, 5, 6, 12, 10, 11, 7, 13], [7, 6, 14, 7], [10, 16, 18, 16]]]
 h' := ![![[14, 16, 5, 4, 3], [7, 8, 11, 14, 12], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[3, 1, 12, 4, 14], [2, 0, 14, 7, 6], [3, 10, 13, 17, 17], [12, 6, 4, 12, 3], [14, 16, 5, 4, 3]], ![[13, 8, 13, 6, 6], [17, 6, 2, 4, 7], [8, 5, 16, 10, 9], [1, 3, 8, 9, 9], [3, 1, 12, 4, 14]], ![[14, 12, 8, 5, 15], [13, 15, 2, 15, 5], [12, 1, 12, 4, 4], [14, 14, 16, 14, 18], [13, 8, 13, 6, 6]], ![[0, 1], [15, 9, 9, 17, 8], [11, 3, 16, 7, 7], [0, 15, 9, 3, 8], [14, 12, 8, 5, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 8, 16, 10], [], [], []]
 b := ![[], [1, 10, 12, 17, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [12, 11, 10, 14, 13, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-55919522976654050, 27974246505631852, -62078931495805934, 80728107349437393, -16800193211700597]
  a := ![38, -32, 16, -13, 79]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2943132788244950, 1472328763454308, -3267312183989786, 4248847755233547, -884220695352663]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 2476099 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-16, 30, -5, 1, -3]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![-16, 30, -5, 1, -3]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![13, 13, 17, 15, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-16, 30, -5, 1, -3], ![-20, 3, 11, 7, 2], ![-2, -48, -15, 72, 14], ![16, -30, 5, 22, 26], ![90, -48, 100, -112, -9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 0], ![0, 0, 0, 0, 0]], ![![11, -19, 4, 0, 2], ![15, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![-13, -13, -17, -15, 23]], ![![1, 3, 2, 2, -3], ![-2, -1, -1, -1, 2], ![-8, -10, -11, -6, 14], ![-14, -16, -19, -16, 26], ![9, 3, 11, 1, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [18, 1, 15, 18, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 9, 8, 4], [0, 10, 19, 8], [17, 3, 19, 11], [0, 1]]
 g := ![![[16, 21, 7, 18], [11, 4, 15, 8], [5, 1], []], ![[15, 12, 22, 9, 19, 18], [22, 7, 15, 12, 0, 2], [22, 16, 7, 15, 13, 2], [18, 6, 16]], ![[8, 0, 16, 21, 7, 6], [2, 14, 15, 20, 15, 18], [2, 13, 16, 15, 20, 4], [13, 3, 18]], ![[7, 4, 5, 0, 10, 15], [21, 1, 16, 0, 15, 5], [3, 9, 4, 14], [1, 11, 6]]]
 h' := ![![[11, 9, 8, 4], [9, 13, 21, 15], [2, 0, 16, 10], [0, 0, 1], [0, 1]], ![[0, 10, 19, 8], [14, 2, 6, 4], [10, 6, 3, 9], [4, 3, 15, 9], [11, 9, 8, 4]], ![[17, 3, 19, 11], [10, 10, 2, 8], [10, 16, 20, 10], [19, 2, 15, 14], [0, 10, 19, 8]], ![[0, 1], [5, 21, 17, 19], [3, 1, 7, 17], [18, 18, 15], [17, 3, 19, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [9, 22, 18], []]
 b := ![[], [], [1, 16, 16, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [18, 1, 15, 18, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![436480535873, -157480463084, 497440879850, -448684323639, -719200723208]
  a := ![19, -20, 2, 3, 46]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![425482171199, 399657779940, 553211007582, 449535935847, -719200723208]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-7, 1, 0, 0, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![-7, 1, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-7, 1, 0, 0, 0], ![0, -7, 1, 0, 0], ![-2, -1, -10, 7, 0], ![0, -1, -1, -4, 2], ![10, -5, 11, -13, -7]]]
  hmulB := by decide  
  f := ![![![-97039, 14055, -5409, 3680, 8], ![-315376, 2875, -12144, -92, 0]], ![![-108850, 15772, -6065, 4128, 8], ![-353762, 3243, -13616, -92, 0]], ![![-102946, 14914, -5737, 3904, 8], ![-334574, 3060, -12880, -92, 0]], ![![1931, -274, 106, -73, 0], ![6276, -38, 240, 0, 0]], ![![-84386, 12226, -4704, 3200, 7], ![-274254, 2512, -10560, -80, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-16, 23, 0, 0, 0], ![-20, 0, 23, 0, 0], ![-1, 0, 0, 23, 0], ![-20, 0, 0, 0, 23]], ![![-1, 1, 0, 0, 0], ![4, -7, 1, 0, 0], ![9, -1, -10, 7, 0], ![0, -1, -1, -4, 2], ![1, -5, 11, -13, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0, 0, 0], ![-16, 30, -5, 1, -3]] ![![23, 0, 0, 0, 0], ![-7, 1, 0, 0, 0]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![529, 0, 0, 0, 0], ![-161, 23, 0, 0, 0]], ![![-368, 690, -115, 23, -69], ![92, -207, 46, 0, 23]]]
 hmul := by decide  
 g := ![![![![23, 0, 0, 0, 0]], ![![-7, 1, 0, 0, 0]]], ![![![-16, 30, -5, 1, -3]], ![![4, -9, 2, 0, 1]]]]
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


lemma PB1535I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1535I0 : PrimesBelowBoundCertificateInterval O 1 23 1535 where
  m := 9
  g := ![5, 4, 5, 3, 4, 3, 3, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1535I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1, I11N2, I11N3]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0]
    · exact ![I23N0, I23N1]
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
    · exact ![49, 49, 7]
    · exact ![11, 121, 11, 11]
    · exact ![2197, 13, 13]
    · exact ![289, 289, 17]
    · exact ![2476099]
    · exact ![279841, 23]
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
      exact NI13N2
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N0, I7N1, I7N2, I11N0, I11N1, I11N2, I11N3, I13N1, I13N2, I17N0, I17N1, I17N2, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [I11N0, I11N1, I11N2, I11N3], [I13N1, I13N2], [I17N0, I17N1, I17N2], [], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
