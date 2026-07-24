
import IdealArithmetic.Examples.NF5_3_1215000000_2.RI5_3_1215000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19645, 7853, 1961, -10156, -6106]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![19645, 7853, 1961, -10156, -6106]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![21, 4, 17, 4, 1]] where
  M :=![![![19645, 7853, 1961, -10156, -6106], ![36636, 9522, -4264, -40909, -20312], ![121872, 20873, -27123, -175573, -81818], ![216472, 36503, -52988, -321444, -151092], ![302422, 44887, -78053, -465426, -215145]]]
  hmulB := by decide  
  f := ![![![26421, -58003, 18103, 12818, -11160]], ![![66960, -37980, -63288, 167, 25636]], ![![-153816, 206989, 25475, -35881, 334]], ![![-29620, 8867, 35940, 2278, -15264]], ![![-59989, 68985, 21693, -10513, -5677]]]
  g := ![![![5099, 1113, 3647, 492, -6106], ![15972, 3130, 11760, 1391, -20312], ![63450, 12005, 47027, 5231, -81818], ![116876, 22099, 86744, 9756, -151092], ![166223, 31223, 123428, 13626, -215145]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 4 2 4 [11, 3, 17, 15, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 18, 2, 15], [13, 3, 9, 13], [28, 7, 18, 1], [0, 1]]
 g := ![![[13, 19, 11, 23], [11, 19, 23], [3, 5, 14, 1], []], ![[17, 23, 8, 27, 4, 27], [24, 20, 22], [8, 10, 22, 7, 9, 19], [10, 13, 25, 23, 25, 11]], ![[6, 6, 7, 23, 22, 23], [1, 27, 9], [15, 17, 13, 12, 25, 25], [28, 15, 10, 0, 28, 22]], ![[17, 19, 26, 26, 3, 7], [15, 17, 4], [14, 16, 1, 8, 3, 13], [5, 12, 25, 14, 10, 1]]]
 h' := ![![[2, 18, 2, 15], [11, 9, 23, 9], [25, 23, 12, 20], [0, 0, 0, 1], [0, 1]], ![[13, 3, 9, 13], [19, 25, 21, 24], [14, 2, 27, 14], [14, 14, 5, 3], [2, 18, 2, 15]], ![[28, 7, 18, 1], [11, 10, 27, 2], [14, 9, 2, 26], [4, 25, 20, 15], [13, 3, 9, 13]], ![[0, 1], [4, 14, 16, 23], [16, 24, 17, 27], [2, 19, 4, 10], [28, 7, 18, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 13, 5], []]
 b := ![[], [], [5, 6, 11, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 4
  hpos := by decide
  P := [11, 3, 17, 15, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14645637393, -3872135447, 5432456288, 23028973661, 12655376606]
  a := ![0, 7, -7, -5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9669260211, -1879091099, -7231342966, -951466647, 12655376606]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 707281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26421, -58003, 18103, 12818, -11160]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![26421, -58003, 18103, 12818, -11160]] 
 ![![29, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![26421, -58003, 18103, 12818, -11160], ![66960, -37980, -63288, 167, 25636], ![-153816, 206989, 25475, -35881, 334], ![-29620, 8867, 35940, 2278, -15264], ![170990, -183733, -74749, 26142, 22561]]]
  hmulB := by decide  
  f := ![![![19645, 7853, 1961, -10156, -6106]], ![![15489, 6015, 1273, -8765, -5122]], ![![19783, 6948, 620, -14109, -7664]], ![![19658, 6133, -610, -17388, -9000]], ![![13138, 2631, -2421, -17450, -8261]]]
  g := ![![![22139, -58003, 18103, 12818, -11160], ![76366, -37980, -63288, 167, 25636], ![-153172, 206989, 25475, -35881, 334], ![-35255, 8867, 35940, 2278, -15264], ![178890, -183733, -74749, 26142, 22561]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![19645, 7853, 1961, -10156, -6106]] ![![26421, -58003, 18103, 12818, -11160]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 5 2 4 [18, 30, 10, 25, 23, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 3, 9, 15, 8], [25, 27, 14, 1, 22], [22, 9, 29, 21, 4], [4, 22, 10, 25, 28], [0, 1]]
 g := ![![[11, 28, 7], [0, 15, 20, 28, 19], [8, 8, 1], []], ![[6, 9, 19, 10, 5, 18, 22, 4], [29, 0, 4, 4, 23, 8, 1, 18], [3, 29, 17, 28, 15, 21, 15, 10], [12, 2, 9, 21, 26, 9, 1, 16]], ![[5, 13, 19, 21, 11, 14, 17, 15], [30, 7, 22, 21, 18, 5, 25, 23], [29, 18, 11, 29, 0, 22, 26, 11], [19, 0, 2, 8, 10, 14, 22, 15]], ![[29, 17, 12, 8, 27, 14, 14, 1], [11, 8, 7, 4, 25, 30, 29, 18], [12, 13, 30, 15, 14, 1, 23, 5], [5, 14, 13, 2, 24, 8, 1, 2]], ![[18, 3, 20, 29, 12, 5, 7, 9], [18, 29, 28, 24, 26, 23, 20, 5], [0, 3, 18, 9, 0, 18, 23, 10], [3, 18, 8, 16, 14, 15, 25, 4]]]
 h' := ![![[19, 3, 9, 15, 8], [0, 6, 11, 10], [11, 19, 3, 0, 9], [0, 0, 0, 1], [0, 1]], ![[25, 27, 14, 1, 22], [21, 3, 14, 1, 27], [28, 4, 28, 2, 17], [9, 1, 29, 30, 28], [19, 3, 9, 15, 8]], ![[22, 9, 29, 21, 4], [23, 20, 4, 13, 9], [5, 15, 15, 20, 26], [0, 21, 6, 17, 27], [25, 27, 14, 1, 22]], ![[4, 22, 10, 25, 28], [10, 29, 12, 25, 15], [30, 24, 12, 13, 19], [18, 18, 2, 6, 28], [22, 9, 29, 21, 4]], ![[0, 1], [22, 4, 21, 13, 11], [28, 0, 4, 27, 22], [10, 22, 25, 8, 10], [4, 22, 10, 25, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 27, 9, 22], [], [], []]
 b := ![[], [28, 5, 24, 27, 5], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 5
  hpos := by decide
  P := [18, 30, 10, 25, 23, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5309002634154613593, 2124670805199497200, -2666481883927831990, -8547688677482539245, -5531712760160973125]
  a := ![3, 62, -124, -1, -249]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![171258149488858503, 68537767909661200, -86015544642833290, -275731892822017395, -178442347101966875]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 28629151 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀

instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 1, -2, -13, -6]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![9, 1, -2, -13, -6]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![3, 28, 1, 0, 0], ![10, 20, 0, 1, 0], ![19, 15, 0, 0, 1]] where
  M :=![![![9, 1, -2, -13, -6], ![36, 6, -10, -55, -26], ![156, 23, -39, -241, -110], ![284, 45, -76, -438, -206], ![416, 59, -106, -639, -293]]]
  hmulB := by decide  
  f := ![![![53, 33, 4, -5, -2]], ![![12, 48, 24, -5, -10]], ![![15, 38, 19, -4, -8]], ![![22, 35, 14, -4, -6]], ![![31, 38, 12, -5, -5]]]
  g := ![![![7, 11, -2, -13, -6], ![30, 48, -10, -55, -26], ![129, 205, -39, -241, -110], ![238, 379, -76, -438, -206], ![343, 546, -106, -639, -293]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [21, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 36], [0, 1]]
 g := ![![[27, 30], [25], [35, 9], [33], [1]], ![[0, 7], [25], [1, 28], [33], [1]]]
 h' := ![![[25, 36], [18, 20], [5, 32], [7, 34], [16, 25], [0, 1]], ![[0, 1], [0, 17], [28, 5], [6, 3], [12, 12], [25, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [22, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [21, 12, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6662, -7982, 8723, 11976, 13980]
  a := ![1, 6, -8, -3, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11303, -18958, 8723, 11976, 13980]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2089, -1079, -548, 105, 270]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-2089, -1079, -548, 105, 270]] 
 ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![-2089, -1079, -548, 105, 270], ![-1620, -836, -426, 81, 210], ![-1260, -645, -329, 63, 162], ![-1284, -663, -336, 64, 166], ![-36, -21, -12, 3, 5]]]
  hmulB := by decide  
  f := ![![![-325, -47, 82, 501, 234]], ![![-117, -17, 30, 180, 84]], ![![-426, -63, 109, 657, 306]], ![![-598, -89, 154, 922, 430]], ![![-635, -94, 164, 978, 455]]]
  g := ![![![386, -1079, -548, 105, 270], ![300, -836, -426, 81, 210], ![231, -645, -329, 63, 162], ![237, -663, -336, 64, 166], ![8, -21, -12, 3, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, 0, -12, -54, -24]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![25, 0, -12, -54, -24]] 
 ![![37, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![27, 0, 0, 0, 1]] where
  M :=![![![25, 0, -12, -54, -24], ![144, 19, -42, -234, -108], ![648, 96, -173, -1008, -468], ![1200, 180, -318, -1859, -864], ![1740, 264, -456, -2682, -1247]]]
  hmulB := by decide  
  f := ![![![301, -360, -96, 54, 24]], ![![110, -125, -42, 18, 12]], ![![194, -240, -53, 36, 12]], ![![27, -36, -6, 7, 0]], ![![231, -264, -84, 36, 25]]]
  g := ![![![31, 0, -12, -54, -24], ![124, 19, -42, -234, -108], ![526, 96, -173, -1008, -468], ![969, 180, -318, -1859, -864], ![1395, 264, -456, -2682, -1247]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2

def I37N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![77, -152, 36, 32, -24]] i)))

def SI37N3: IdealEqSpanCertificate' Table ![![77, -152, 36, 32, -24]] 
 ![![37, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![77, -152, 36, 32, -24], ![144, -63, -156, -4, 64], ![-384, 496, 89, -88, -8], ![-64, 8, 84, 13, -40], ![416, -424, -196, 48, 69]]]
  hmulB := by decide  
  f := ![![![-15687, -8104, -4132, 736, 2008]], ![![-10077, -5207, -2656, 468, 1288]], ![![-11262, -5824, -2975, 504, 1432]], ![![-1078, -568, -300, 5, 120]], ![![-12682, -6568, -3364, 528, 1597]]]
  g := ![![![89, -152, 36, 32, -24], ![101, -63, -156, -4, 64], ![-370, 496, 89, -88, -8], ![-34, 8, 84, 13, -40], ![354, -424, -196, 48, 69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N3 : Nat.card (O ⧸ I37N3) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N3)

lemma isPrimeI37N3 : Ideal.IsPrime I37N3 := prime_ideal_of_norm_prime hp37.out _ NI37N3
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![9, 1, -2, -13, -6]] ![![-2089, -1079, -548, 105, 270]]
  ![![-993, -512, -260, 50, 128]] where
 M := ![![![-993, -512, -260, 50, 128]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-993, -512, -260, 50, 128]] ![![25, 0, -12, -54, -24]]
  ![![15687, 8104, 4132, -736, -2008]] where
 M := ![![![15687, 8104, 4132, -736, -2008]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N2 : IdealMulLeCertificate' Table 
  ![![15687, 8104, 4132, -736, -2008]] ![![77, -152, 36, 32, -24]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2, I37N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
    exact isPrimeI37N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1 ⊙ MulI37N2)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-71, -89, 47, 180, 64]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-71, -89, 47, 180, 64]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![29, 30, 27, 31, 1]] where
  M :=![![![-71, -89, 47, 180, 64], ![-384, -106, 44, 705, 360], ![-2160, -53, 555, 2997, 1410], ![-3668, -547, 996, 5608, 2588], ![-5042, -1007, 1279, 8112, 3789]]]
  hmulB := by decide  
  f := ![![![1365, 707, 357, -66, -178]], ![![1068, 540, 284, -63, -132]], ![![792, 451, 193, -3, -126]], ![![872, 405, 244, -82, -88]], ![![2927, 1500, 771, -155, -373]]]
  g := ![![![-47, -49, -41, -44, 64], ![-264, -266, -236, -255, 360], ![-1050, -1033, -915, -993, 1410], ![-1920, -1907, -1680, -1820, 2588], ![-2803, -2797, -2464, -2667, 3789]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 4 2 5 [8, 39, 31, 4, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 5, 25, 17], [24, 23, 26, 3], [31, 12, 31, 21], [0, 1]]
 g := ![![[33, 25, 40, 36], [4, 37, 23], [16, 35, 20], [37, 1], []], ![[37, 26, 4, 7, 17, 19], [37, 8, 33], [13, 10, 37], [22, 10, 9, 7, 12, 29], [30, 22, 2]], ![[17, 29, 25, 2, 17, 34], [40, 8, 4], [28, 27, 31], [21, 37, 39, 26, 19, 3], [14, 38, 9]], ![[2, 31, 24, 39, 21, 40], [0, 23, 40], [11, 38, 5], [8, 39, 27, 27, 28, 40], [15, 30, 31]]]
 h' := ![![[23, 5, 25, 17], [4, 11, 29, 6], [35, 40, 26, 8], [32, 25, 3, 26], [0, 0, 1], [0, 1]], ![[24, 23, 26, 3], [28, 15, 1, 10], [23, 1, 33, 22], [39, 17, 7, 23], [2, 32, 27, 29], [23, 5, 25, 17]], ![[31, 12, 31, 21], [6, 38, 7, 36], [30, 40, 6, 2], [34, 15, 13, 20], [13, 8, 35, 1], [24, 23, 26, 3]], ![[0, 1], [33, 18, 4, 30], [19, 1, 17, 9], [36, 25, 18, 13], [21, 1, 19, 11], [31, 12, 31, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [14, 3, 18], []]
 b := ![[], [], [21, 39, 27, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 4
  hpos := by decide
  P := [8, 39, 31, 4, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6455218301961, -4141321443227, 4748483227586, 10824937675695, 8765934476991]
  a := ![1, -25, 48, -1, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6357739466700, -6515106237877, -5656871893931, -6363878807586, 8765934476991]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 2825761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1365, -707, -357, 66, 178]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-1365, -707, -357, 66, 178]] 
 ![![41, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![-1365, -707, -357, 66, 178], ![-1068, -540, -284, 63, 132], ![-792, -451, -193, 3, 126], ![-872, -405, -244, 82, 88], ![34, -65, 37, -72, 41]]]
  hmulB := by decide  
  f := ![![![71, 89, -47, -180, -64]], ![![44, 46, -24, -105, -40]], ![![70, 23, -25, -117, -50]], ![![157, 98, -69, -308, -124]], ![![168, 81, -61, -312, -133]]]
  g := ![![![223, -707, -357, 66, 178], ![163, -540, -284, 63, 132], ![165, -451, -193, 3, 126], ![102, -405, -244, 82, 88], ![66, -65, 37, -72, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-71, -89, 47, 180, 64]] ![![-1365, -707, -357, 66, 178]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![-41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -8, -2, 4, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![5, -8, -2, 4, 0]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![12, 41, 21, 1, 0], ![3, 16, 5, 0, 1]] where
  M :=![![![5, -8, -2, 4, 0], ![0, 3, -2, -2, 8], ![-48, 28, 3, 40, -4], ![-8, -24, 22, 21, 28], ![-56, 16, -26, 96, 13]]]
  hmulB := by decide  
  f := ![![![559, 288, 146, -28, -72]], ![![432, 225, 114, -22, -56]], ![![336, 172, 89, -16, -44]], ![![740, 383, 195, -37, -96]], ![![239, 124, 63, -12, -31]]]
  g := ![![![-1, -4, -2, 4, 0], ![0, -1, 0, -2, 8], ![-12, -36, -19, 40, -4], ![-8, -31, -13, 21, 28], ![-29, -96, -49, 96, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [40, 19, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 8, 23], [40, 34, 20], [0, 1]]
 g := ![![[0, 38, 36], [37, 25, 17], [24, 16], [33, 40, 1], []], ![[42, 13, 39, 13], [33, 24, 31, 24], [13, 1], [16, 2, 28, 14], [28, 13]], ![[13, 40, 13, 39], [2, 26, 1, 2], [22, 9], [29, 29, 6, 33], [31, 13]]]
 h' := ![![[0, 8, 23], [25, 5, 6], [26, 41, 24], [13, 9, 4], [0, 0, 1], [0, 1]], ![[40, 34, 20], [13, 6, 18], [21, 20, 39], [5, 35, 42], [41, 23, 34], [0, 8, 23]], ![[0, 1], [20, 32, 19], [29, 25, 23], [7, 42, 40], [16, 20, 8], [40, 34, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 4], []]
 b := ![[], [19, 19, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [40, 19, 3, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3136531, 36812979, -35205849, -5527150, -46541711]
  a := ![-1, 7, -17, 8, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4716614, 23444035, 7292392, -5527150, -46541711]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-559, -288, -146, 28, 72]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-559, -288, -146, 28, 72]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![1, 22, 1, 0, 0], ![36, 18, 0, 1, 0], ![37, 36, 0, 0, 1]] where
  M :=![![![-559, -288, -146, 28, 72], ![-432, -225, -114, 22, 56], ![-336, -172, -89, 16, 44], ![-344, -176, -90, 17, 44], ![-8, -8, -2, 0, 1]]]
  hmulB := by decide  
  f := ![![![-5, 8, 2, -4, 0]], ![![0, -3, 2, 2, -8]], ![![1, -2, 1, 0, -4]], ![![-4, 6, 2, -3, -4]], ![![-3, 4, 4, -4, -7]]]
  g := ![![![-95, -4, -146, 28, 72], ![-74, -3, -114, 22, 56], ![-57, -2, -89, 16, 44], ![-58, -2, -90, 17, 44], ![-1, 0, -2, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [18, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 42], [0, 1]]
 g := ![![[2, 38], [4, 15], [6], [5, 6], [1]], ![[10, 5], [23, 28], [6], [4, 37], [1]]]
 h' := ![![[7, 42], [14, 9], [37, 12], [39, 36], [25, 7], [0, 1]], ![[0, 1], [34, 34], [35, 31], [33, 7], [31, 36], [7, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [24, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [18, 36, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20106, -18368, 15800, -25524, 13308]
  a := ![0, 4, 16, -26, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![10018, -8968, 15800, -25524, 13308]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![5, -8, -2, 4, 0]] ![![-559, -288, -146, 28, 72]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![-43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-351, -49, 92, 537, 250]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-351, -49, 92, 537, 250]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![18, 26, 1, 0, 0], ![38, 24, 0, 1, 0], ![38, 34, 0, 0, 1]] where
  M :=![![![-351, -49, 92, 537, 250], ![-1500, -230, 396, 2313, 1074], ![-6444, -987, 1687, 9945, 4626], ![-11900, -1805, 3118, 18340, 8530], ![-17168, -2603, 4504, 26451, 12299]]]
  hmulB := by decide  
  f := ![![![-697, 669, -534, 915, -478]], ![![2868, -2512, 2118, -3555, 1830]], ![![1086, -925, 793, -1323, 678]], ![![1146, -959, 832, -1382, 706]], ![![1062, -877, 766, -1269, 647]]]
  g := ![![![-679, -507, 92, 537, 250], ![-2922, -2182, 396, 2313, 1074], ![-12564, -9379, 1687, 9945, 4626], ![-23172, -17299, 3118, 18340, 8530], ![-33420, -24951, 4504, 26451, 12299]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [23, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 46], [0, 1]]
 g := ![![[5, 17], [10, 12], [40, 28], [24, 18], [1]], ![[24, 30], [40, 35], [16, 19], [22, 29], [1]]]
 h' := ![![[26, 46], [5, 8], [20, 23], [12, 34], [24, 26], [0, 1]], ![[0, 1], [25, 39], [7, 24], [3, 13], [42, 21], [26, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [6, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [23, 21, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1147, -22871, 22305, 4996, 28922]
  a := ![13, 7, -15, 5, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-35941, -36299, 22305, 4996, 28922]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5803, -2993, -1522, 291, 750]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-5803, -2993, -1522, 291, 750]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![40, 28, 1, 0, 0], ![16, 43, 0, 1, 0], ![5, 28, 0, 0, 1]] where
  M :=![![![-5803, -2993, -1522, 291, 750], ![-4500, -2322, -1180, 225, 582], ![-3492, -1799, -917, 177, 450], ![-3564, -1841, -934, 176, 462], ![-108, -51, -30, 9, 11]]]
  hmulB := by decide  
  f := ![![![-53, 37, 44, -3, -18]], ![![108, -148, -10, 21, -6]], ![![20, -55, 29, 9, -18]], ![![80, -121, 6, 17, -12]], ![![61, -88, 0, 12, -7]]]
  g := ![![![993, 130, -1522, 291, 750], ![770, 101, -1180, 225, 582], ![598, 78, -917, 177, 450], ![610, 81, -934, 176, 462], ![19, 2, -30, 9, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [10, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 46], [0, 1]]
 g := ![![[37, 32], [27, 42], [30, 28], [2, 36], [1]], ![[41, 15], [44, 5], [10, 19], [30, 11], [1]]]
 h' := ![![[6, 46], [12, 19], [29, 18], [27, 34], [37, 6], [0, 1]], ![[0, 1], [32, 28], [43, 29], [43, 13], [26, 41], [6, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [22, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [10, 41, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-636, -533, 575, 1000, 890]
  a := ![-1, 1, -2, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-938, -1799, 575, 1000, 890]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![115, -98, 80, -144, 76]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![115, -98, 80, -144, 76]] 
 ![![47, 0, 0, 0, 0], ![40, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![45, 0, 0, 0, 1]] where
  M :=![![![115, -98, 80, -144, 76], ![-456, 407, -322, 552, -288], ![1728, -1550, 1281, -2142, 1104], ![-1784, 1586, -1338, 2245, -1156], ![3268, -2894, 2452, -4128, 2127]]]
  hmulB := by decide  
  f := ![![![-4779, -2554, -1380, -120, 476]], ![![-4128, -2213, -1202, -132, 400]], ![![-4545, -2464, -1363, -258, 396]], ![![-704, -442, -298, -287, -36]], ![![-4325, -2408, -1388, -504, 275]]]
  g := ![![![-39, -98, 80, -144, 76], ![134, 407, -322, 552, -288], ![-563, -1550, 1281, -2142, 1104], ![618, 1586, -1338, 2245, -1156], ![-1149, -2894, 2452, -4128, 2127]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-351, -49, 92, 537, 250]] ![![-5803, -2993, -1522, 291, 750]]
  ![![-4779, -2554, -1380, -120, 476]] where
 M := ![![![-4779, -2554, -1380, -120, 476]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-4779, -2554, -1380, -120, 476]] ![![115, -98, 80, -144, 76]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13149, 6611, 3202, -1361, -1976]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![13149, 6611, 3202, -1361, -1976]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![27, 39, 1, 0, 0], ![29, 27, 0, 1, 0], ![5, 11, 0, 0, 1]] where
  M :=![![![13149, 6611, 3202, -1361, -1976], ![11856, 5380, 2048, -3611, -2722], ![16332, 5253, -279, -13799, -7222], ![23840, 6459, -2166, -25126, -12514], ![23384, 3629, -6004, -35697, -16619]]]
  hmulB := by decide  
  f := ![![![31273, -31829, -15448, 4255, 5004]], ![![-30024, 57478, -12126, -12065, 8510]], ![![-7125, 26452, -15707, -6661, 8356]], ![![2217, 11196, -14566, -3686, 7008]], ![![-3087, 9622, -4964, -2341, 2711]]]
  g := ![![![-452, -1128, 3202, -1361, -1976], ![1413, 999, 2048, -3611, -2722], ![8682, 8833, -279, -13799, -7222], ![16482, 17113, -2166, -25126, -12514], ![24600, 26121, -6004, -35697, -16619]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [34, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 52], [0, 1]]
 g := ![![[50, 16], [25], [14, 28], [6], [49, 1]], ![[39, 37], [25], [8, 25], [6], [45, 52]]]
 h' := ![![[49, 52], [52, 49], [1, 48], [7, 9], [30, 35], [0, 1]], ![[0, 1], [15, 4], [21, 5], [24, 44], [49, 18], [49, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [23, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [34, 4, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1331, -1358, 1500, 2453, 2539]
  a := ![3, -3, 4, 2, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2371, -2906, 1500, 2453, 2539]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-40429, 35076, 26051, -3701, -9472]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-40429, 35076, 26051, -3701, -9472]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![5, 42, 1, 0, 0], ![20, 28, 0, 1, 0], ![50, 49, 0, 0, 1]] where
  M :=![![![-40429, 35076, 26051, -3701, -9472], ![56832, -91195, 5324, 17620, -7402], ![44412, 11682, -78899, -10820, 35240], ![-36732, 53446, 2062, -9759, 2066], ![18378, -89580, 61893, 23511, -32113]]]
  hmulB := by decide  
  f := ![![![-256157, -132104, -67133, 12973, 33170]], ![![-199020, -102487, -51998, 10594, 25946]], ![![-184817, -95184, -48292, 9813, 24090]], ![![-204836, -105534, -53568, 10735, 26650]], ![![-425828, -219439, -111405, 22167, 55355]]]
  g := ![![![7112, -9270, 26051, -3701, -9472], ![904, -8405, 5324, 17620, -7402], ![-20881, 35880, -78899, -10820, 35240], ![846, 2620, 2062, -9759, 2066], ![15931, -33469, 61893, 23511, -32113]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P1 : CertificateIrreducibleZModOfList' 53 2 2 5 [6, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 52], [0, 1]]
 g := ![![[2, 9], [43], [11, 25], [17], [41, 1]], ![[0, 44], [43], [29, 28], [17], [29, 52]]]
 h' := ![![[41, 52], [17, 50], [40, 19], [47, 5], [19, 32], [0, 1]], ![[0, 1], [0, 3], [24, 34], [40, 48], [6, 21], [41, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [37, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N1 : CertifiedPrimeIdeal' SI53N1 53 where
  n := 2
  hpos := by decide
  P := [6, 12, 1]
  hirr := P53P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1805, -14610, 14425, 885, 18475]
  a := ![1, -5, 12, -5, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19090, -29255, 14425, 885, 18475]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N1 B_one_repr
lemma NI53N1 : Nat.card (O ⧸ I53N1) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 7, 3, 0, -2]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![13, 7, 3, 0, -2]] 
 ![![53, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![13, 7, 3, 0, -2], ![12, 4, 4, -3, 0], ![0, 11, -3, 9, -6], ![16, -3, 8, -10, 4], ![-14, 13, -11, 18, -9]]]
  hmulB := by decide  
  f := ![![![21, -17, -15, 6, 8]], ![![9, -7, -7, 3, 4]], ![![3, -4, -2, 3, 2]], ![![16, -15, -12, 8, 8]], ![![4, -5, -5, 6, 5]]]
  g := ![![![-3, 7, 3, 0, -2], ![0, 4, 4, -3, 0], ![-10, 11, -3, 9, -6], ![7, -3, 8, -10, 4], ![-16, 13, -11, 18, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![13149, 6611, 3202, -1361, -1976]] ![![-40429, 35076, 26051, -3701, -9472]]
  ![![-21, 17, 15, -6, -8]] where
 M := ![![![-21, 17, 15, -6, -8]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![-21, 17, 15, -6, -8]] ![![13, 7, 3, 0, -2]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, -18, -24, -2, 10]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-29, -18, -24, -2, 10]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![16, 17, 53, 1, 0], ![18, 37, 20, 0, 1]] where
  M :=![![![-29, -18, -24, -2, 10], ![-60, 27, 4, -14, -4], ![24, -62, 9, -26, -28], ![44, -26, -28, -69, -28], ![20, 86, -22, -120, -43]]]
  hmulB := by decide  
  f := ![![![145, -130, 108, -182, 94]], ![![-564, 501, -420, 706, -364]], ![![2184, -1942, 1627, -2738, 1412]], ![![1800, -1601, 1341, -2257, 1164]], ![![502, -447, 374, -630, 325]]]
  g := ![![![-3, -6, -2, -2, 10], ![4, 7, 14, -14, -4], ![16, 24, 33, -26, -28], ![28, 37, 71, -69, -28], ![46, 63, 122, -120, -43]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [48, 16, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 17, 14], [41, 41, 45], [0, 1]]
 g := ![![[47, 30, 12], [44, 53, 20], [], [47, 57, 21], [1]], ![[2, 16, 33, 54], [31, 42, 37, 52], [12, 9], [53, 21, 54, 56], [36, 11, 9, 30]], ![[41, 54, 15, 25], [7, 17, 37, 3], [47, 9], [37, 9, 36, 41], [25, 53, 52, 29]]]
 h' := ![![[45, 17, 14], [12, 4, 37], [19, 53, 16], [45, 55], [11, 43, 27], [0, 1]], ![[41, 41, 45], [35, 11, 39], [8, 36, 41], [42, 50, 3], [12, 42, 57], [45, 17, 14]], ![[0, 1], [44, 44, 42], [46, 29, 2], [58, 13, 56], [48, 33, 34], [41, 41, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 9], []]
 b := ![[], [54, 53, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [48, 16, 32, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-446, 824, -1015, 1823, -911]
  a := ![4, 0, -1, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-224, 60, -1346, 1823, -911]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![145, -130, 108, -182, 94]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![145, -130, 108, -182, 94]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![45, 17, 1, 0, 0], ![55, 42, 0, 1, 0], ![8, 24, 0, 0, 1]] where
  M :=![![![145, -130, 108, -182, 94], ![-564, 501, -420, 706, -364], ![2184, -1942, 1627, -2738, 1412], ![-2284, 2030, -1700, 2861, -1476], ![4196, -3730, 3122, -5256, 2711]]]
  hmulB := by decide  
  f := ![![![-29, -18, -24, -2, 10]], ![![-60, 27, 4, -14, -4]], ![![-39, -7, -17, -6, 6]], ![![-69, 2, -20, -13, 6]], ![![-28, 10, -2, -8, -1]]]
  g := ![![![77, 58, 108, -182, 94], ![-298, -225, -420, 706, -364], ![1157, 873, 1627, -2738, 1412], ![-1209, -912, -1700, 2861, -1476], ![2222, 1676, 3122, -5256, 2711]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [33, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 58], [0, 1]]
 g := ![![[11, 5], [1, 20], [51], [47, 3], [50, 1]], ![[25, 54], [57, 39], [51], [20, 56], [41, 58]]]
 h' := ![![[50, 58], [26, 51], [22, 43], [42, 13], [2, 48], [0, 1]], ![[0, 1], [39, 8], [48, 16], [43, 46], [42, 11], [50, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [21, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [33, 9, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-38977, -12441, 15268, 63177, 34902]
  a := ![7, 21, 7, -50, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-75932, -63781, 15268, 63177, 34902]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-29, -18, -24, -2, 10]] ![![145, -130, 108, -182, 94]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [16, 45, 10, 34, 53, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 48, 34, 45, 54], [56, 34, 41, 8, 34], [4, 43, 42, 56, 46], [26, 57, 5, 13, 49], [0, 1]]
 g := ![![[43, 56, 22, 7, 34], [51, 36, 57, 34], [54, 52, 25, 4, 56], [30, 8, 1], []], ![[1, 42, 20, 22, 27, 20, 35, 33], [16, 22, 47, 47], [11, 54, 18, 11], [60, 30, 27, 19, 44, 34, 25, 32], [27, 49, 33, 41, 58, 40, 28, 23]], ![[18, 52, 28, 58, 3, 36, 40, 46], [28, 15, 14, 36], [2, 25, 53, 36, 58, 22, 60, 27], [44, 27, 33, 9, 60, 7, 17, 13], [8, 27, 1, 40, 52, 22, 27, 20]], ![[33, 19, 24, 15, 19, 41, 46, 60], [45, 55, 58, 45], [30, 45, 36, 50, 27, 51, 56, 22], [20, 9, 46, 52, 12, 58, 8, 27], [26, 32, 10, 21, 2, 52, 3, 41]], ![[44, 39, 13, 51, 47, 50, 39, 34], [27, 33, 43, 16], [6, 54, 15, 25, 56, 42, 52, 22], [29, 3, 13, 27, 49, 25, 11, 39], [46, 10, 36, 2, 5, 22, 27, 41]]]
 h' := ![![[44, 48, 34, 45, 54], [16, 28, 4, 60, 41], [51, 35, 34, 48, 20], [8, 47, 56, 14, 19], [0, 0, 0, 1], [0, 1]], ![[56, 34, 41, 8, 34], [30, 4, 36, 5, 59], [15, 44, 57, 15, 48], [51, 11, 46], [23, 28, 44, 29, 10], [44, 48, 34, 45, 54]], ![[4, 43, 42, 56, 46], [37, 37, 41, 60, 32], [34, 54, 54, 28, 6], [50, 23, 7, 6, 11], [52, 50, 40, 29, 19], [56, 34, 41, 8, 34]], ![[26, 57, 5, 13, 49], [48, 14, 4, 53, 22], [55, 16, 10, 34, 44], [37, 26, 37, 47, 24], [14, 16, 18, 24, 48], [4, 43, 42, 56, 46]], ![[0, 1], [47, 39, 37, 5, 29], [28, 34, 28, 58, 4], [13, 15, 37, 55, 7], [4, 28, 20, 39, 45], [26, 57, 5, 13, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 14, 2, 6], [], [], []]
 b := ![[], [27, 50, 31, 45, 27], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [16, 45, 10, 34, 53, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![145970890071, -13110669976, -4148221125, -215201888166, -58434584610]
  a := ![1, 6, 4, -15, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2392965411, -214929016, -68003625, -3527899806, -957944010]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 844596301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀



lemma PB1705I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB1705I1 : PrimesBelowBoundCertificateInterval O 23 61 1705 where
  m := 9
  g := ![2, 1, 4, 2, 2, 3, 3, 2, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB1705I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0]
    · exact ![I37N0, I37N1, I37N2, I37N3]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![707281, 29]
    · exact ![28629151]
    · exact ![1369, 37, 37, 37]
    · exact ![2825761, 41]
    · exact ![79507, 1849]
    · exact ![2209, 2209, 47]
    · exact ![2809, 2809, 53]
    · exact ![205379, 3481]
    · exact ![844596301]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
      exact NI37N3
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
  β := ![I29N1, I37N0, I37N1, I37N2, I37N3, I41N1, I47N2, I53N2]
  Il := ![[I29N1], [], [I37N0, I37N1, I37N2, I37N3], [I41N1], [], [I47N2], [I53N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
